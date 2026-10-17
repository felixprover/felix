#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <spawn.h>

#if defined(__APPLE__)
#include <crt_externs.h>
#define FELIX_NATIVE_SPAWN 1
#elif defined(__GLIBC__)
#if __GLIBC_PREREQ(2, 34)
#define FELIX_NATIVE_SPAWN 1
#endif
#endif

/* process-1.6.26.1 implements close_fds with fork and a loop up to
 * _SC_OPEN_MAX. Use CLOEXEC_DEFAULT on macOS and addclosefrom_np on Linux/glibc
 * to close unrelated descriptors, including those opened concurrently.
 * The pipe owner supplies distinct descriptors above stderr; dup2 actions are
 * the only inheritance exceptions. Inherit the environment, cwd and signal
 * dispositions (delegate_ctlc=False), and create a new process group. */
int felix_spawn_vampire(char *const argv[], int input, int output, int error,
                       pid_t *pid)
{
#ifndef FELIX_NATIVE_SPAWN
    /* Older glibc and other Linux libcs retain System.Process's safe fallback. */
    (void)argv; (void)input; (void)output; (void)error; (void)pid;
    return ENOSYS;
#else
    posix_spawn_file_actions_t actions;
    posix_spawnattr_t attributes;
    int status = posix_spawn_file_actions_init(&actions);
    if (status != 0)
        return status;
    status = posix_spawnattr_init(&attributes);
    if (status != 0) {
        posix_spawn_file_actions_destroy(&actions);
        return status;
    }

    /* The launching RTS thread can transiently block SIGINT. Do not export
     * thread-specific signal masks to the prover: Vampire uses SIGINT to stop
     * losing portfolio workers before publishing the winning proof. */
    sigset_t child_mask;
    sigemptyset(&child_mask);
    short flags = POSIX_SPAWN_SETPGROUP | POSIX_SPAWN_SETSIGMASK;
#if defined(__APPLE__)
    flags |= POSIX_SPAWN_CLOEXEC_DEFAULT;
    char **environment = *_NSGetEnviron();
#else
    extern char **environ;
    char **environment = environ;
#endif
    status = posix_spawnattr_setflags(&attributes, flags);
    if (status == 0)
        status = posix_spawnattr_setsigmask(&attributes, &child_mask);
    if (status == 0)
        status = posix_spawnattr_setpgroup(&attributes, 0);
    if (status == 0)
        status = posix_spawn_file_actions_adddup2(&actions, input, 0);
    if (status == 0)
        status = posix_spawn_file_actions_adddup2(&actions, output, 1);
    if (status == 0)
        status = posix_spawn_file_actions_adddup2(&actions, error, 2);
#if !defined(__APPLE__)
    /* Run after dup2: close all originals and unrelated descriptors, even
     * descriptors above a subsequently lowered RLIMIT_NOFILE. */
    if (status == 0)
        status = posix_spawn_file_actions_addclosefrom_np(&actions, 3);
#endif
    if (status == 0)
        status = posix_spawnp(pid, argv[0], &actions, &attributes, argv,
                             environment);

    posix_spawnattr_destroy(&attributes);
    posix_spawn_file_actions_destroy(&actions);
    return status;
#endif
}
