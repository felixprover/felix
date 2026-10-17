#include <signal.h>
#include <stdio.h>
#include <stdlib.h>

static volatile sig_atomic_t received;

static void receive_interrupt(int signal_number)
{
    (void)signal_number;
    received = 1;
}

/* Use a native executable: another language runtime may repair its inherited
 * signal mask during startup and conceal the launcher's bug. */
int main(void)
{
    sigset_t mask;
    struct sigaction action = {0};
    if (sigprocmask(SIG_SETMASK, NULL, &mask) != 0)
        return EXIT_FAILURE;
    if (sigismember(&mask, SIGINT)) {
        fputs("prover inherited blocked SIGINT\n", stderr);
        return EXIT_FAILURE;
    }
    action.sa_handler = receive_interrupt;
    sigemptyset(&action.sa_mask);
    if (sigaction(SIGINT, &action, NULL) != 0 || raise(SIGINT) != 0 || !received)
        return EXIT_FAILURE;
    while (getchar() != EOF) {}
    if (ferror(stdin))
        return EXIT_FAILURE;
    puts("% SZS status Theorem for signal probe");
    return EXIT_SUCCESS;
}
