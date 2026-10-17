#include "Rts.h"
#include "rts/OSThreads.h"

/* Executable-only hook, called before GHC parses compiled, environment and
 * command-line RTS options. Keep the N formula aligned with selectAutomaticJobs.
 * Clamp before multiplying so even an excessive detected count cannot overflow.
 */
void FlagDefaultsHook(void)
{
    uint32_t processors = getNumberOfProcessors();
    if (processors > 24) processors = 24;
    uint32_t capabilities = 2 * processors / 3;
    RtsFlags.ParFlags.nCapabilities = capabilities > 0 ? capabilities : 1;
}
