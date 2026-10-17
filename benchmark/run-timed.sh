#!/bin/sh
set -eu

usage() {
    printf '%s\n' \
        'usage: run-timed.sh elapsed-log OUTPUT LABEL -- COMMAND [ARG ...]' \
        '       run-timed.sh resources OUTPUT -- COMMAND [ARG ...]' >&2
    exit 2
}

if [ "$#" -lt 4 ]; then
    usage
fi

mode=$1
output=$2
shift 2

timer=${FELIX_TIME_COMMAND:-/usr/bin/time}
case "$timer" in
    */*)
        if [ ! -x "$timer" ]; then
            printf 'time command is not executable: %s\n' "$timer" >&2
            exit 2
        fi
        ;;
    *)
        resolved_timer=$(command -v "$timer") || {
            printf 'time command was not found: %s\n' "$timer" >&2
            exit 2
        }
        timer=$resolved_timer
        ;;
esac

case "$mode" in
    elapsed-log)
        label=$1
        shift
        if [ "$1" != -- ] || [ "$#" -lt 2 ]; then
            usage
        fi
        shift

        temporary=$(mktemp "${TMPDIR:-/tmp}/felix-time.XXXXXX")
        trap 'rm -f "$temporary"' EXIT HUP INT TERM

        "$timer" -p -o "$temporary" "$@"
        elapsed=$(awk '$1 == "real" { print $2; found = 1; exit }
            END { if (!found) exit 1 }' "$temporary") || {
            printf 'time command produced no elapsed-time record\n' >&2
            exit 2
        }
        printf '%s %s seconds\n' "$label" "$elapsed" >> "$output"
        ;;
    resources)
        if [ "$1" != -- ] || [ "$#" -lt 2 ]; then
            usage
        fi
        shift

        style=${FELIX_TIME_STYLE:-auto}
        if [ "$style" = auto ]; then
            # Detailed resource flags differ between GNU and BSD time.  Probe
            # the actual executable, then retain POSIX timing as a safe floor.
            version=$({ "$timer" --version 2>&1 || :; })
            case "$version" in
                *GNU*) style=gnu ;;
                *)
                    if "$timer" -l -o /dev/null true 2>/dev/null; then
                        style=bsd
                    else
                        style=portable
                    fi
                    ;;
            esac
        fi

        case "$style" in
            gnu)
                exec "$timer" -q -v -o "$output" "$@"
                ;;
            bsd)
                exec "$timer" -l -o "$output" "$@"
                ;;
            portable)
                exec "$timer" -p -o "$output" "$@"
                ;;
            *)
                printf 'unsupported FELIX_TIME_STYLE: %s\n' "$style" >&2
                exit 2
                ;;
        esac
        ;;
    *)
        usage
        ;;
esac
