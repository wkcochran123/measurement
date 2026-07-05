#!/usr/bin/env bash
#
# ryot-reset.sh — Reset a RYOT process to an empty slate.
#
# When a RYOT job's context saturates (the inboxes grow huge, the goals pile up,
# the tanges/funges accumulate), this wipes the process back to zero so the two
# agents can start completely over.
#
# What it clears (the "goals, tanges, and funges"):
#   - INBOXES   notes_for_*.md          the handoff history (every turn, every
#                                        tange/select and funge/pool ever passed) -> emptied
#   - LEDGERS   .handoff_*_state         the handled-turn counters               -> last_turn=0
#   - GOALS     ryot/tasks/*.md          the task checkpoints (accepted decisions,
#                                        open questions, next actions)            -> archived away
#
# It is REVERSIBLE by default: everything is snapshotted into
#   ryot/archive/reset-<UTC-timestamp>/
# before anything is cleared. Nothing is destroyed unless you pass --no-backup.
#
# It does NOT touch: RYOT.md, the book/source artifacts, git, or your Claude
# memory. It only resets the RYOT *process* files.
#
# Prompt automations (self-scheduled wakes / cron) live in each agent's runtime,
# not on disk, so this script cannot cancel them. Pause/cancel them yourself
# after a reset, or the agents will wake into an empty inbox and idle.
#
# Usage:
#   ryot/reset.sh                 # backup + reset the RYOT process in the cwd (asks to confirm)
#   ryot/reset.sh --dir <path>    # target a different project root
#   ryot/reset.sh --dry-run       # show exactly what would change, touch nothing
#   ryot/reset.sh --yes           # skip the confirmation prompt
#   ryot/reset.sh --keep-tasks    # leave ryot/tasks/*.md in place (clear only inboxes+ledgers)
#   ryot/reset.sh --no-backup     # HARD reset: delete instead of archive (not reversible)
#
set -euo pipefail

DIR="$(pwd)"
BACKUP=1
ASSUME_YES=0
DRY=0
CLEAR_TASKS=1

usage() { sed -n '2,40p' "$0" | sed 's/^# \{0,1\}//'; }

while [[ $# -gt 0 ]]; do
  case "$1" in
    --dir)        DIR="${2:?--dir needs a path}"; shift 2;;
    --no-backup)  BACKUP=0; shift;;
    --keep-tasks) CLEAR_TASKS=0; shift;;
    --yes|-y)     ASSUME_YES=1; shift;;
    --dry-run|-n) DRY=1; shift;;
    -h|--help)    usage; exit 0;;
    *) echo "ryot-reset: unknown argument: $1" >&2; echo "try --help" >&2; exit 2;;
  esac
done

cd "$DIR"

# --- discover the RYOT process files (generic: any agent names) ---------------
shopt -s nullglob
inboxes=( notes_for_*.md )
states=( .handoff_*_state )
tasks=()
[[ $CLEAR_TASKS -eq 1 ]] && tasks=( ryot/tasks/*.md )

if [[ ${#inboxes[@]} -eq 0 && ${#states[@]} -eq 0 && ${#tasks[@]} -eq 0 ]]; then
  echo "ryot-reset: no RYOT process files found in $DIR (looked for notes_for_*.md, .handoff_*_state, ryot/tasks/*.md)." >&2
  exit 1
fi

ts="$(date -u +%Y%m%dT%H%M%SZ)"
archive="ryot/archive/reset-${ts}"

# --- show the plan ------------------------------------------------------------
echo "RYOT RESET  (project: $DIR)"
echo "  timestamp : $ts"
echo "  backup    : $([[ $BACKUP -eq 1 ]] && echo "yes -> $archive" || echo "NO (--no-backup: files will be destroyed)")"
echo
echo "  inboxes to empty (-> header stub, history archived):"
for f in "${inboxes[@]}"; do printf '    %s  (%s)\n' "$f" "$(wc -c <"$f" | tr -d ' ') bytes"; done
[[ ${#inboxes[@]} -eq 0 ]] && echo "    (none)"
echo "  ledgers to zero (-> last_turn=0):"
for f in "${states[@]}"; do printf '    %s  (%s)\n' "$f" "$(tr -d '\n' <"$f")"; done
[[ ${#states[@]} -eq 0 ]] && echo "    (none)"
echo "  goals/checkpoints to clear:"
for f in "${tasks[@]}"; do printf '    %s\n' "$f"; done
[[ ${#tasks[@]} -eq 0 ]] && echo "    (none$([[ $CLEAR_TASKS -eq 0 ]] && echo ' — --keep-tasks'))"
echo

if [[ $DRY -eq 1 ]]; then
  echo "--dry-run: nothing changed."
  exit 0
fi

if [[ $ASSUME_YES -ne 1 ]]; then
  printf 'Proceed with the reset? [y/N] '
  read -r reply
  [[ "$reply" == "y" || "$reply" == "Y" ]] || { echo "aborted."; exit 1; }
fi

# --- 1. snapshot (reversible) -------------------------------------------------
if [[ $BACKUP -eq 1 ]]; then
  mkdir -p "$archive"
  for f in "${inboxes[@]}" "${states[@]}" "${tasks[@]}"; do
    [[ -e "$f" ]] || continue
    dest="$archive/$f"; mkdir -p "$(dirname "$dest")"; cp -p "$f" "$dest"
  done
  echo "reset $ts: archived $(( ${#inboxes[@]} + ${#states[@]} + ${#tasks[@]} )) file(s)" \
    >> ryot/archive/reset-log.txt
fi

# --- 2. empty the inboxes (leave a breadcrumb, not a zero-byte file) ----------
for f in "${inboxes[@]}"; do
  if [[ $BACKUP -eq 1 ]]; then
    printf '<!-- RYOT inbox reset %s — prior history archived at %s/%s -->\n' "$ts" "$archive" "$f" > "$f"
  else
    printf '<!-- RYOT inbox reset %s -->\n' "$ts" > "$f"
  fi
done

# --- 3. zero the ledgers ------------------------------------------------------
for f in "${states[@]}"; do
  printf 'last_turn=0\n' > "$f"
done

# --- 4. clear the goals (already snapshotted above; remove the live copies) ----
for f in "${tasks[@]}"; do
  [[ -e "$f" ]] && rm -f "$f"
done

echo
echo "RYOT process reset to empty."
[[ $BACKUP -eq 1 ]] && echo "  history preserved at: $archive"
echo "  next: cancel/pause the agents' wake automations, then seed turn 1 with a fresh"
echo "        HANDOFF (respond_to_sha: RYOT_START_<task>) to begin the new job."
