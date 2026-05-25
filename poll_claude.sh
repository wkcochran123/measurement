#!/usr/bin/env bash
#
# poll_claude.sh — Watcher for the Claude/Codex handoff protocol.
#
# Watches notes_for_claude.md (Claude's inbox) for new HANDOFF messages.
# When a new message addressed `to: claude` arrives with a turn number
# higher than the last one processed, the script prints a Claude-ready
# prompt block. You forward that block to Claude (paste in a Claude Code
# session, pipe to `claude`, etc.). Claude responds by writing
# notes_for_codex.md. The script keeps watching.
#
# Protocol expectation (see notes_for_claude.md): each handoff file begins
# with a header of the form
#
#   <!-- HANDOFF
#   from: codex
#   to: claude
#   turn: 7
#   status: NEEDS_RESPONSE
#   respond_to_sha: <hash>
#   stop_token: HANDOFF_CONVERGED
#   -->
#
# The script enforces:
#
#   * to == claude            (otherwise ignore)
#   * from != claude          (self-reference guard)
#   * turn > last processed   (no replays on restart)
#
# Stop conditions:
#
#   * HANDOFF_CONVERGED  in both inboxes against the same respond_to_sha
#   * HANDOFF_HUMAN_NEEDED in either inbox
#   * SIGINT / SIGTERM
#
# State persistence: .handoff_claude_state holds the last turn this watcher
# emitted, so restarts do not re-emit old messages.
#
# Usage:
#   ./poll_claude.sh
#   ./poll_claude.sh --interval 5
#   ./poll_claude.sh --inbox notes_for_claude.md --outbox notes_for_codex.md
#

set -euo pipefail

INBOX="notes_for_claude.md"
OUTBOX="notes_for_codex.md"
STATE_FILE=".handoff_claude_state"
INTERVAL=2
ONCE=0

usage() {
  sed -n '1,/^$/{ /^#!\|^$/d; s/^# \?//; p; }' "$0"
  cat <<EOF

Options:
  --interval N      Polling interval in seconds (default: 2)
  --inbox PATH      Claude's inbox (default: notes_for_claude.md)
  --outbox PATH     Codex's inbox (default: notes_for_codex.md)
  --state PATH      State file (default: .handoff_claude_state)
  -h, --help        Show this help
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --interval) INTERVAL="$2"; shift 2 ;;
    --inbox)    INBOX="$2";    shift 2 ;;
    --outbox)   OUTBOX="$2";   shift 2 ;;
    --state)    STATE_FILE="$2"; shift 2 ;;
    --once)     ONCE=1; shift ;;
    -h|--help)  usage; exit 0 ;;
    *) echo "Unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

if [[ ! -f "$STATE_FILE" ]]; then
  echo "last_turn=0" > "$STATE_FILE"
fi

get_last_turn() {
  if [[ -f "$STATE_FILE" ]]; then
    grep '^last_turn=' "$STATE_FILE" 2>/dev/null | head -1 | cut -d= -f2
  else
    echo "0"
  fi
}

set_last_turn() {
  echo "last_turn=$1" > "$STATE_FILE"
}

# Extract a single field value from the first <!-- HANDOFF ... --> block
# in the given file. Returns empty string if not present.
extract_header_field() {
  local file="$1"
  local field="$2"
  [[ -f "$file" ]] || { echo ""; return; }
  awk -v field="$field" '
    /<!-- HANDOFF/ { in_block=1; next }
    in_block && /-->/ { in_block=0; exit }
    in_block {
      sub(/^[ \t]+/, "")
      if ($1 == field":") {
        sub("^"field":[ \t]*", "")
        print
        exit
      }
    }
  ' "$file"
}

mtime_of() {
  [[ -f "$1" ]] || { echo "0"; return; }
  if [[ "$(uname)" == "Darwin" ]]; then
    stat -f %m "$1" 2>/dev/null || echo "0"
  else
    stat -c %Y "$1" 2>/dev/null || echo "0"
  fi
}

check_human_stop() {
  # A directive only counts if it appears as a literal HTML comment OUTSIDE
  # of any fenced code block. This avoids false-positive triggers on
  # protocol documentation that quotes the directive inside a fence.
  for f in "$INBOX" "$OUTBOX"; do
    [[ -f "$f" ]] || continue
    if awk '
      /^```/ { in_fence = !in_fence; next }
      !in_fence && /^[[:space:]]*<!--[[:space:]]*HANDOFF_HUMAN_NEEDED[[:space:]]*-->[[:space:]]*$/ {
        print "match"; exit 0
      }
    ' "$f" | grep -q '^match$'; then
      echo "" >&2
      echo "[poll_claude] HANDOFF_HUMAN_NEEDED in $f — stopping." >&2
      exit 0
    fi
  done
}

check_convergence() {
  [[ -f "$INBOX" && -f "$OUTBOX" ]] || return 1
  local inbox_status outbox_status inbox_sha outbox_sha
  inbox_status=$(extract_header_field "$INBOX" "status")
  outbox_status=$(extract_header_field "$OUTBOX" "status")
  inbox_sha=$(extract_header_field "$INBOX" "respond_to_sha")
  outbox_sha=$(extract_header_field "$OUTBOX" "respond_to_sha")
  [[ "$inbox_status" == "CONVERGED" && "$outbox_status" == "CONVERGED" && \
     -n "$inbox_sha" && "$inbox_sha" == "$outbox_sha" ]]
}

trap 'echo "" >&2; echo "[poll_claude] stopped." >&2; exit 0' INT TERM

echo "[poll_claude] watching $INBOX  (interval ${INTERVAL}s, state $STATE_FILE)" >&2
echo "[poll_claude] press Ctrl-C to stop" >&2

last_mtime="0"

while true; do
  check_human_stop

  if check_convergence; then
    echo "" >&2
    echo "[poll_claude] CONVERGED — both inboxes agree on respond_to_sha. stopping." >&2
    exit 0
  fi

  if [[ ! -f "$INBOX" ]]; then
    sleep "$INTERVAL"
    continue
  fi

  current_mtime=$(mtime_of "$INBOX")
  if [[ "$current_mtime" == "$last_mtime" ]]; then
    sleep "$INTERVAL"
    continue
  fi
  last_mtime="$current_mtime"

  to=$(extract_header_field "$INBOX" "to")
  from=$(extract_header_field "$INBOX" "from")
  turn=$(extract_header_field "$INBOX" "turn")
  status=$(extract_header_field "$INBOX" "status")
  sha=$(extract_header_field "$INBOX" "respond_to_sha")

  if [[ -z "$to" || -z "$from" || -z "$turn" ]]; then
    # No header yet, or malformed — wait for a complete header
    continue
  fi

  if [[ "$to" != "claude" ]]; then
    echo "[poll_claude] $INBOX: addressed to '$to' — ignoring" >&2
    continue
  fi

  if [[ "$from" == "claude" ]]; then
    echo "[poll_claude] $INBOX: from claude — ignoring (self-reference guard)" >&2
    continue
  fi

  last_turn=$(get_last_turn)
  if ! [[ "$turn" =~ ^[0-9]+$ ]]; then
    echo "[poll_claude] $INBOX: turn '$turn' is not a non-negative integer — skipping" >&2
    continue
  fi
  if (( turn <= last_turn )); then
    # Already processed; quietly skip
    continue
  fi

  # New, valid, addressed-to-claude handoff. Emit a Claude-ready block.
  cat <<EOF

================================================================================
NEW HANDOFF FOR CLAUDE
  turn:           $turn   (last processed: $last_turn)
  from:           $from
  status:         $status
  respond_to_sha: $sha
================================================================================

$(cat "$INBOX")

================================================================================
END HANDOFF.

Forward the above to Claude. After Claude writes notes_for_codex.md with
turn $((turn + 1)) (or higher), this watcher resumes.
================================================================================

EOF

  set_last_turn "$turn"

  if [[ "$ONCE" == "1" ]]; then
    exit 0
  fi
done
