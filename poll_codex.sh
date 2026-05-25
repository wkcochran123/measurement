#!/usr/bin/env bash
#
# poll_codex.sh — Watcher for the Claude/Codex handoff protocol.
#
# Watches notes_for_codex.md (Codex's inbox) for new HANDOFF messages.
# When a new message addressed `to: codex` arrives with a turn number higher
# than the last one processed, the script prints the handoff and keeps waiting.
#
# State persistence: .handoff_codex_state holds the last turn this watcher
# emitted, so restarts do not re-emit old messages.
#
# Usage:
#   ./poll_codex.sh
#   ./poll_codex.sh --interval 5
#   ./poll_codex.sh --inbox notes_for_codex.md --outbox notes_for_claude.md

set -euo pipefail

AGENT="codex"
INBOX="notes_for_codex.md"
OUTBOX="notes_for_claude.md"
STATE_FILE=".handoff_codex_state"
INTERVAL=2

usage() {
  sed -n '1,/^$/{ /^#!\|^$/d; s/^# \?//; p; }' "$0"
  cat <<EOF

Options:
  --interval N      Polling interval in seconds (default: 2)
  --inbox PATH      Codex's inbox (default: notes_for_codex.md)
  --outbox PATH     Claude's inbox (default: notes_for_claude.md)
  --state PATH      State file (default: .handoff_codex_state)
  -h, --help        Show this help
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --interval) INTERVAL="$2"; shift 2 ;;
    --inbox)    INBOX="$2";    shift 2 ;;
    --outbox)   OUTBOX="$2";   shift 2 ;;
    --state)    STATE_FILE="$2"; shift 2 ;;
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
  for f in "$INBOX" "$OUTBOX"; do
    if [[ -f "$f" ]] && grep -q 'HANDOFF_HUMAN_NEEDED' "$f"; then
      echo "" >&2
      echo "[poll_codex] HANDOFF_HUMAN_NEEDED in $f — stopping." >&2
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

trap 'echo "" >&2; echo "[poll_codex] stopped." >&2; exit 0' INT TERM

echo "[poll_codex] watching $INBOX  (interval ${INTERVAL}s, state $STATE_FILE)" >&2
echo "[poll_codex] press Ctrl-C to stop" >&2

last_mtime="0"

while true; do
  check_human_stop

  if check_convergence; then
    echo "" >&2
    echo "[poll_codex] CONVERGED — both inboxes agree on respond_to_sha. stopping." >&2
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
    continue
  fi

  if [[ "$to" != "$AGENT" ]]; then
    echo "[poll_codex] $INBOX: addressed to '$to' — ignoring" >&2
    continue
  fi

  if [[ "$from" == "$AGENT" ]]; then
    echo "[poll_codex] $INBOX: from $AGENT — ignoring (self-reference guard)" >&2
    continue
  fi

  last_turn=$(get_last_turn)
  if ! [[ "$turn" =~ ^[0-9]+$ ]]; then
    echo "[poll_codex] $INBOX: turn '$turn' is not a non-negative integer — skipping" >&2
    continue
  fi
  if (( turn <= last_turn )); then
    continue
  fi

  cat <<EOF

================================================================================
NEW HANDOFF FOR CODEX
  turn:           $turn   (last processed: $last_turn)
  from:           $from
  status:         $status
  respond_to_sha: $sha
================================================================================

$(cat "$INBOX")

================================================================================
END HANDOFF.

Codex should respond by writing notes_for_claude.md with turn $((turn + 1))
or higher, unless the handoff requests human input or declares convergence.
================================================================================

EOF

  set_last_turn "$turn"
done
