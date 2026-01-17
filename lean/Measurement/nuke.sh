#!/usr/bin/env bash

set -euo pipefail

echo "💣 Nuking VS Code caches and Lean artifacts..."

# --- VS Code user-level caches ---
rm -rf "$HOME/Library/Application Support/Code/User/workspaceStorage"
rm -rf "$HOME/Library/Application Support/Code/CachedData"
rm -rf "$HOME/Library/Application Support/Code/Service Worker"
rm -rf "$HOME/Library/Application Support/Code/logs"
rm -rf "$HOME/Library/Application Support/Code/GPUCache"

# --- VS Code extension caches (Lean lives here) ---
rm -rf "$HOME/.vscode/extensions/*/out"
rm -rf "$HOME/.vscode/extensions/*/.cache"

# --- Optional but recommended: crash resurrection junk ---
rm -rf "$HOME/Library/Saved Application State/com.microsoft.VSCode.savedState"

# --- Kill running VS Code + language servers ---
pkill -f "Visual Studio Code" || true
pkill -f "lean" || true
pkill -f "node" || true

# --- Project-local Lean/Lake artifacts (run from project root safely) ---
if [ -f "lakefile.lean" ]; then
  echo "📁 Lean project detected, nuking .lake and build/"
  rm -rf .lake build
fi

echo "✅ Done. VS Code has been ritually purified."

