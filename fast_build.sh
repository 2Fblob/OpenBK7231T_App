#!/bin/bash
# Fast incremental build for ONE OpenBeken target.
#
# Why this is fast:
#   - builds only your chip (not all 7 platforms)
#   - NO 'make clean' -> the Beken SDK build is make-based, so only files you
#     actually changed get recompiled. First build is a full (cold) compile;
#     every build after that is seconds.
#   - parallel compile across all cores via MAKEFLAGS=-j
#
# Usage:   ./fast_build.sh [PLATFORM]
#   PLATFORM defaults to OpenBK7231N. Examples: OpenBK7231T, OpenBK7231N
#
# Run it natively (toolchain installed) OR inside the build container, e.g.:
#   docker run -it -v "$(pwd)":/OpenBK7231T_App openbk_build /OpenBK7231T_App/fast_build.sh OpenBK7231N
#
# IMPORTANT: only run a real 'make clean' when you switch chips or git branches,
# or after changing SDK-level config. Day-to-day app edits never need it.

set -e

SDK="${1:-OpenBK7231N}"                       # <-- your chip
APP_VER="${APP_VERSION:-dev_$(date +%Y%m%d_%H%M%S)}"
: "${MAKEFLAGS:=-j$(nproc)}"                   # use all cores unless caller set it
export MAKEFLAGS

# Walk up to the repo root (the dir that has the Makefile), from wherever this lives.
DIR="$(cd "$(dirname "$0")" && pwd)"
while [ ! -f "$DIR/Makefile" ] && [ "$DIR" != "/" ]; do DIR="$(dirname "$DIR")"; done
cd "$DIR"

# Avoid git "dubious ownership" noise when run in a container.
git config --global --add safe.directory "$DIR" 2>/dev/null || true

echo "=================================================================="
echo " Building $SDK   version=$APP_VER   MAKEFLAGS=$MAKEFLAGS"
echo " (incremental: no clean - only changed files recompile)"
echo "=================================================================="

time make APP_VERSION="$APP_VER" APP_NAME="$SDK" "$SDK"

echo
echo "Done. Firmware in: output/$APP_VER/"
ls -la "output/$APP_VER/" 2>/dev/null || true
