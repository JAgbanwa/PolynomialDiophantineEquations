#!/bin/bash
# Graceful stop: workers finish their current chunk (a few minutes at most) and exit. Restart any time with: bash run.sh
cd "$(dirname "$0")" || exit 1
touch STOP
echo "Stop requested; workers will exit after their current chunk."
