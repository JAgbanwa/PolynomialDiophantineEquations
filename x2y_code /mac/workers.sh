#!/bin/bash
cd "$(dirname "$0")" || exit 1
NW=${1:-8}
for w in $(seq 1 "$NW"); do bash worker.sh "$w" x2y_search_worker & done
wait
