#!/bin/bash
# Builds Storage.vpk (run inside WSL). Usage: ./build.sh
set -e
export VITASDK=${VITASDK:-$HOME/vitasdk}
export PATH=$VITASDK/bin:$PATH
cd "$(dirname "$0")"
if [ ! -f sce_sys/icon0.png ] || [ ! -f assets/logo.png ]; then python3 tools/make_livearea.py; fi
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release > /dev/null
cmake --build build -j8
ls -l build/VitaStorageManager.vpk
