#!/bin/bash
DEST="${1:-./collected_p}"
mkdir -p "$DEST"
SEEN=""
echo "[*] Monitoring ~/.isabelle/prob_*.p ... (Ctrl-C to stop)"
while true; do
    for src in ~/.isabelle/prob_*.p; do
        [ -f "$src" ] || continue
        HASH=$(md5 -q "$src" 2>/dev/null || md5sum "$src" | cut -d" " -f1)
        KEY="${HASH}_$(basename $src)"
        if ! echo "$SEEN" | grep -q "$KEY"; then
            cp "$src" "$DEST/$KEY"
            echo "  Captured: $KEY"
            SEEN="$SEEN $KEY"
        fi
    done
    sleep 0.3
done
