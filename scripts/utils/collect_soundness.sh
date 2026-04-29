#!/bin/bash
OUT=~/fyp-isabelle-fuzz/soundness_p_files
mkdir -p "$OUT"

for thy in ~/fyp-isabelle-fuzz/soundness_session/FuzzTest*.thy; do
    name=$(basename "$thy" .thy)
    echo "=== Building $name ==="
    
    # 清理旧 .p 文件
    rm -f ~/.isabelle/Isabelle2025/prob_zipperposition*.p
    
    # 单独 build 一个 theory（用临时 ROOT）
    TMP_DIR=$(mktemp -d)
    cp "$thy" "$TMP_DIR/"
    cat > "$TMP_DIR/ROOT" << EOF
session SingleTest = HOL +
  theories
    $name
EOF
    
    isabelle build -d "$TMP_DIR" SingleTest 2>/dev/null
    
    # 收集 .p 文件
    for p in ~/.isabelle/Isabelle2025/prob_zipperposition*.p; do
        [ -f "$p" ] && cp "$p" "$OUT/${name}_$(basename "$p")"
    done
    
    rm -rf "$TMP_DIR"
    echo "  collected .p files for $name"
done

echo "[*] All .p files in $OUT"
ls "$OUT" | wc -l