#!/bin/sh
# ValX 冷编: 删本路自己的 .agdai (字面路径), 从仓库根编译入口 (入口导入全部 ValX* 模块), 再查禁用构造.
# 用法 (从仓库根): sh probes/Survey/scripts/valx/verify.sh <库文件>
LIB="$1"
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/ValX.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/ValXIf.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/ValXRel.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/ValXObs.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/ValXBase.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/ValXMono.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/ValXTm.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/ValXGoal.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/ValXP1.agdai
agda --library-file="$LIB" -i src -i probes probes/OCF/Lean/ValX.lagda.md +RTS -M6G -RTS
echo "EXIT $?"
echo "禁用构造 (应为空):"
grep -n -E "postulate|\{-# *(TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK)|trustMe|--with-K|\{!|\?\s*$" probes/OCF/Lean/ValX*.lagda.md
echo "OPTIONS 行:"
grep -h "OPTIONS" probes/OCF/Lean/ValX*.lagda.md | sort | uniq -c
