#!/bin/sh
# 冷编 SameV* (只删这些模块自己的接口, 字面路径). 用法: verify.sh <库文件>, 从仓库根运行.
LIB="$1"
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/SameVRel.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/SameVMono.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/SameVX.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/SameVLeg.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/SameVGoal.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/SameVObs.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/SameV.agdai
agda --library-file="$LIB" -i src -i probes probes/OCF/Lean/SameV.lagda.md +RTS -M6G -RTS
echo "SameV exit=$?"
