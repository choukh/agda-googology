#!/bin/sh
# 重新生成 LadderLabZ*, LadderLabRel, LadderLabClass, LadderLabPsi, LadderLabEval, LadderLabNFOmega, LadderLabForget.
# 用法: sh mkall.sh [输出目录]. 默认写回 probes/OCF/Align/. 逐字节可重复.
d=$(dirname "$0")
python3 "$d/mkworld.py" "$@"
python3 "$d/mk_class.py" "$@"
