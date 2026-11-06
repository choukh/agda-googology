#!/bin/sh
# NegValX: 冷编本路的模块 (只删本路自己的 .agdai, 字面路径), 再从入口编译, 退出码不经管道.
# 用法 (从仓库根): sh probes/Survey/scripts/negvalx/verify.sh <库文件> <日志>
LIB="$1"
LOG="$2"
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/NegValX.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/NegValXSelf.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/NegValXIfSelf.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/NegValXUip.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/NegValXSh.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/NegValXCopy.agdai
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/NegValXInst.agdai
agda --library-file="$LIB" -i src -i probes probes/OCF/Lean/NegValX.lagda.md +RTS -M6G -RTS > "$LOG" 2>&1
echo "EXIT $?"
# 禁用构造 (只看 agda 代码块里的写法; 讲解里的词不算)
grep -nE 'postulate|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|trustMe|--with-K|\{!|\?\s*$' probes/OCF/Lean/NegValX*.lagda.md || echo "no forbidden constructs"
