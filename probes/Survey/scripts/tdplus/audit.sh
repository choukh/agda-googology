#!/bin/bash
# TdPlus 一路的审计: 导入闭包 (编译器级) 与禁用构造. 从仓库根目录运行:
#   bash probes/Survey/scripts/tdplus/audit.sh
# --only 表同 DiagK, 加 TdPlus 与 View 一族 (MainView, BrwView, BrwWf).
cd "$(dirname "$0")/../../../.." || exit 2
ONLY=(--only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRuleSpec
      --only OCF.Align.TLRuleSum --only OCF.Align.SumOne --only OCF.Align.HtGen --only OCF.Align.HtFeed
      --only OCF.Align.HtOut --only OCF.Align.HtCross --only OCF.Align.SumVar --only OCF.Align.HtTower
      --only OCF.Align.LFRe --only OCF.Align.DiagK --only OCF.Align.TdPlus
      --only OCF.Align.MainView --only OCF.Align.BrwView --only OCF.Align.BrwWf)
rc=0
for m in TdPlusUni TdPlusFold TdPlusVal TdPlusGrow TdPlusView TdPlus; do
  python3 probes/Survey/scripts/importclosure.py "${ONLY[@]}" OCF.Align.$m | grep -E '^==|命中|^   OK|FAIL'
  r=${PIPESTATUS[0]}; echo "  importclosure $m exit=$r"; [ $r -ne 0 ] && rc=1
done
echo "== 禁用构造 (postulate, 洞, 编译指示, trustMe, Funext, 选项)"
grep -nE 'postulate|TERMINATING|NON_TERMINATING|NO_POSITIVITY|trustMe|Funext|\{!|^\s*\?\s*$| \?$' probes/OCF/Align/TdPlus*.lagda.md && rc=1 || echo "  0 命中"
grep -L -- '--safe --without-K --lossy-unification' probes/OCF/Align/TdPlus*.lagda.md | sed 's/^/  缺选项: /'
exit $rc
