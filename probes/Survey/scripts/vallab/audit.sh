#!/bin/zsh
# 用法 (仓库根目录): audit.sh <library-file> <html 目录>
L=$1; H=$2
agda --library-file=$L -i src -i probes --html --html-highlight=all --html-dir=$H probes/OCF/Align/ValLab.lagda.md +RTS -M15G -RTS || exit 1
python3 probes/Survey/scripts/depslice.py $H OCF.Align.LadderOrdMain:GᴺTᵠ OCF.Align.CrossMClosed:T⊤ OCF.Align.ValLabLadder:V-≺ OCF.Align.ValLabNeg:no-any-M₂ OCF.Align.ValLabNegTop:no-val-T⊤
