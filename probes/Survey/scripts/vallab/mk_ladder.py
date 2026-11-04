#!/usr/bin/env python3
"""把 ValueJudgeLadder (对 HtS) 机械改写成对 HtB 的 ValLabLadder. 只换名字."""
import re,sys,os
root=os.path.join(os.path.dirname(__file__),'..','..','..','OCF','Align')
s=open(os.path.join(root,'ValueJudgeLadder.lagda.md'),encoding='utf8').read()
s=s.replace('OCF.Align.LadderInfBase','OCF.Align.LadderOrdBase').replace('OCF.Align.ValueJudgeLadder','OCF.Align.ValLabLadder')
s=s.replace('(𝕊 : HtS)','(𝕊 : HtB)').replace('OCF.Align.LadderInf','OCF.Align.LadderOrd')
s=s.replace('# 值判据 (一): 塔上的相对值','# 值验收: 塔上的相对值, 对 `HtB`')
s=s.replace('> **判决: HOLDS (编译过, 无条件).** 底座. 结论写在 [ValueJudge](ValueJudge.lagda.md). 对高度结构 `HtS` 参数化, 不含记号.','> **机械改写.** 由 [ValueJudgeLadder](ValueJudgeLadder.lagda.md) 经 `Survey/scripts/vallab/mk_ladder.py` 生成: 只把 `HtS`, `LadderInf*` 换成 `HtB`, `LadderOrd*`. 入口 [ValLab](ValLab.lagda.md). 不含记号.')
open(os.path.join(root,'ValLabLadder.lagda.md'),'w',encoding='utf8').write(s)
