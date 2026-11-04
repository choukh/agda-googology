import os
# 由 LadderMono{Rel,Down,Main} 生成标签世界的克隆 LadderMonoW*: 只改导入 (规则同 Survey/scripts/laddernf/mk_w.py)
import re
A=os.path.join(os.environ.get('REPO') or os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..','..')),'probes/OCF/Align/')
MODS='Rel Cx Rules Rules2 Rules3 Strict Strict2 Strict3 Class ClassF Good Vis Read Iota Tr Add Psi PsiH Eval Tail Mono Root Omega Main'.split()
shim={'Floor':'WFloor','Aux':'WAux','Tree':'WFT','Base':'WBase'}
def rewrite(s):
    s=s.replace('OCF.Free.Eq','OCF.Align.LadderNFWEq')
    s=re.sub(r'OCF\.Align\.LadderNF(?=Tree\b)','OCF.Align.LadderNFW',s)
    for m in sorted(MODS,key=len,reverse=True):
        s=re.sub(r'OCF\.Align\.LadderNF'+m+r'\b','OCF.Align.LadderNFW'+m,s)
    s=s.replace('OCF.Free.Level','OCF.Align.Level').replace('OCF.Free.Prefix','OCF.Align.LadderNFWPrefix')
    s=s.replace('OCF.Free.Force','OCF.Align.LadderNFWForce')
    for X,W in shim.items():
        s=s.replace('OCF.Free.'+X,'OCF.Align.LadderNF'+W)
    s=re.sub(r'OCF\.Align\.LadderMono(Rel|Down|Main)\b',r'OCF.Align.LadderMonoW\1',s)
    return s
for m in ['Rel','Down','Main']:
    t=open(A+'LadderMono'+m+'.lagda.md',encoding='utf-8').read()
    t=rewrite(t)
    t='> **机械克隆, 验收用.** 由 `LadderMono'+m+'` 经脚本复制, 只改导入 (规则同 `Survey/scripts/laddernf/mk_w.py`), 把证书搬到标签阶梯的世界. 见 [LadderMonoAccept](LadderMonoAccept.lagda.md).\n\n'+t
    open(A+'LadderMonoW'+m+'.lagda.md','w',encoding='utf-8').write(t)
