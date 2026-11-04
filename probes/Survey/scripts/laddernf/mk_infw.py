# 由 LadderInf* 生成标签世界的克隆 LadderInfW*: 只改导入 (规则同 mk_w.py), 代码行逐字.
import re,os
R=os.environ.get('REPO') or os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..','..'))
A=R+'/probes/OCF/Align/'
NFM='Rel Cx Rules Rules2 Rules3 Strict Strict2 Strict3 Class ClassF Good Vis Read Iota Tr Add Psi PsiH Eval Tail Mono Root Omega Main'.split()
MODS='Tree Rel Cx Rules Rules2 Rules3 Strict Strict2 Strict3 Class ClassF Good Vis Read Iota Tr Add Psi PsiH Eval Tail Mono Root Omega Main Top Dn DnSelf BridgeTop Agree Nat Bridge'.split()
shim={'Floor':'WFloor','Aux':'WAux','Tree':'WFT','Base':'WBase'}
def rewrite(s):
    s=s.replace('OCF.Free.Eq','OCF.Align.LadderNFWEq')
    s=re.sub(r'OCF\.Align\.LadderNF(?=Tree\b)','OCF.Align.LadderNFW',s)
    for m in sorted(NFM,key=len,reverse=True):
        s=re.sub(r'OCF\.Align\.LadderNF'+m+r'\b','OCF.Align.LadderNFW'+m,s)
    s=re.sub(r'OCF\.Align\.LadderMono(Rel|Down|Main)\b',r'OCF.Align.LadderMonoW\1',s)
    s=s.replace('OCF.Free.Level','OCF.Align.Level').replace('OCF.Free.Prefix','OCF.Align.LadderNFWPrefix')
    s=s.replace('OCF.Free.Force','OCF.Align.LadderNFWForce')
    for X,W in shim.items():
        s=s.replace('OCF.Free.'+X,'OCF.Align.LadderNF'+W)
    for m in sorted(MODS,key=len,reverse=True):
        s=re.sub(r'OCF\.Align\.LadderInf'+m+r'\b','OCF.Align.LadderInfW'+m,s)
    return s
for m in MODS:
    t=open(A+'LadderInf'+m+'.lagda.md',encoding='utf-8').read()
    t=rewrite(t)
    t='> **机械克隆, 验收用.** 由 `LadderInf'+m+'` 经 `Survey/scripts/laddernf/mk_infw.py` 复制, 只改导入, 落在标签阶梯的世界. 见 [LadderInfAccept](LadderInfAccept.lagda.md).\n\n'+t
    open(A+'LadderInfW'+m+'.lagda.md','w',encoding='utf-8').write(t)
