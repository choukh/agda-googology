# -*- coding: utf-8 -*-
# Third 一路的分层行数 (口径同 recb/locslice_recb.py: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Lean.Third, 再 python3 locslice_third.py <H>
# 参数化模块 (ThirdFold, ThirdPath, ThirdSan, ThirdX) 经模块应用使用; 切片看不见模块应用, 用到的模块内定义手工列为根.
import os,sys,io,collections
here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
# 同 recb: 只用 CRw 的 FGH, 不跟随 CRw 根上的 open
_succ=succ
def succ(node):
    out=_succ(node)
    if node[0]!='OCF.Lean.CRw': return out
    f=chunk('OCF.Lean.CRw'); op=set(f.chunks[f.rootc].get('opens',[]))
    return [t for t in out if not (t[0]=='OCF.Lean.CRw' and t[1] in op)]
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def tot(P): return sum(lines(n) for n in P if n[0] not in NOT)
def note(P): return sum(lines(n) for n in P if n[0] in NOT)
def M(m,ns): return [('OCF.Lean.'+m,n) for n in ns.split()]
def by_mod(P):
    c=collections.Counter()
    for n in P: c[n[0].replace('OCF.Lean.','')]+=lines(n)
    return ', '.join('%s %d'%kv for kv in c.most_common(40))
FOLDN='T _⊲ᵘ_ Gd AdT San Gd-⊞ GT mulG ΣG chainG limG Cg cgS cgL cgO cg Dg pickG dcg AccC wfC gC lg↓ ⊏⊑ nodeG Φ'
SHN='Sh Sh-⊞ ShG Sh-mul Sh-Σ Sh-chain Sh-node Sh-Φ'
SANN='sf san sN gd-san gN gd-z Gd-up Gd-ιL Gd-ιO tpS ΣS gd-tp gd-ΣS Er ph-san pN ph-tp ph-ΣS'
PATHN='ClP pS pL pO clP evE upkE evA upkA PH-mulG PH-ΣG PH-chainG Ok PH-node okP okB Pm okD PH-Φ'
XN='PoU sh₀ Adm₀ EvX AdX nxX PSX ⊤̂ dcI dcx aS ↑S ΦX PH-ΦX↓'
L1=(M('CRwBase','KS HB _⊲[_]_ LgB step sup up ι S⊥ Cd _⊲_ _⊞_')+M('ThirdIf','Tw Pos')+
    M('ThirdTw','Ix FX XSof Sb ιK gtX fl topT ΣT')+M('ThirdPS','Po PS PH psStep psSup PSL triv FQ lift'))
L2=(M('ThirdTw','emb frE posE along frA posA')+M('ThirdPS','PH-mono PH-⊞ PH-up PH-ι')+
    M('ThirdFold',FOLDN)+M('ThirdSan',SANN)+M('ThirdPath',PATHN)+
    M('ThirdLeg','Σᴸ cxX legX legN Lg-legX Lg-legN Lg-Σ legC Lg-legC Lg-ΣC legS Lg-legS wT lwT bnd lg-bnd wS lwS pkT pkT-bd pkT-top pkS pk-bd pk-top')+
    M('ThirdX',XN)+
    M('ThirdTm','PH-cp gdT PH-gt PH-fl PH-gtL Qs own liftE QL Gdn b₀ stp ↓Gd desc every gd-fl TN yΛ TΛ fghΛ')+M('CRw','iter FGH'))
L3=(M('ThirdFold',SHN)+M('ThirdX','Sh-ΦX')+M('ThirdTm','Sh-desc sh→lg LgB-TN lg-yΛ LgB-TΛ'))
labs=['定义','+折叠, 实例, 闭项, FGH','+证书']
acc=set(); P={}
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3]),1):
    acc=acc|C(roots); P[i]=set(acc)
    print('层%d %s: 树侧 %d | 记号模块 %d'%(i,lab,tot(acc),note(acc)))
    print('    逐模块:',by_mod(acc))
ok=('OCF.Lean.Third','OCF.Lean.CRwBase','OCF.Lean.CRw','OCF.Lean.LHRec')
bad=[n for n in P[3] if not n[0].startswith(ok)]
print('层3 闭包里 Third*, CRw*, LHRec* 之外的仓库模块块数:',len(bad), sorted({n[0] for n in bad}))
new=set(n for n in P[3] if n[0].startswith('OCF.Lean.Third'))
print('层3 里 Third* 新写的块: %d 行; 沿用的块: %d 行'%(sum(lines(n) for n in new), tot(P[3])-sum(lines(n) for n in new)))
def piece(lab,ms):
    xs=set(x for m,n in ms for x in find(m,n))
    print('  %-44s %d'%(lab,sum(lines(n) for n in xs&P[3])))
print('逐件 (块的行数, 不含依赖, 只计层 3 内):')
piece('接口用到的 (Tw, Pos)',M('ThirdIf','Tw Pos'))
piece('底与地板 (Ix FX XSof Sb ιK gtX fl topT ΣT)',M('ThirdTw','Ix FX XSof Sb ιK gtX fl topT ΣT'))
piece('嵌入 (emb frE posE along frA posA)',M('ThirdTw','emb frE posE along frA posA'))
piece('路径结构 (ThirdPS)',M('ThirdPS','Po PS PH PH-mono PH-⊞ psStep psSup PH-up PH-ι PSL triv FQ lift'))
piece('同底折叠与决定 (ThirdFold, 不含形状)',M('ThirdFold',FOLDN))
piece('形状证书 (Sh*)',M('ThirdFold',SHN)+M('ThirdX','Sh-ΦX'))
piece('洗法实例 (ThirdSan)',M('ThirdSan',SANN))
piece('下层路径 (ThirdPath)',M('ThirdPath',PATHN))
piece('合法化 (legX legC ...)',M('ThirdLeg','Σᴸ cxX legX legN Lg-legX Lg-legN Lg-Σ legC Lg-legC Lg-ΣC legS Lg-legS'))
piece('世界与代表坐标',M('ThirdLeg','wT lwT bnd lg-bnd wS lwS pkT pkT-bd pkT-top pkS pk-bd pk-top'))
piece('跨底折叠与 PH-ΦX↓ (ThirdX)',M('ThirdX',XN))
piece('地板路径, 世界塔, 下降',M('ThirdTm','PH-cp gdT PH-gt PH-fl PH-gtL Qs own liftE QL Gdn b₀ stp ↓Gd desc every gd-fl'))
piece('闭项, FGH, 证书',M('ThirdTm','TN yΛ TΛ fghΛ Sh-desc sh→lg LgB-TN lg-yΛ LgB-TΛ'))
