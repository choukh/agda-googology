# -*- coding: utf-8 -*-
# LeanLv 一路的分层行数 (口径同 leanfb/locslice_leanfb.py: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Lean.LeanLv (入口, 导入全部), 再
#   python3 locslice_leanlv.py <H> [-v]
# 输出: (1) 主候选 TVs (LeanLvTmS) 的四层; (2) 第 3 层逐模块与按件分; (3) 同一台切片机重算 TF (LeanFbTm) 的第 3 层,
#       与 TVs 的共有 / 只在 TF / 只在 TVs; (4) 逐文件代码行.
import os,sys,io,collections
here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def tot(P): return sum(lines(n) for n in P if n[0] not in NOT)
def note(P): return sum(lines(n) for n in P if n[0] in NOT)
def M(pre,m,ns): return [(pre+m,n) for n in ns.split()]
def by_mod(P,pre):
    c=collections.Counter()
    for n in P: c[n[0].replace(pre,'')]+=lines(n)
    return c
V='-v' in sys.argv
Ln='OCF.Lean.'
FOLD='LW ω⋅ tg↑ τ₀ τ₁ zeroD _⨾ᴰ_ nlᴰ _⊕⟨_⟩_ cv Stp Ig↾ kk Bu Rk rkS rkT Cl₁ ClA Run Rpt RunNi Ai Chn RKi BNi RunC RKc RKk κc₁ κΔ₁ RKa κcF κΔA'
TREE2='S→⊲ Kup Sk NZ-S nz⊲ NZ₁-S accC accᴸ zkS zΩ outC inC outS inS drp pt sum toD₀ Ωd Pre mkOf Int nbA rd₁ rdp₁ drp₁ ≤rf ≤tr'
BASE1=(M(Ln,'LeanTBase','KS HB _⊲[_]_ LgB step sup up ι _⊞_ S⊥')+
    M(Ln,'LeanTLv','LH Lv FL SL νL node ofHB Ω̂ tw')+
    M(Ln,'LeanTTree','StH NZ NZ₁ AccY DG₊ D Vs Vc ZK BotK Tg Df St Ig Fb')+
    M(Ln,'LeanFbIf','Up LvRd Feed Plan')+
    M(Ln,'LeanFbSt','st FS SLs νS ιS tws Λs ΛF WS upd bumpH')+
    M(Ln,'LeanFbSlot','num eqN cast bump addN addSt PosN PosSt kN kSt uncast coN coSt Mem MemSt')+
    M(Ln,'LeanFbRd','AK0'))
BASE3=(M(Ln,'LeanFbSt','lΛF oneF Lg-tws tws-st upd-R upd-Q upd-at')+
    M(Ln,'LeanFbSlot','eqN-num bump-fst addN≤ addSt≤ Lg-cast Lg-bump Lg-addN Lg-addSt top-new top-addN top-addSt')+
    M(Ln,'LeanFbRd','rdX-fst Lg-rdX Lg-rdpX')+
    M(Ln,'LeanTTree','sum-fst Lg-sum Lg-pt rd₁-fst Lg-rd₁ Lg-rdp₁')+M(Ln,'LeanTBase','lgB⊲ cmpB Lg-⊞ Lg-up Lg-ι'))
L1=BASE1+M(Ln,'LeanLvIf','Emb Sim⁺')
L2=(M(Ln,'LeanLvTmS','simC⁺ σ₂⁺ RLs feedLs planKs planS fbS ActS ΨVs TVs fghVs')+M(Ln,'LeanLvTmS','Sg')+
    M(Ln,'LeanLvEmb','idE stepE supE _∘E_ botE supMap nbJ ΩE ΩMap nodeMap embΩ emb2')+
    M(Ln,'LeanLvRdS','Br readS readSp rdN rdP slf wrS wrK')+
    M(Ln,'LeanFbTm','bkS feed0 feed1 toFb')+
    M(Ln,'LeanT','iter FGH')+M(Ln,'LeanTFold',FOLD)+M(Ln,'LeanTTree',TREE2)+
    M(Ln,'LeanFbSt','headUp')+M(Ln,'LeanFbSlot','slotUp memS memN memSt')+
    M(Ln,'LeanFbRd','newAK rdX rdpX R0 RX'))
L3=(M(Ln,'LeanLvTmS','Lg-TVs Sg⊲')+
    M(Ln,'LeanLvEmb','nbJ-mono nbJ-fst Lg-nbJ')+
    M(Ln,'LeanLvRdS','readS-fst rdN-fst rdP-fst slf-fst Lg-readS Lg-readSp Lg-rdN Lg-rdP Lg-slf')+BASE3)
L4=(M(Ln,'LeanLvShape','IsL heads-fed lv-layer Sg1≢1 own2-x own2-em own2-Q lvm-x κa κa-co κb-co κa≢κb bd0 x₀ rd-a rd-b rd-ab0 pick2 pick3 hz≢1 kinds0 kinds1 x₂-lossy-Sim exec-head Dir nav exec-TVs2 fb2 fb2-ℓ')+
    M(Ln,'LeanLvVal','hasK-⊞ βW rdΩd Y-Ωd hY-Ωd')+[(Ln+'LeanLvVal','module Cell'),(Ln+'LeanLvVal','module CellΩ'),(Ln+'LeanLvVal','c'),(Ln+'LeanLvVal','δ₀'),(Ln+'LeanLvVal','top0'),(Ln+'LeanLvVal','top0-Ωd')]+M(Ln,'LeanLvTmS','lvSims')+M(Ln,'LeanLvIf','LvSim HasK'))
labs=['定义','+折叠 (读回, 一般折叠, 计划, 闭项, FGH)','+证书','+形状与世界定理']
print('== 闭项 TVs (OCF.Lean.LeanLvTmS)')
acc=set(); P={}
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3,L4]),1):
    acc=acc|C(roots); P[i]=set(acc)
    print('  层%d %s: 树侧 %d | 记号模块 %d'%(i,lab,tot(acc),note(acc)))
    if V: print('      ',', '.join('%s %d'%kv for kv in by_mod(acc,Ln).most_common(40)))
c=by_mod(P[3],Ln)
print('  层3 逐模块:',', '.join('%s %d'%kv for kv in c.most_common(40)))
bad=[n for n in P[3] if not n[0].startswith(Ln)]
print('  层3 闭包里 OCF.Lean 之外的仓库模块块数:',len(bad), sorted({n[0] for n in bad}))

# (2b) 经 LeanFbTm 根上的模块应用 (open Fold … fb) 带进来, 但 TVs 语义上不用的块 (切片的上近似)
EXTRA={'feedH','planK','plan','fb','find0','findSt','oldAK','supAK','Act','ΨF','TF','fghF'}
ex=[n for n in P[3] if n[0] in (Ln+'LeanFbTm',Ln+'LeanFbRd') and chunk(n[0]).chunks[n[1]]['name'] in EXTRA]
print('  层3 里经 LeanFbTm 的模块应用带进的旧计划块: %d 行 (%s)'%(sum(lines(n) for n in ex),', '.join(sorted(chunk(n[0]).chunks[n[1]]['name'] for n in ex))))

# (3) TF 的第 3 层, 根同 leanfb/locslice_leanfb.py
F1=BASE1
F2=(M(Ln,'LeanFbTm','bkS feed0 feed1 feedH planK plan toFb fb Act ΨF TF fghF')+
    M(Ln,'LeanT','iter FGH')+M(Ln,'LeanTFold',FOLD)+M(Ln,'LeanTTree',TREE2)+
    M(Ln,'LeanFbSt','headUp')+M(Ln,'LeanFbSlot','slotUp memS memN memSt')+
    M(Ln,'LeanFbRd','newAK oldAK supAK find0 findSt rdX rdpX R0 RX'))
F3=M(Ln,'LeanFbTm','Lg-TF')+BASE3
Fset=C(F1)|C(F2)|C(F3)
print('== 对照 TF 第 3 层: %d; TF 与 TVs 共有 %d, 只在 TF %d, 只在 TVs %d'%(tot(Fset),tot(Fset&P[3]),tot(Fset-P[3]),tot(P[3]-Fset)))
only=by_mod(P[3]-Fset,Ln); onlyF=by_mod(Fset-P[3],Ln)
print('   只在 TVs 逐模块:',', '.join('%s %d'%kv for kv in only.most_common(40)))
print('   只在 TF 逐模块:',', '.join('%s %d'%kv for kv in onlyF.most_common(40)))
if V:
    for n in sorted(P[3]-Fset):
        print('     +',n[0].replace(Ln,''),chunk(n[0]).chunks[n[1]]['name'],lines(n))
    for n in sorted(Fset-P[3]):
        print('     -',n[0].replace(Ln,''),chunk(n[0]).chunks[n[1]]['name'],lines(n))

# (4) 逐文件代码行
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('== 各文件代码行 (agda 块非空非注释 / 全文)')
for m in ['LeanLvIf','LeanLvEmb','LeanLvRd','LeanLvRdS','LeanLvTm','LeanLvTmS','LeanLvShape','LeanLvVal','LeanLvTest','LeanLv']:
    p=os.path.join(R,'probes','OCF','Lean',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st_=l.strip()
        if st_.startswith('```'): inc=st_.startswith('```agda'); continue
        if inc and st_ and not st_.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
