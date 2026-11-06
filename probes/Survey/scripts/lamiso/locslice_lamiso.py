# -*- coding: utf-8 -*-
# LamIso 一路的分层行数 (口径同 leanlv/locslice_leanlv.py: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 依次编译 OCF.Lean.LamIso 与 OCF.Lean.LeanLv (同一个 <H>), 再
#   python3 locslice_lamiso.py <H> [-v]
# 输出: (1) 闭项 TI (LamIsoTm) 的四层; (2) 第 3 层逐模块; (3) 同一台切片机重算 TVs (LeanLvTmS) 的第 3 层,
#       与 TI 的共有 / 只在 TVs / 只在 TI, 只在 TI 的逐件; (4) 逐文件代码行.
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
COMMON2=(M(Ln,'LeanLvEmb','idE stepE supE _∘E_ botE')+
    M(Ln,'LeanLvRdS','Br readS readSp rdN rdP slf wrS wrK')+
    M(Ln,'LeanT','iter FGH')+M(Ln,'LeanTFold',FOLD)+M(Ln,'LeanTTree',TREE2)+
    M(Ln,'LeanFbSt','headUp')+M(Ln,'LeanFbSlot','slotUp memS memN memSt')+
    M(Ln,'LeanFbRd','newAK rdX rdpX'))
COMMON3=(M(Ln,'LeanLvEmb','nbJ-mono nbJ-fst Lg-nbJ')+
    M(Ln,'LeanLvRdS','readS-fst rdN-fst rdP-fst slf-fst Lg-readS Lg-readSp Lg-rdN Lg-rdP Lg-slf')+BASE3)
I1=(BASE1+M(Ln,'LeanLvIf','Emb Sim⁺')+M(Ln,'LamIsoIf','Prt')+
    M(Ln,'LamIsoPsi','X it Zf eqH ΩF lft rgt Src Gb Qt Pv Qn Ψ')+
    M(Ln,'LamIsoL','Est tw-eq g₀ Gt Et Sr L ΛL Λ′'))
I2=(M(Ln,'LamIsoTm','bkS toS R0′ RX′ Rown feed0′ feed1′ feedOwn planKI planI toFbI fbI ActI ΨI TI fghI')+
    M(Ln,'LamIsoL','prtL skL')+M(Ln,'LamIsoPsi','Prt-Ψ prtNode P⟨_⟩ eqS eqL eqΩ')+COMMON2)
I3=(M(Ln,'LamIsoTm','Lg-TI')+M(Ln,'LamIsoPsi','Ψ-fst Ψ-step Ψ-mono Lg-Ψ')+
    M(Ln,'LamIsoL','Lg-L L-st Lg-ΛL lΛ′ L⊲ one′')+COMMON3)
I4=(M(Ln,'LamIsoShape','own-x own-em own-layer own-reads plan-own g₂ L3-top L3-br0 L3-node L3-node-co kTop3 kTop3-co g₃ w3 lw3 wS lwS W3 lW3 r3 x3 rd-top3 rd-top3-has')+
    M(Ln,'LamIsoL','lamIso')+M(Ln,'LamIsoTm','own lvSimI toSim')+M(Ln,'LamIsoIf','LamIso OwnRd')+M(Ln,'LeanLvIf','LvSim HasK')+
    M(Ln,'LamIsoVal','κT3 kO rdΩd3 rdΩd3-base rdΩd4 hasK-⊞ Y-Ωd')+[(Ln+'LamIsoVal',x) for x in ('module Cell','module CellΩ3','c','δ₀','top0','top0-Ωd')])
labs=['定义 (树, 层 L, 最高层 Λ′)','+折叠 (同形, 读回, 一般折叠, 计划, 闭项, FGH)','+证书','+形状与世界定理']
print('== 闭项 TI (OCF.Lean.LamIsoTm)')
acc=set(); P={}
for i,(lab,roots) in enumerate(zip(labs,[I1,I2,I3,I4]),1):
    acc=acc|C(roots); P[i]=set(acc)
    print('  层%d %s: 树侧 %d | 记号模块 %d'%(i,lab,tot(acc),note(acc)))
c=by_mod(P[3],Ln)
print('  层3 逐模块:',', '.join('%s %d'%kv for kv in c.most_common(40)))
bad=[n for n in P[3] if not n[0].startswith(Ln)]
print('  层3 闭包里 OCF.Lean 之外的仓库模块块数:',len(bad), sorted({n[0] for n in bad}))
EXTRA={'feedH','planK','plan','fb','find0','findSt','oldAK','supAK','Act','ΨF','TF','fghF','feed0','feed1','toFb','R0','RX'}
ex=[n for n in P[3] if n[0] in (Ln+'LeanFbTm',Ln+'LeanFbRd') and chunk(n[0]).chunks[n[1]]['name'] in EXTRA]
print('  层3 里经 LeanFbTm 的模块应用带进的旧计划块: %d 行 (%s)'%(sum(lines(n) for n in ex),', '.join(sorted(chunk(n[0]).chunks[n[1]]['name'] for n in ex))))

# TVs 的第 3 层, 根同 leanlv/locslice_leanlv.py
V1=BASE1+M(Ln,'LeanLvIf','Emb Sim⁺')
V2=(M(Ln,'LeanFbTm','bkS')+M(Ln,'LeanLvTmS','simC⁺ σ₂⁺ RLs feedLs planKs planS fbS ActS ΨVs TVs fghVs Sg')+
    M(Ln,'LeanLvEmb','supMap nbJ ΩE ΩMap nodeMap embΩ emb2')+M(Ln,'LeanFbTm','feed0 feed1 toFb')+M(Ln,'LeanFbRd','R0 RX')+COMMON2)
V3=M(Ln,'LeanLvTmS','Lg-TVs Sg⊲')+COMMON3
Vset=C(V1)|C(V2)|C(V3)
print('== 对照 TVs 第 3 层: %d; 共有 %d, 只在 TVs %d, 只在 TI %d'%(tot(Vset),tot(Vset&P[3]),tot(Vset-P[3]),tot(P[3]-Vset)))
only=by_mod(P[3]-Vset,Ln); onlyV=by_mod(Vset-P[3],Ln)
print('   只在 TI 逐模块:',', '.join('%s %d'%kv for kv in only.most_common(40)))
print('   只在 TVs 逐模块:',', '.join('%s %d'%kv for kv in onlyV.most_common(40)))
pieces=collections.Counter()
for n in sorted(P[3]-Vset):
    nm=chunk(n[0]).chunks[n[1]]['name']; pieces[(n[0].replace(Ln,''),nm)]+=lines(n)
print('   只在 TI 逐件:')
for (m,nm),k in sorted(pieces.items()):
    print('     +',m,nm,k)
if V:
    for n in sorted(Vset-P[3]):
        print('     -',n[0].replace(Ln,''),chunk(n[0]).chunks[n[1]]['name'],lines(n))

R=os.path.abspath(os.path.join(here,'..','..','..'))
print('== 各文件代码行 (agda 块非空非注释 / 全文)')
for m in ['LamIsoIf','LamIsoPsi','LamIsoL','LamIsoTm','LamIsoShape','LamIsoVal','LamIsoTest','LamIso']:
    p=os.path.join(R,'probes','OCF','Lean',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st_=l.strip()
        if st_.startswith('```'): inc=st_.startswith('```agda'); continue
        if inc and st_ and not st_.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
