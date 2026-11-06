# -*- coding: utf-8 -*-
# KindLv 一路的分层行数 (同 genfold/locslice_genfold.py 口径: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译一个导入 OCF.Align.KindLv 的模块, 再 python3 locslice_kindlv.py <H> [-v].
# 基础函数 (chunk, closure, lines, find, NOT) 取 locslice.py 的前半段 (到 B4= 之前), 同 dnfold 脚本.
# 模块应用 CK = ColL GΛ … lvΛ 的实参与参数化模块 (EvK, ColL, KindLvRun, KindLvRd, GenFoldRun, GenFoldRd, NewTwrRd, EvN, Tree, Om) 的模块内定义手工列为根.
# 另外检查: 闭项前 3 层的闭包里是否出现读进 Ht 的定义 (rd₂, evAt, evB, T⁺, TΛ, HtTowerFFold 的模块).
import os,sys,io,collections
here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
A='OCF.Align.'
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'KindLv'))
def tree(P): return sum(lines(n) for n in P if n[0] not in NOT)
def note(P): return sum(lines(n) for n in P if n[0] in NOT)
def M(m,ns): return [(A+m,n) for n in ns.split()]
L1=(M('KindLvIf','Emb lyL RdLTy WrLTy KLv LvFb CollLvFbTy')+
    M('GenFoldIf','StH NZ NZ₁ AccY DG₊ D Vs Vc ZK DK TopG FBA GenK LgDn FbLgAt FbLg Tg Df St Ig LW')+
    M('HtTowerTy','KS S₀ HB _⊲[_]_ LgB step sup Lev up ι _⊞_')+M('LvKtIf','FN nxt Kc KΛc emb injL ιΛ'))
L2=(M('KindLvEmb','idE stepE supE _∘E_ nbJ')+
    M('KindLvRd','lgW≤ Br readL readLp rdS wrL wrK')+
    M('KindLvRun','ω⋅ tg↑ τ₀ τ₁ zeroD _⨾ᴰ_ nlᴰ _⊕⟨_⟩_ cv Stp Ig↾ kk Bu Rk rkS rkT Cl₁ ClA Run Rpt RunNi Ai BNi Chn RKi RunC RKc RKk κc₁ κΔ₁ RKv RKa κcL κcA κΔA')+
    M('KindLvTw','Act Y₀ W₁ ΔΩ ΨΩ Tψ collLv B inc Bᴧ ΛB Λ IsTwo isTwo κ₁ W₁′ sel up₂ K1 lvΛ TK ordK fghK')+
    M('KindLvEv','Act Y₀ out₂ out₂K evK ρK')+
    M('NewTwrRd','toDᵀ qy cumT flatT rdG rdpG')+
    M('NewTwrColl','GΛ')+
    M('NewTwrEv','two LX W₀X ΩX')+
    M('GenFoldTree','S→⊲ Kup Sk NZ-S nz⊲ nz₁→nz NZ₁-S zkS zΩ outC inC outS inS drp pt sum toD₀ Ωd Pre mkOf Int topStepG ≤rf ≤tr')+
    M('GenFoldRd','nbA lgW≤ rd₁ rdp₁ drp₁')+
    M('GenFoldInst','fbS₀ genS₀ liftFB liftS genStep topSupG genSupNo upd liftℕ liftSℕ genSupℕ genLev genFN genNxt liftL liftSL updL genKc'))
L3=(M('KindLvEmb','nbJ-mono nbJ-fst Lg-nbJ LgΩ')+
    M('KindLvRd','readL-fst rdS-fst Lg-readL Lg-readLp Lg-rdS')+
    M('KindLvTw','lW₁ Lg-Tψ lB lBᴧ lΛ one⊲ sel≤ up₂≤ selLg up₂Lg Lg-TK')+M('KindLvEv','lg-evK lρK')+
    M('NewTwrRd','lWy Lg-cumT Lg-flatT rdG-fst Lg-rdG Lg-rdpG')+
    M('NewTwrColl','LdΛ flΛ')+M('NewTwrEv','lLX oLX eLX lW₀X')+
    M('GenFoldTree','accL accC accᴸ sum-fst Lg-sum Lg-pt')+
    M('GenFoldRd','nbA-mono nbA-fst Lg-nbA rd₁-fst Lg-rd₁ Lg-rdp₁')+
    M('GenFoldInst','ldS₀ ldStep ldSup ldLev flS₀ flLift flStep flSupNo flLiftℕ flSupℕ flLev upd-R upd-Q upd-at ldFN ldNxt flLiftL flNxt ldKc flKc'))
L4=(M('KindLvCmp','_≈_ ≈-rf nbA-cong rdL0≈rd₁ rdpL0≈rd₁ wr0-z toD₁-z wr0-s toD₁-s wr0-l toD₁-l wr0-Ω toD₁-Ω nbJ≈nbᴮ rdL1-new rdL1-old rdL1-nc rdL1-notA κ₁-in-Bᴧ lv-κ₁ K1-ℓ K1-rd K1-seen κ₁-was-lossy'))
acc=set(); print('== 无条件闭项 TK (塔 B, Bᴧ; 下降 ρK; 坍缩 CK = ColL GΛ LdΛ flΛ Λ lΛ one⊲ lvΛ)')
labs=['定义','折叠 (级读回, 嵌入, 按级回灌的折叠, 塔, 对角, 每站求值, 闭项, FGH)','证书','对照, 形状']
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3,L4]),1):
    acc=acc|C(roots)
    print('  层%d %s: 本路新增 %d | 树侧全部 %d | 记号模块 %d'%(i,lab,new(acc),tree(acc),note(acc)))
    if i==3: P3=set(acc)
    if '-v' in sys.argv:
        c=collections.Counter()
        for n in acc: c[n[0].replace(A,'')]+=lines(n)
        print('      ',', '.join('%s %d'%kv for kv in c.most_common(40)))
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('== 前 3 层闭包里的 GenFoldRun 块:', sorted(n[1] for n in P3 if n[0]==A+'GenFoldRun') or '无')
print('== 各文件代码行 (agda 块非空非注释)')
for m in ['KindLvIf','KindLvEmb','KindLvRd','KindLvRun','KindLvEv','KindLvTw','KindLvCmp','KindLv']:
    p=os.path.join(R,'probes','OCF','Align',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
