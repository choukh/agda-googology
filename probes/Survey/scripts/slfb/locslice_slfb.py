# -*- coding: utf-8 -*-
# SLFb 一路的分层行数 (同 newtwr/locslice_newtwr.py 口径: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Align.SLFb, 再 python3 locslice_slfb.py <H> [-v].
# 基础函数 (chunk, closure, lines, find, NOT) 取 locslice.py 的前半段 (到 B4= 之前).
# 参数化模块 (SLFbRd, KindLvRun, KindLvTw.ColL, GenFoldRd, Tree, Om) 的模块内定义手工列为根.
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
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'SLFb'))
def tree(P): return sum(lines(n) for n in P if n[0] not in NOT)
def note(P): return sum(lines(n) for n in P if n[0] in NOT)
def M(m,ns): return [(A+m,n) for n in ns.split()]
L1=(M('SLFbIf','SNᵢ jN resN AK KC HdFb')+
    M('KindLvIf','KLv LvFb CollLvFbTy')+
    M('GenFoldIf','StH NZ NZ₁ AccY DG₊ D Vs Vc ZK DK TopG FBA GenK LgDn FbLgAt FbLg Tg Df St Ig LW')+
    M('HtTowerTy','KS HB _⊲[_]_ LgB step sup up ι _⊞_')+
    M('LFReTy','LH Lv S⊥ FL SL νL ofHB node')+M('RsOwnIf','RsK'))
L2=(M('SLFbTm','kₙ FN SN tpN GN ιN ΩN B ΛN kc→KLv hdKit dpKit KH₁ KH KHn lvN collN TF ordF fghF')+
    M('SLFbKit','topV topΩ toB kcNew kcOld kcℕ kcL mapS kcLv kcSt akNew akOld akSup akV akSt')+
    M('SLFbRd','rdQ rdpQ')+
    M('LFReTower','Ω̂ tw')+
    M('FabLFReGen','top⊥ LvΩ w₀Lv frE⊥')+
    M('KindLvTw','Act Y₀ W₁ ΔΩ ΨΩ Tψ collLv')+
    M('KindLvRun','ω⋅ tg↑ τ₀ τ₁ zeroD _⨾ᴰ_ nlᴰ _⊕⟨_⟩_ cv Stp Ig↾ kk Bu Rk rkS rkT Cl₁ ClA Run Rpt RunNi Ai BNi Chn RKi RunC RKc RKk κc₁ κΔ₁ RKv RKa κcL κcA κΔA')+
    M('GenFoldTree','S→⊲ Kup Sk NZ-S nz⊲ nz₁→nz NZ₁-S zkS zΩ outC inC outS inS drp pt sum toD₀ Ωd Pre mkOf Int topStepG ≤rf ≤tr')+
    M('GenFoldRd','nbA lgW≤ rd₁ rdp₁ drp₁')+
    M('GenFoldInst','topSupG upd updL'))
L3=(M('SLFbTm','Lg-ΩN lB lΛN one⊲N LdN flN Lg-TF')+
    M('SLFbKit','toB-⊲ Lg-toB')+
    M('SLFbRd','rdQ-fst Lg-rdQ Lg-rdpQ')+
    M('FabLFReGen','ld⊥ ldLv lw₀Lv frE⊥-⊲ frE⊥-lg')+
    M('KindLvTw','lW₁ Lg-Tψ')+
    M('GenFoldTree','accL accC accᴸ sum-fst Lg-sum Lg-pt')+
    M('GenFoldRd','nbA-mono nbA-fst Lg-nbA rd₁-fst Lg-rd₁ Lg-rdp₁')+
    M('GenFoldInst','ldStep ldSup upd-R upd-Q upd-at'))
L4=(M('SLFbTm','embN embN-⊲ Lg-embN res-Bd headFb tw-shape stage-lΩ HasAK akV-suc ℓ-of head-ℓ1 head-ℓ0 head-rs-top deep2-lossy deep2-left-fed fb-lossyN top-base-V top-baseN rd-n1-at rd-n1 emb-head')+
    M('SLFbKit','deep-lossy-Lv new-fed lΩ-left-fed akV-lΩ')+
    M('SLFbRd','OnlyA onlyA-nbA onlyA-rdQ onlyA-rdpQ')+
    M('SLFbStuck','J Slot WJ sel rsJ UIPat sel-top rsJ-top decZ nz nz-const trans-sym nz-canon uip-hz')+
    M('SLFbIf','RsSL RsSLᴾ RsUp RsSL⊵ RsEv'))
acc=set(); print('== 无条件闭项 TF (SN = SNᵢ kₙ; 坍缩 collLv GN LdN flN ΛN lΛN one⊲N lvN)')
labs=['定义','折叠 (子结构, 回灌件, 读回, 按级回灌的折叠, 层, 闭项, FGH)','证书','形状, 盲点, 卡点']
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3,L4]),1):
    acc=acc|C(roots)
    print('  层%d %s: 本路新增 %d | 树侧全部 %d | 记号模块 %d'%(i,lab,new(acc),tree(acc),note(acc)))
    if i==3: P3=set(acc)
    if '-v' in sys.argv:
        c=collections.Counter()
        for n in acc: c[n[0].replace(A,'')]+=lines(n)
        print('      ',', '.join('%s %d'%kv for kv in c.most_common(40)))
def names(P): return {(n[0].replace(A,''),chunk(n[0]).chunks[n[1]]['name']) for n in P}
nm=names(P3)
bad=[x for x in nm if x[1] in ('rd₂','rdp₂','evAt','evB','T⁺','TΛ','encH','toD₁') or x[0] in ('HtTowerFFold','HtTowerFClosed','HtTowerFRead','SLFbStuck')]
print('== 前 3 层闭包里读进 Ht 的定义或 SLFbStuck 的块:', sorted(bad) if bad else '无')
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('== 各文件代码行 (agda 块非空非注释)')
for m in ['SLFbIf','SLFbKit','SLFbRd','SLFbTm','SLFbStuck','SLFb']:
    p=os.path.join(R,'probes','OCF','Align',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
