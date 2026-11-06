# -*- coding: utf-8 -*-
# Fab2SLs 一路的分层行数 (同 strattw/locslice_strattw.py 口径: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Align.Fab2SLs, 再 python3 locslice_fab2.py <H> [-v].
# 基础函数 (chunk, closure, lines, find, NOT) 取 locslice.py 的前半段 (到 B4= 之前), 同 strattw 脚本.
# 闭项 TΛs = CS.Tψ, CS = ColL GS LdS flS ΛS lΛS oneS lvS (KindLvTw 的参数化模块 ColL 的模块内定义手工列为根).
# 参数化模块 (KindLvRun, ColL, GenFoldRd, Tree, Om) 的模块内定义手工列为根. 手工根可能有遗漏, 是近似.
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
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'Fab2'))
def tree(P): return sum(lines(n) for n in P if n[0] not in NOT)
def note(P): return sum(lines(n) for n in P if n[0] in NOT)
def M(m,ns): return [(A+m,n) for n in ns.split()]
L1=(M('Fab2SLs','st FS SLs ιS νS tws Λs ΛS WS setH flat embA rdC')+
    M('LFReTy','LH Lv FL S⊥ ofHB')+M('LFReTower','tw Ω̂')+
    M('KindLvIf','lyL KLv LvFb CollLvFbTy')+
    M('GenFoldIf','StH NZ NZ₁ AccY DG₊ D Vs Vc ZK DK TopG FBA GenK LgDn FbLgAt FbLg Tg Df St Ig LW')+
    M('HtTowerTy','KS S₀ HB _⊲[_]_ LgB step sup Lev up ι _⊞_'))
L2=(M('Fab2SLs','GS LdS flS tpS KH lvS TΛs ordS fghΛs')+
    M('FabLFReGen','top⊥ ld⊥ LvΩ topLv ldLv w₀Lv lw₀Lv frE⊥')+
    M('KindLvTw','Act Y₀ W₁ ΔΩ ΨΩ Tψ')+
    M('KindLvRun','ω⋅ tg↑ τ₀ τ₁ zeroD _⨾ᴰ_ nlᴰ _⊕⟨_⟩_ cv Stp Ig↾ kk Bu Rk rkS rkT Cl₁ ClA Run Rpt RunNi Ai BNi Chn RKi RunC RKc RKk κc₁ κΔ₁ RKv RKa κcL κcA κΔA')+
    M('GenFoldTree','S→⊲ Kup Sk NZ-S nz⊲ nz₁→nz NZ₁-S zkS zΩ outC inC outS inS drp pt sum toD₀ Ωd Pre mkOf Int topStepG ≤rf ≤tr')+
    M('GenFoldRd','nbA lgW≤ rd₁ rdp₁ drp₁')+
    M('GenFoldInst','ldStep topSupG ldSup upd'))
L3=(M('Fab2SLs','tws-st Lg-tws Lg-Λs lΛS oneS stage-fst setH≤ setHLg setH-top embA-⊲ Lg-embA rdC-lg Lg-TΛs')+
    M('FabLFReGen','frE⊥-⊲ frE⊥-lg')+
    M('KindLvTw','lW₁ Lg-Tψ')+
    M('GenFoldTree','accL accC accᴸ sum-fst Lg-sum Lg-pt')+
    M('GenFoldRd','nbA-mono nbA-fst Lg-nbA rd₁-fst Lg-rd₁ Lg-rdp₁')+
    M('GenFoldInst','upd-R upd-Q upd-at'))
L4=(M('Fab2SLs','coord-stage top-head upd-keep setH-keep rdC-one rdC-form all-heads deep-lossy'))
acc=set(); print('== 无条件闭项 TΛs (站 ℕ 下标 SLs, 层 LH 一次封闭; 坍缩 ColL GS LdS flS ΛS lΛS oneS lvS)')
labs=['定义','折叠 (按级回灌的折叠, 可数读回, 精确升界, 闭项, FGH)','证书','对照, 形状']
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3,L4]),1):
    acc=acc|C(roots)
    print('  层%d %s: 本路新增 %d | 树侧全部 %d | 记号模块 %d'%(i,lab,new(acc),tree(acc),note(acc)))
    if i==3: P3=set(acc)
    if '-v' in sys.argv:
        c=collections.Counter()
        for n in acc: c[n[0].replace(A,'')]+=lines(n)
        print('      ',', '.join('%s %d'%kv for kv in c.most_common(40)))
print('== 前 3 层闭包里的 GenFoldRun 块:', sorted(n[1] for n in P3 if n[0]==A+'GenFoldRun') or '无')
print('== 前 3 层闭包里的 KindLvRd, StratTw*, NewTwr* 块:', sorted((n[0].replace(A,''),n[1]) for n in P3 if n[0]==A+'KindLvRd' or n[0].startswith(A+'StratTw') or n[0].startswith(A+'NewTwr')) or '无')
