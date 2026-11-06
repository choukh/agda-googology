# -*- coding: utf-8 -*-
# GenFold 一路的分层行数 (同 dnfold/locslice_dnfold.py 口径: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译一个导入 OCF.Align.GenFold 的模块, 再 python3 locslice_genfold.py <H> [-v].
# 根表: 塔, 截断版, 级顶读回 (Def1 … UC, L4) 原样取 dnfold 脚本的前半段 (到 DnFold 的根之前); 本路的根在下面.
# 模块应用 KG = KD dnG dnL₀ 的实参 dnG, dnL₀, 与参数化模块 GenFoldRun, GenFoldRd, EvAt, EvX, Tree, Om 的模块内定义手工列为根.
import os,sys,io,collections
here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'dnfold','locslice_dnfold.py'),encoding='utf-8').read().split("\nDI=A+'DnFoldIf'")[0]
__file__=os.path.join(here,'dnfold','locslice_dnfold.py')
exec(s)
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'GenFold'))
def show(name,layers):
    acc=set(); print('==',name)
    for i,lab,roots in layers:
        if roots is None: print('  层%d %s: 无新增'%(i,lab)); continue
        acc=acc|C(roots)
        print('  层%d %s: 本路新增 %d | 树侧全部 %d | 记号模块 %d'%(i,lab,new(acc),tree(acc),note(acc)))
        if '-v' in sys.argv:
            c=collections.Counter()
            for n in acc: c[n[0].replace(A,'')]+=lines(n)
            print('      ',', '.join('%s %d'%kv for kv in c.most_common(40)))
GI=A+'GenFoldIf'; GT=A+'GenFoldTree'; GD=A+'GenFoldRd'; GR=A+'GenFoldRun'; GN=A+'GenFoldInst'; GE=A+'GenFoldEv'; GK=A+'GenFoldK'; GC=A+'GenFoldCmp'
def M(m,ns): return [(m,n) for n in ns.split()]
N1=M(GI,'StH NZ NZ₁ AccY DG₊ D Vs Vc ZK DK TopG FBA GenK LgDn FbLgAt FbLg Tg Df St Ig LW')
N2=(M(GT,'S→⊲ Kup Sk NZ-S nz⊲ nz₁→nz NZ₁-S zkS zΩ outC inC outS inS drp pt sum toD₀ Ωd Pre mkOf Int topStepG ≤rf ≤tr')+
    M(GD,'nbA lgW≤ rd₁ rdp₁ drp₁ toD₁ cumT encH qy lWy rd₂ rdp₂')+
    M(GR,'ω⋅ tg↑ τ₀ τ₁ zeroD _⨾ᴰ_ nlᴰ _⊕⟨_⟩_ cv Stp Ig↾ kk Bu Rk rkS rkT Cl₁ ClA Run Rpt RunNi Ai BNi Chn RKi RunC RKc RKk κc₁ κΔ₁ RKa κcA κΔA')+
    M(GN,'fbS₀ genS₀ liftFB liftS genStep topSupG genSupNo upd liftℕ liftSℕ genSupℕ genLev')+
    M(GE,'Act Y₀ out₂ evAt')+
    M(GK,'two LX W₀X ΩX evB constD dnG TG fghG TG∞'))
N3=(M(GT,'accL accC accᴸ sum-fst Lg-sum Lg-pt')+
    M(GD,'nbA-mono nbA-fst Lg-nbA rd₁-fst Lg-rd₁ Lg-rdp₁ rd₂-fst Lg-rd₂ Lg-rdp₂ Lg-cumT Lg-encH')+
    M(GN,'ldS₀ ldStep ldSup ldLev flS₀ flLift flStep flSupNo flLiftℕ flSupℕ flLev upd-R upd-Q upd-at')+
    M(GE,'lg-evAt')+M(GK,'lLX oLX eLX lW₀X lg-evB Lg-TG Lg-TG∞'))
N4=(M(GI,'EvGenTy DnGenTy K₁ RunTy FBABd FbBdAt FbBd')+M(GE,'OkG evSysG G₁ Ld₁ fl₁ D₁ᴷ evK₁ fb-old fb-rd fb-new evS₀ lay-S₀')+
    M(GN,'genFN ldFN genNxt ldNxt liftL liftSL updL flLiftL flNxt genKc ldKc flKc bdS₀ bdLift bdStep bdSupNo bdLiftℕ bdSupℕ bdLev bdLiftL bdNxt bdKc no-swap₁')+
    M(GK,'XG Hs0-ev Hs-ev layer-rts rts-head Br ΩX-head out₂-kept evB-head Hs-head hΩ≢hs not-dnC')+
    M(GC,'lay≡ wd≡ DS σ σ⁻ nzc nzc⁻ nz₁c nz₁c⁻ τ ρ τ-nμ τ-nκ ρ-nc₂ Ωd-κH'))
show('无条件闭项 TG (KG = KD dnG dnL₀; 层号是后继的站经一般折叠求值, 其余截断版)',[
  (1,'定义',Def1+Def1t+IfD+[(If,'FoldAllK'),(If,'FoldTower'),(If,'FoldLimK')]+N1),
  (2,'折叠 (塔, 截断版, 级顶读回, 一般折叠, 读回, 每种类结构的实例, 下降, 闭项, FGH)',GFr+TowD+TowL+InstD+TopD+UD+N2),
  (3,'证书',TowC+TowCL+InstC+TopC+UC+N3),
  (4,'律/形状/实验/互译',L4+N4)])
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('== 各文件代码行 (agda 块非空非注释)')
for m in ['GenFoldIf','GenFoldTree','GenFoldRd','GenFoldRun','GenFoldInst','GenFoldEv','GenFoldK','GenFoldCmp','GenFold']:
    p=os.path.join(R,'probes','OCF','Align',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
