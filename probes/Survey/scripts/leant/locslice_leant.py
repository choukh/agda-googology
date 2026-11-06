# -*- coding: utf-8 -*-
# LeanT 一路的分层行数 (口径同 newtwr/locslice_newtwr.py: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Lean.LeanTCmp 与 OCF.Lean.LeanTFb, 再
#   python3 locslice_leant.py <H> [-v]
# 基础函数 (chunk, closure, lines, find, NOT) 取 locslice.py 的前半段 (到 B4= 之前).
# 输出: (1) 重写后的闭项 TΛ′ 的四层; (2) 同一机器上原闭项 FabLFReGen.TΛ 的前 3 层 (根同 fabloc, 对照 1042);
#       (3) 参数化折叠的实例 (LeanTFb) 另计; (4) 逐文件代码行.
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
    return ', '.join('%s %d'%kv for kv in c.most_common(40))
V='-v' in sys.argv

# (1) 重写
Ln='OCF.Lean.'
L1=(M(Ln,'LeanTBase','KS HB _⊲[_]_ LgB step sup up ι _⊞_ S⊥')+
    M(Ln,'LeanTLv','LH Lv FL SL νL node ofHB Ω̂ tw Λ')+
    M(Ln,'LeanTTree','StH NZ NZ₁ AccY DG₊ D Vs Vc ZK BotK Tg Df St Ig Fb'))
# 第 2 层: 闭项与 FGH 的闭包 (折叠经链接到达; 模块应用的实参经根块的 open 到达). 折叠各函数手工列为根, 防切片漏看模块应用.
L2=(M(Ln,'LeanT','bkL Λ′ one⊲ Act ΨΩ TΛ′ iter FGH fghΛ′')+
    M(Ln,'LeanTFold','LW ω⋅ tg↑ τ₀ τ₁ zeroD _⨾ᴰ_ nlᴰ _⊕⟨_⟩_ cv Stp Ig↾ kk Bu Rk rkS rkT Cl₁ ClA Run Rpt RunNi Ai Chn RKi BNi RunC RKc RKk κc₁ κΔ₁ RKa κcF κΔA')+
    M(Ln,'LeanTTree','S→⊲ Kup Sk NZ-S nz⊲ NZ₁-S accC accᴸ zkS zΩ outC inC outS inS drp pt sum toD₀ Ωd Pre mkOf Int nbA rd₁ rdp₁ drp₁ ≤rf ≤tr'))
L3=(M(Ln,'LeanT','lΛ′ Lg-TΛ′')+M(Ln,'LeanTLv','Lg-Λ Lg-tw tw-st Lg-Ω̂ Ω̂-⊲')+
    M(Ln,'LeanTTree','sum-fst Lg-sum Lg-pt rd₁-fst Lg-rd₁ Lg-rdp₁')+M(Ln,'LeanTBase','lgB⊲ cmpB Lg-⊞ Lg-up Lg-ι'))
L4=M(Ln,'LeanT','Old old-up old-⊞ old-⊲ old-Λ′ old-target')
labs=['定义','+折叠 (读回, 一般折叠, 层, 闭项, FGH)','+证书','+形状定理']
print('== 重写: 闭项 TΛ′ (OCF.Lean.LeanT)')
acc=set(); P={}
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3,L4]),1):
    acc=acc|C(roots); P[i]=set(acc)
    print('  层%d %s: 树侧 %d | 记号模块 %d'%(i,lab,tot(acc),note(acc)))
    if V: print('      ',by_mod(acc,Ln))
print('  层3 逐模块:',by_mod(P[3],Ln))
bad=[n for n in P[3] if not n[0].startswith(Ln)]
print('  层3 闭包里 OCF.Lean 之外的仓库模块块数:',len(bad), sorted({n[0] for n in bad}))

# 回灌部分 (新种类的 rd₁ 回灌与旧种类的级回灌): 按 LeanT §3 的形状定理, TΛ′ 的计算不执行它们 (判断)
FB=(M(Ln,'LeanTFold','Cl₁ κc₁ κΔ₁ ClA κcF κΔA')+
    M(Ln,'LeanTTree','Fb BotK nbA nbA-mono nbA-fst Lg-nbA rd₁ rdp₁ rd₁-fst Lg-rd₁ Lg-rdp₁ drp₁'))
fbset=set(x for m,n in FB for x in find(m,n))
print('  层3 里回灌专用的块 (不含 RKc/RKa 的回灌行, 不含 St 的 z, z₁ 字段): %d 行; 其余 %d 行'%(sum(lines(n) for n in fbset), tot(P[3])-sum(lines(n) for n in fbset)))
for m,n in FB: print('     ',n,sum(lines(x) for x in find(m,n)))

# (2) 原闭项 (同 fabloc/loc_fab.py 的根)
A='OCF.Align.'
O1=(M(A,'GenFoldIf','StH NZ NZ₁ AccY DG₊ D Vs Vc ZK DK TopG FBA GenK LgDn FbLgAt FbLg Tg Df St Ig LW')+
    M(A,'HtTowerTy','KS S₀ HB _⊲[_]_ LgB step sup Lev up ι _⊞_')+M(A,'NewTwrIf','CollK'))
O2=(M(A,'FabLFReGen','top⊥ LvΩ topLv w₀Lv frE⊥ GL collL TΛ ordL fghΛ')+
    M(A,'NewTwrColl','Act Y₀ W₁ ΔΩ ΨΩ Tψ one⊞ collG')+
    M(A,'GenFoldTree','S→⊲ Kup Sk NZ-S nz⊲ nz₁→nz NZ₁-S zkS zΩ outC inC outS inS drp pt sum toD₀ Ωd Pre mkOf Int topStepG ≤rf ≤tr')+
    M(A,'GenFoldRd','nbA lgW≤ rd₁ rdp₁ drp₁')+
    M(A,'GenFoldRun','ω⋅ tg↑ τ₀ τ₁ zeroD _⨾ᴰ_ nlᴰ _⊕⟨_⟩_ cv Stp Ig↾ kk Bu Rk rkS rkT Cl₁ ClA Run Rpt RunNi Ai BNi Chn RKi RunC RKc RKk κc₁ κΔ₁ RKa κcA κΔA'))
O3=(M(A,'FabLFReGen','ld⊥ ldLv lw₀Lv frE⊥-⊲ frE⊥-lg LdL flL Lg-TΛ')+
    M(A,'NewTwrColl','lW₁ Lg-Tψ')+
    M(A,'GenFoldTree','accL accC accᴸ sum-fst Lg-sum Lg-pt')+
    M(A,'GenFoldRd','nbA-mono nbA-fst Lg-nbA rd₁-fst Lg-rd₁ Lg-rdp₁'))
print('== 原闭项 TΛ (OCF.Align.FabLFReGen), 同一台切片机')
acc=set()
for i,roots in enumerate([O1,O2,O3],1):
    acc=acc|C(roots)
    print('  层%d: 树侧 %d | 记号模块 %d'%(i,tot(acc),note(acc)))
print('  层3 逐模块:',by_mod(acc,A))

# (3) 参数化折叠的实例 (不进 TΛ′ 的切片)
F3=C(M(Ln,'LeanTFb','FBA fromFBA genFoldFb KLv fromKLv kindLvFb'))
print('== 级回灌参数的两个实例 (LeanTFb), 闭包里不在 TΛ′ 层3 的部分: %d 行'%sum(lines(n) for n in F3-P[3]))
if V: print('      ',by_mod(F3-P[3],Ln))
fbrows=[(m,n) for (m,n) in [(Ln+'LeanTTree','Fb'),(Ln+'LeanTFold','κcF'),(Ln+'LeanTFold','RKa'),(Ln+'LeanTFold','ClA'),(Ln+'LeanTFold','κΔA')]]
print('  折叠里与级回灌有关的块:',', '.join('%s %d'%(n,sum(lines(x) for x in find(m,n))) for m,n in fbrows))
orow=[(A+'GenFoldIf','FBA'),(A+'GenFoldIf','FbLgAt'),(A+'GenFoldIf','FbLg'),(A+'GenFoldRun','κcA'),(A+'GenFoldRun','RKa'),(A+'GenFoldRun','ClA'),(A+'GenFoldRun','κΔA')]
print('  原折叠的对应块:',', '.join('%s %d'%(n,sum(lines(x) for x in find(m,n))) for m,n in orow))

# (4) 逐文件代码行
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('== 各文件代码行 (agda 块非空非注释 / 全文)')
for m in ['LeanTBase','LeanTLv','LeanTTree','LeanTFold','LeanT','LeanTFb','LeanTCmp']:
    p=os.path.join(R,'probes','OCF','Lean',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
