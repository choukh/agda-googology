# -*- coding: utf-8 -*-
# LeanFb 一路的分层行数 (口径同 leant/locslice_leant.py: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Lean.LeanFbShape (它导入 LeanFbTm 与全部依赖), 再
#   python3 locslice_leanfb.py <H> [-v]
# 输出: (1) 闭项 TF 的四层; (2) 第 3 层按件分: 基础 (LeanT*), 站 (LeanFbSt), 一起升 (LeanFbSlot), 按级读回 (LeanFbRd), 其他 (LeanFbIf, LeanFbTm);
#       (3) 同一台切片机重算 TΛ′ 的第 3 层 (对照 745); (4) 逐文件代码行.
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
L1=(M(Ln,'LeanTBase','KS HB _⊲[_]_ LgB step sup up ι _⊞_ S⊥')+
    M(Ln,'LeanTLv','LH Lv FL SL νL node ofHB Ω̂ tw')+
    M(Ln,'LeanTTree','StH NZ NZ₁ AccY DG₊ D Vs Vc ZK BotK Tg Df St Ig Fb')+
    M(Ln,'LeanFbIf','Up LvRd Feed Plan')+
    M(Ln,'LeanFbSt','st FS SLs νS ιS tws Λs ΛF WS upd bumpH')+
    M(Ln,'LeanFbSlot','num eqN cast bump addN addSt PosN PosSt kN kSt uncast coN coSt Mem MemSt')+
    M(Ln,'LeanFbRd','AK0'))
L2=(M(Ln,'LeanFbTm','bkS feed0 feed1 feedH planK plan toFb fb Act ΨF TF fghF')+
    M(Ln,'LeanT','iter FGH')+M(Ln,'LeanTFold',FOLD)+M(Ln,'LeanTTree',TREE2)+
    M(Ln,'LeanFbSt','headUp')+M(Ln,'LeanFbSlot','slotUp memS memN memSt')+
    M(Ln,'LeanFbRd','newAK oldAK supAK find0 findSt rdX rdpX R0 RX'))
L3=(M(Ln,'LeanFbTm','Lg-TF')+M(Ln,'LeanFbSt','lΛF oneF Lg-tws tws-st upd-R upd-Q upd-at')+
    M(Ln,'LeanFbSlot','eqN-num bump-fst addN≤ addSt≤ Lg-cast Lg-bump Lg-addN Lg-addSt top-new top-addN top-addSt')+
    M(Ln,'LeanFbRd','rdX-fst Lg-rdX Lg-rdpX')+
    M(Ln,'LeanTTree','sum-fst Lg-sum Lg-pt rd₁-fst Lg-rd₁ Lg-rdp₁')+M(Ln,'LeanTBase','lgB⊲ cmpB Lg-⊞ Lg-up Lg-ι'))
L4=M(Ln,'LeanFbShape','IsL tw-shape st-shape find-lΩ heads-fed stage-head exec-head Dir nav exec-TF0 exec-TF1 exec-TF2 cell0 cellS raise0 self read0 read1 cp1 cp1-coord cp1-fed cp1-moves head1-moves lz1 bk-merge lv2 lv2-lossy cp2 cp2-coord cp2-lossy cp2-not-moved deep-lossy')
labs=['定义','+折叠 (读回, 一般折叠, 计划, 闭项, FGH)','+证书','+形状定理']
print('== 闭项 TF (OCF.Lean.LeanFbTm)')
acc=set(); P={}
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3,L4]),1):
    acc=acc|C(roots); P[i]=set(acc)
    print('  层%d %s: 树侧 %d | 记号模块 %d'%(i,lab,tot(acc),note(acc)))
    if V: print('      ',', '.join('%s %d'%kv for kv in by_mod(acc,Ln).most_common(40)))
c=by_mod(P[3],Ln)
print('  层3 逐模块:',', '.join('%s %d'%kv for kv in c.most_common(40)))
base=sum(v for k,v in c.items() if k.startswith('LeanT'))
print('  层3 按件: 基础 (LeanT*) %d, 站 (LeanFbSt) %d, 一起升 (LeanFbSlot) %d, 按级读回 (LeanFbRd) %d, 其他 (LeanFbIf %d + LeanFbTm %d) %d'%(
    base,c['LeanFbSt'],c['LeanFbSlot'],c['LeanFbRd'],c['LeanFbIf'],c['LeanFbTm'],c['LeanFbIf']+c['LeanFbTm']))
bad=[n for n in P[3] if not n[0].startswith(Ln)]
print('  层3 闭包里 OCF.Lean 之外的仓库模块块数:',len(bad), sorted({n[0] for n in bad}))

# (3) TΛ′ 的第 3 层, 同一台切片机 (根同 leant/locslice_leant.py)
T1=(M(Ln,'LeanTBase','KS HB _⊲[_]_ LgB step sup up ι _⊞_ S⊥')+M(Ln,'LeanTLv','LH Lv FL SL νL node ofHB Ω̂ tw Λ')+
    M(Ln,'LeanTTree','StH NZ NZ₁ AccY DG₊ D Vs Vc ZK BotK Tg Df St Ig Fb'))
T2=(M(Ln,'LeanT','bkL Λ′ one⊲ Act ΨΩ TΛ′ iter FGH fghΛ′')+M(Ln,'LeanTFold',FOLD)+M(Ln,'LeanTTree',TREE2))
T3=(M(Ln,'LeanT','lΛ′ Lg-TΛ′')+M(Ln,'LeanTLv','Lg-Λ Lg-tw tw-st Lg-Ω̂ Ω̂-⊲')+
    M(Ln,'LeanTTree','sum-fst Lg-sum Lg-pt rd₁-fst Lg-rd₁ Lg-rdp₁')+M(Ln,'LeanTBase','lgB⊲ cmpB Lg-⊞ Lg-up Lg-ι'))
Tset=C(T1)|C(T2)|C(T3)
print('== 对照 TΛ′ 第 3 层: %d; TΛ′ 与 TF 共有 %d, 只在 TΛ′ %d, 只在 TF %d'%(tot(Tset),tot(Tset&P[3]),tot(Tset-P[3]),tot(P[3]-Tset)))
if V:
    print('   只在 TΛ′:',', '.join('%s.%s'%(n[0].replace(Ln,''),getattr(n,'name','')) for n in []))

# (4) 逐文件代码行
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('== 各文件代码行 (agda 块非空非注释 / 全文)')
for m in ['LeanFbIf','LeanFbSt','LeanFbSlot','LeanFbRd','LeanFbTm','LeanFbShape','LeanFbTest','LeanFb']:
    p=os.path.join(R,'probes','OCF','Lean',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st_=l.strip()
        if st_.startswith('```'): inc=st_.startswith('```agda'); continue
        if inc and st_ and not st_.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
