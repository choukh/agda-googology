# -*- coding: utf-8 -*-
# LvTop 一路的分层行数 (切片口径, 同 lvrd/locslice_lvrd.py: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Align.LvTop, 再 python3 locslice_lvtop.py <H> [-v].
# 每层: 累计闭包里 LvTop* 模块的行 (本路新增) | 闭包全部树侧行 (含依赖) | 记号模块行.
# 切片看不见模块应用的实参与模块参数: Tr = Tower CovF foldFin …, TrL = Tr.Lim CovΩ foldω covL,
# FullΛ = Full F σ₀ … 都是模块应用, 所以把实参 (foldFin, foldω, covL, covS1, B-fin, σ₀) 与
# 塔的模块内定义 (B, Hs, rts, U, slotω, Wω, Hω, cum, …) 手工列为根; LvRd 的 GF 同 locslice_lvrd.py 列 fold/ch/chain.
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
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'LvTop'))
def tree(P): return sum(lines(n) for n in P if n[0] not in NOT)
def note(P): return sum(lines(n) for n in P if n[0] in NOT)
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
If=A+'LvTopIf'; Tw=A+'LvTopTower'; In=A+'LvTopInst'; Va=A+'LvTopVal'; Te=A+'LvTopTest'
Fo=A+'LvRdFold'; RIf=A+'LvRdIf'; Wo=A+'LvRdWorld'; Pk=A+'LvRdPkg'; Em=A+'LvRdEmb'; Wk=A+'LvRdWk'
GFr=[(Fo,'fold'),(Fo,'ch'),(Fo,'chain')]
TowD=[(Tw,'top'),(Tw,'w₀'),(Tw,'tpL'),(Tw,'B'),(Tw,'Hs'),(Tw,'rts'),(Tw,'σs'),(Tw,'psum≡B'),(Tw,'Bω'),(Tw,'rtP'),(Tw,'ιP'),(Tw,'U'),(Tw,'slotω'),(Tw,'Wω'),(Tw,'cum'),(Tw,'Λ∞'),(Tw,'TΛ∞'),(Tw,'fghΛ∞')]
TowL=[(Tw,'Hω'),(Tw,'Λ∞ω'),(Tw,'TΛ∞ω'),(Tw,'fghΛ∞ω')]
TowC=[(Tw,'lw₀'),(Tw,'lg-tpL'),(Tw,'lB'),(Tw,'cB'),(Tw,'lHs'),(Tw,'lrts'),(Tw,'lσs'),(Tw,'lBω'),(Tw,'lrtP'),(Tw,'lU'),(Tw,'lslotω'),(Tw,'lWω'),(Tw,'lcum'),(Tw,'lΛ∞'),(Tw,'Lg-TΛ∞')]
TowCL=[(Tw,'lHω'),(Tw,'lΛ∞ω'),(Tw,'Lg-TΛ∞ω')]
InstD=[(In,'foldFin'),(In,'foldω'),(In,'rtF'),(In,'HF'),(In,'outF'),(In,'outΩ'),(In,'toG'),(In,'ofG'),(In,'cvt'),(In,'eF'),(In,'levFin'),(In,'toS'),
       (In,'one₀'),(In,'covS1'),(In,'B-fin'),(In,'covL'),(In,'Ttr'),(In,'fghTr'),(In,'Ttr∞')]
InstC=[(In,'lrtF'),(In,'lgHF'),(In,'loutF'),(In,'loutΩ'),(In,'lg-ofG'),(In,'Lg-cvt'),(In,'cvt-⊲'),(In,'lg-toS'),(In,'Lg-Ttr'),(In,'Lg-Ttr∞')]
show('截断版闭项 Ttr (有限站 + 对角 + 极限站, 读法常数 1)',[
  (1,'定义 (码, 世界, 接口, LvRd 的码世界与读回包类型)',[(If,'Cod'),(If,'Wb'),(If,'LgWb'),(If,'FoldAt'),(RIf,'Cd'),(RIf,'Pc'),(RIf,'Wld'),(Wo,'raise'),(RIf,'RdC'),(Pk,'NdI'),(Em,'Emb')]),
  (2,'折叠 (塔, 极限站, 实例, 闭项, FGH)',GFr+TowD+TowL+InstD),
  (3,'证书',TowC+TowCL+InstC),
  (4,'律/形状/值/测试',[(Tw,'κ'),(Tw,'κ-tgt'),(Tw,'B-fst'),(Tw,'topP'),(Tw,'stageω'),(Tw,'stageω-tgt'),(Tw,'stageω-coh'),(In,'foldTr'),
     (Va,'cum-strict'),(Va,'val-cum'),(Va,'val-cum<'),(Va,'lim-fst'),(Va,'val-lim'),(Va,'tr-H0'),(Va,'foldTriv'),(Va,'triv-Hs'),
     (Te,'t-head'),(Te,'t-br0'),(Te,'t-br5'),(Te,'t-H1'),(Va,'Kt'),(Va,'KΛ'),(Va,'Kt1')])])
show('全塔版闭项 FullΛ.TΛ∞ (条件: F : FoldAll; 读法 σ₀)',[
  (1,'定义',[(If,'Cod'),(If,'Wb'),(If,'LgWb'),(If,'FoldAt'),(If,'FoldAll')]),
  (2,'折叠 (塔与对角; 一切码上的折叠是前提, 不计)',TowD+[(Wk,'σ₀')]),
  (3,'证书',TowC+[(Wk,'lσ₀')]),
  (4,'',None)])
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('== 各文件代码行 (agda 块非空非注释)')
for m in ['LvTopIf','LvTopTower','LvTopInst','LvTopVal','LvTopTest','LvTop']:
    p=os.path.join(R,'probes','OCF','Align',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
