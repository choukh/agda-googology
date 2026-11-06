# -*- coding: utf-8 -*-
# LvKt 一路的分层行数 (切片口径, 同 lvtop/locslice_lvtop.py: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译一个导入 OCF.Align.LvKt 的模块, 再 python3 locslice_lvkt.py <H> [-v].
# 每层: 累计闭包里 LvKt* 模块的行 (本路新增) | 闭包全部树侧行 (含依赖) | 记号模块行.
# 切片看不见模块应用的实参与模块参数: TrK = Tower (CovFK …) (foldFinK …) φ₁ …, TrKL = TrK.Lim …, FT = FullK …,
# 以及 FinK 模块内的定义, 都手工列为根 (实参 foldFinK, foldωK, covSK, covLK, φ₁; 塔的模块内定义 B, rts, Hs, inc, Bᴧ, ΛB, cum, Λ∞, …).
# LvTop 的实例 (outF, outΩ, Cvt, toS) 与 LvRd 的 GF 同 locslice_lvtop.py 列为根.
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
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'LvKt'))
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
Co=A+'LvKtCode'; If=A+'LvKtIf'; Tw=A+'LvKtTower'; In=A+'LvKtInst'; Va=A+'LvKtVal'; Te=A+'LvKtTest'
Fo=A+'LvRdFold'; RIf=A+'LvRdIf'; Wo=A+'LvRdWorld'; Pk=A+'LvRdPkg'; Em=A+'LvRdEmb'; TI=A+'LvTopInst'
GFr=[(Fo,'fold'),(Fo,'ch'),(Fo,'chain')]
Def1=[(Co,'RC'),(Co,'CdK'),(Co,'vB'),(Co,'tB'),(Co,'Code'),(Co,'tgt'),(Co,'cdS₀'),(Co,'cdStep'),(Co,'cdSup'),(Co,'cdLev'),(Co,'vA'),(Co,'tA'),
      (If,'CodeK'),(If,'WbK'),(If,'LgWbK'),(If,'FoldAtK'),(If,'FN'),(If,'nxt'),(If,'cdNxt'),(If,'Kc'),(If,'ckc'),(If,'KΛc'),(If,'ckΛ'),(If,'emb'),(If,'injL'),(If,'ιΛ')]
Def1t=[(RIf,'Cd'),(RIf,'Pc'),(RIf,'Wld'),(Wo,'raise'),(RIf,'RdC'),(Pk,'NdI'),(Em,'Emb')]
TowD=[(Co,'top'),(Tw,'w₀K'),(Tw,'rtTop'),(Tw,'HTop'),(Tw,'B'),(Tw,'rts'),(Tw,'Hs'),(Tw,'inc'),(Tw,'Bᴧ'),(Tw,'ΛB'),(Tw,'cum'),(Tw,'Λ∞'),(Tw,'TΛ∞'),(Tw,'fghΛ∞')]
TowL=[(Tw,'rtω'),(Tw,'Hω'),(Tw,'Λ∞ω'),(Tw,'TΛ∞ω'),(Tw,'fghΛ∞ω')]
TowC=[(Tw,'lw₀K'),(Tw,'lrtTop'),(Tw,'lgHTop'),(Tw,'Lg-emb'),(Tw,'Lg-injL'),(Tw,'Lg-ιΛ'),(Tw,'lB'),(Tw,'cB'),(Tw,'lrts'),(Tw,'lHs'),(Tw,'linc'),(Tw,'lBᴧ'),(Tw,'lΛB'),(Tw,'lcum'),(Tw,'lΛ∞'),(Tw,'Lg-TΛ∞')]
TowCL=[(Tw,'lHω'),(Tw,'lΛ∞ω'),(Tw,'Lg-TΛ∞ω')]
InstD=[(In,'finK'),(In,'levFinK'),(In,'eFK'),(In,'tpK'),(In,'ι-fin'),(In,'CovFK'),(In,'rtFK'),(In,'HFK'),(In,'foldFinK'),(In,'CovΩK'),(In,'toGK'),(In,'ofGK'),(In,'foldωK'),
       (TI,'outF'),(TI,'outΩ'),(TI,'cvt'),(TI,'toS'),(In,'φ₁'),(In,'covSK'),(In,'B-finK'),(In,'Bᴧ-fin'),(In,'covLK'),(In,'Tkt'),(In,'fghKt'),(In,'Tkt∞')]
InstC=[(In,'lg-tpK'),(In,'lg-finK'),(In,'lrtFK'),(In,'lgHFK'),(In,'lg-ofGK'),(TI,'loutF'),(TI,'loutΩ'),(TI,'Lg-cvt'),(TI,'cvt-⊲'),(TI,'lg-toS'),(In,'Lg-Tkt'),(In,'Lg-Tkt∞')]
Lay4=[(Co,'≟RC'),(Co,'vB-prop'),(Co,'code-≟'),(Co,'pB'),(Co,'top-tgt'),(Tw,'emb-⊲'),(Tw,'injL-⊲'),(Tw,'B-suc'),(Tw,'B-fst'),(Tw,'r0'),(Tw,'B1'),(Tw,'lB1'),(Tw,'r1'),(Tw,'B2'),(Tw,'lB2'),
      (In,'ckt1'),(In,'foldFinKt1'),(In,'foldωKt1'),(In,'foldFinKc1'),(In,'foldωKc1'),(In,'kfin2'),(In,'kωK'),(In,'covωK'),(In,'rt-fin2'),(In,'H-fin2'),(In,'H-ωK'),
      (Va,'two-B1'),(Va,'two-B2'),(Va,'two-H0'),(Va,'two-H1'),(Va,'Bᴧ-fst'),(Va,'cum-strict'),(Va,'val-cum'),(Va,'val-cum<'),(Va,'lim-fst'),(Va,'val-lim'),
      (Va,'foldTrivK'),(Va,'Ttriv'),(Va,'Lg-Ttriv'),(Va,'triv-Hs'),(Va,'triv-B1'),
      (Te,'t-Hs0'),(Te,'t-Hs1'),(Te,'t-Hs2'),(Te,'t-new'),(Te,'t-new-ne0'),(Te,'t-kfin2'),(Te,'ncΩ-fin'),(Te,'t-cells'),(Te,'no-covF₁'),(Te,'no-covΩ₁')]
show('截断版闭项 Tkt (有限站 + 对角 + 极限站, 回灌常数 1)',[
  (1,'定义 (码, 世界, 接口, 种类结构的塔; LvRd 的码世界与读回包类型)',Def1+Def1t),
  (2,'折叠 (塔, 极限站, 实例, 闭项, FGH)',GFr+TowD+TowL+InstD),
  (3,'证书',TowC+TowCL+InstC),
  (4,'律/形状/值/测试',Lay4)])
show('条件版闭项 FullK.TΛ∞ω (前提 FA : FoldTower, FL : FoldLimK; 回灌整个读回)',[
  (1,'定义',Def1+[(If,'FoldAllK'),(If,'FoldTower'),(If,'FoldLimK')]),
  (2,'折叠 (塔, 对角, 极限站; 每站一切码上的折叠是前提, 不计)',TowD+TowL),
  (3,'证书',TowC+TowCL),
  (4,'',None)])
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('== 各文件代码行 (agda 块非空非注释)')
for m in ['LvKtCode','LvKtIf','LvKtTower','LvKtInst','LvKtVal','LvKtTest','LvKt']:
    p=os.path.join(R,'probes','OCF','Align',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
