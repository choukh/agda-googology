# -*- coding: utf-8 -*-
# KcFold 一路的分层行数 (同 lvkt/locslice_lvkt.py 口径: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译一个导入 OCF.Align.KcFold 的模块, 再 python3 locslice_kcfold.py <H> [-v].
# 每层: 累计闭包里 KcFold* 模块的行 (本路新增) | 闭包全部树侧行 (含依赖) | 记号模块行.
# 另外: KU = KD dn₀ dnL₀ = FullK (foldTower dn₀) (foldLim dnL₀) 1 tt 是模块应用, 实参 (foldTower, foldLim, dn₀, dnL₀) 手工列为根;
# dn₀ 读截断版 TrK.Hs, TrKL.Hω, 所以截断版的塔与实例 (lvkt 脚本的 InstD/InstC) 也列为根.
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
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'KcFold'))
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
KI=A+'KcFoldIf'; KT=A+'KcFoldTop'; KW=A+'KcFoldTower'; KS_=A+'KcFoldTest'
IfD=[(KI,'DnK'),(KI,'DnTower'),(KI,'DnLim')]
TopD=[(KT,'toH'),(KT,'sumι'),(KT,'Ω₀'),(KT,'top'),(KT,'lgTgt'),(KT,'foldTop'),(KT,'foldTower'),(KT,'foldLim')]
TopC=[(KT,'toH-⊲'),(KT,'Lg-toH'),(KT,'Lg-sumι'),(KT,'Lg-hlsum'),(KT,'Lg-Ω₀'),(KT,'Lg-top')]
UD=[(KW,'dn₀'),(KW,'dnL₀'),(KW,'FT₀'),(KW,'FL₀'),(KW,'Tkc'),(KW,'fghKc'),(KW,'Tkc∞')]
UC=[(KW,'Lg-Tkc'),(KW,'Lg-Tkc∞')]
L4=[(KI,'LvW'),(KI,'BDecK'),(KI,'BDecTower'),(KI,'LayK'),(KI,'lyK'),(KI,'WbKW'),(KI,'LgWbKW'),(KI,'FoldAtKW'),(KI,'FoldAllKW'),(KI,'FoldTowerW'),(KI,'FoldLimKW'),(KI,'ForgetK'),(KI,'GrowW'),(KI,'WTower'),
    (KT,'top-above'),(KT,'top-branch'),(KT,'topW'),(KT,'Lg-topW'),(KT,'foldTopW'),
    (KW,'rts-def'),(KW,'Hs-def'),(KW,'X'),(KW,'B-suc-shape'),(KW,'rts-suc'),(KW,'B-new'),(KW,'coord-new'),(KW,'rts-above'),
    (KW,'B1-shape'),(KW,'X₁'),(KW,'comp'),(KW,'s1-above'),(KW,'no-covF1'),(KW,'no-covΩ1'),(KW,'Hs-trunc'),(KW,'Hω-trunc'),
    (KW,'ftW'),(KW,'flW'),(KW,'rtW-def'),(KW,'bdecS₀'),(KW,'ht-coords'),(KW,'s1-sees'),(KW,'s1-sees-lg'),(KW,'wt₀'),(KW,'finA'),(KW,'ωA'),(KW,'aWω'),(KW,'laWω'),(KW,'wtω'),(KW,'wtω-sees'),(A+'KcFoldBdec','bdecT'),(A+'KcFoldBdec','bdecL'),(A+'KcFoldBdec','bdecLv'),
    (KS_,'isΩ'),(KS_,'kidx'),(KS_,'cellL'),(KS_,'rtB₁'),(KS_,'t-cell2'),(KS_,'t-rt-idx')]
show('无条件闭项 Tkc (KU = FullK (foldTower dn₀) (foldLim dnL₀) 1 tt; 下降取截断版输出)',[
  (1,'定义 (码, 世界, 接口, 种类结构的塔, 下降的类型; 截断版的 LvRd 码世界与读回包类型)',Def1+Def1t+IfD+[(If,'FoldAllK'),(If,'FoldTower'),(If,'FoldLimK')]),
  (2,'折叠 (塔, 对角, 极限站, 级顶读回, 由下降给出的折叠, 截断版的下降, 闭项, FGH)',GFr+TowD+TowL+InstD+TopD+UD),
  (3,'证书',TowC+TowCL+InstC+TopC+UC),
  (4,'律/形状/测试/带世界版',L4)])
show('条件版闭项 KD dn dnL . TΛ∞ω (前提只有下降 dn : DnTower, dnL : DnLim)',[
  (1,'定义',Def1+IfD+[(If,'FoldAllK'),(If,'FoldTower'),(If,'FoldLimK')]),
  (2,'折叠 (塔, 对角, 极限站, 级顶读回, 由下降给出的折叠; 下降是前提, 不计)',TowD+TowL+TopD),
  (3,'证书',TowC+TowCL+TopC),
  (4,'',None)])
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('== 各文件代码行 (agda 块非空非注释)')
for m in ['KcFoldIf','KcFoldTop','KcFoldTower','KcFoldTest','KcFoldBdec','KcFold']:
    p=os.path.join(R,'probes','OCF','Align',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
