# -*- coding: utf-8 -*-
# DnFold 一路的分层行数 (根表沿用 kcfold/locslice_kcfold.py, 本文件由它的前半段加 DnFold 的根组成)
# 原 KcFold 注释:
# KcFold 一路的分层行数 (同 lvkt/locslice_lvkt.py 口径: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译一个导入 OCF.Align.DnFold 的模块, 再 python3 locslice_dnfold.py <H> [-v].
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
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'DnFold'))
def newKc(P): return sum(lines(n) for n in P if n[0].startswith(A+'KcFold'))
def tree(P): return sum(lines(n) for n in P if n[0] not in NOT)
def note(P): return sum(lines(n) for n in P if n[0] in NOT)
def show(name,layers):
    acc=set(); print('==',name)
    for i,lab,roots in layers:
        if roots is None: print('  层%d %s: 无新增'%(i,lab)); continue
        acc=acc|C(roots)
        print('  层%d %s: 本路新增 %d | (KcFold %d) | 树侧全部 %d | 记号模块 %d'%(i,lab,new(acc),newKc(acc),tree(acc),note(acc)))
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
DI=A+'DnFoldIf'; DE=A+'DnFoldEv'; DR=A+'DnFoldRd'; DC=A+'DnFoldDc'; DM=A+'DnFoldMu'; DB=A+'DnFoldBr'; DK=A+'DnFoldK'; DO=A+'DnFoldObs'
# 模块应用 KQ = KD dnD dnL₀ 的实参 dnD, dnL₀ 与 Rd a, Br N, EvAt L … 模块内的定义手工列为根 (切片看不见模块应用).
N1=[(DI,'LvH'),(DI,'LyH'),(DI,'DnEv'),(DM,'K1'),(DM,'Oth'),(DM,'Kd1'),(DB,'PE')]
N2=[(DE,'evAt'),(DE,'evD'),(DE,'toDn'),
    (DR,'bdecS₁'),(DR,'Lv'),(DR,'o⋆'),(DR,'eA'),(DR,'eS'),(DR,'eM'),(DR,'iκ'),(DR,'NdW'),(DR,'Wκ'),(DR,'rdW'),(DR,'rdpW'),(DR,'NdT'),(DR,'TrT'),(DR,'Pkg'),
    (DR,'trN'),(DR,'ndi'),(DR,'rdc'),(DR,'ndQ'),(DR,'newN'),(DR,'trK-z'),(DR,'ndS-z'),(DR,'trK-s'),(DR,'ndS-s'),(DR,'ιL'),(DR,'trK-l'),(DR,'ndS-l'),(DR,'ιΩ'),(DR,'trK-Ω'),(DR,'ndΩd'),(DR,'ndS-Ω'),(DR,'pk'),
    (DM,'kd1'),(DM,'μΩ'),(DM,'μ′'),
    (DB,'selP'),(DB,'mapP'),(DB,'liftO'),(DB,'stepPE'),(DB,'eqA'),(DB,'decA'),(DB,'eqH'),(DB,'decH'),(DB,'aN'),(DB,'inΩ'),(DB,'outΩ'),(DB,'FΩ'),(DB,'GΩ'),(DB,'F'),(DB,'G'),
    (DK,'sumH'),(DK,'ev₁'),(DK,'dn₁'),(DK,'dnD'),(DK,'TD'),(DK,'fghD'),(DK,'TD∞')]
N3=[(DE,'lg-evAt'),(DR,'fstW'),(DR,'lgW'),(DR,'lgpW'),(DR,'fstc'),(DR,'lgc'),(DR,'fsQ'),(DR,'lgQ'),(DR,'fsS-z'),(DR,'lgS-z'),(DR,'fsS-s'),(DR,'lgS-s'),(DR,'fsS-l'),(DR,'lgS-l'),
    (DR,'fsΩd'),(DR,'lgΩd'),(DR,'fsS-Ω'),(DR,'lgS-Ω'),
    (DC,'LyH-mono'),(DC,'lgLyH'),(DC,'o1H'),(DC,'e2-of'),
    (DM,'ωW'),(DM,'lωW'),(DM,'eO'),(DM,'basebot'),(DM,'μΩ-⊲'),(DM,'μ-⊲'),(DM,'LgΩ'),(DM,'Lg-μ′'),(DM,'oneΩ'),(DM,'one⊲'),(DB,'laN'),
    (DK,'Lg-sumH'),(DK,'Lg-hlH'),(DK,'Lg-TD'),(DK,'Lg-TD∞')]
N4=[(DI,'DnEvTower'),(DI,'EvSys'),(DI,'DnEvS'),(DI,'EvSysK'),(DI,'DnSq'),(DI,'rdTop'),(DI,'rdCut'),(DI,'FaithRd'),(DI,'Faith0'),(DI,'FaithTower'),(DI,'DiffTkc'),(DI,'RestrK'),(DI,'ExactAdm'),
    (DE,'OkHt'),(DE,'evSysHt'),(DE,'toDnS'),(DE,'ofDnEv'),
    (DC,'dnEvH'),(DC,'dnH'),(DC,'dnHs'),(DC,'R₀'),(DC,'tr-top'),(DC,'tr-cut'),(DC,'X₁H'),(DC,'lX₁H'),(DC,'c₁H'),(DC,'finH₀'),(DC,'ω₀H'),(DC,'lg-finH₀'),(DC,'Lg-ω₀H'),(DC,'finA'),(DC,'lg-finA'),(DC,'ωA'),(DC,'Lg-ωA'),(DC,'aω'),(DC,'laω'),(DC,'one⊲c₁'),(DC,'HD₁'),(DC,'lgHD₁'),(DC,'TH₁'),(DC,'Lg-TH₁'),(DC,'fghH₁'),
    (DK,'Hs0-rd'),(DK,'Hs0-shape'),(DK,'diffD'),(DK,'faith0D'),(DK,'X₀'),(DK,'H1N'),(DK,'Hs1'),(DK,'rd-kept'),(DK,'tr₁'),(DK,'HsSS'),(DK,'IsL'),(DK,'t-keep'),(DK,'t-drop'),(DK,'t-dropω'),
    (DO,'levIdx'),(DO,'lvhIdx'),(DO,'sLH-adm'),(DO,'eqH-self'),(DO,'decH-fin′'),(DO,'eqA-self'),(DO,'decA-fin′')]
show('无条件闭项 TD (KQ = KD dnD dnL₀; 第 0 站恒等, 第 1 站经求值, 其余站截断版)',[
  (1,'定义',Def1+Def1t+IfD+[(If,'FoldAllK'),(If,'FoldTower'),(If,'FoldLimK')]+N1),
  (2,'折叠 (塔, 截断版, 级顶读回, 经求值的下降, 读回包, 层号搬运, 桥, 闭项, FGH)',GFr+TowD+TowL+InstD+TopD+UD+N2),
  (3,'证书',TowC+TowCL+InstC+TopC+UC+N3),
  (4,'律/形状/测试/TH₁/障碍',L4+N4)])
show('闭项 TH₁ (层号在 Ht 的经求值的下降, 不经塔)',[
  (1,'定义',[(DI,'LvH'),(DI,'LyH'),(DI,'DnEv'),(KI,'LvW'),(KI,'DnK')]),
  (2,'折叠 (读回包, 求值, 下降, 闭项, FGH)',[(DE,'evAt'),(DE,'evD'),(DE,'toDn'),(DC,'dnEvH'),(DC,'dnH'),(DC,'dnHs'),(DC,'X₁H'),(DC,'c₁H'),(DC,'aω'),(DC,'HD₁'),(DC,'TH₁'),(DC,'fghH₁')]+[n for n in N2 if n[0]==DR]),
  (3,'证书',[(DE,'lg-evAt'),(DC,'lgLyH'),(DC,'o1H'),(DC,'e2-of'),(DC,'one⊲c₁'),(DC,'lX₁H'),(DC,'laω'),(DC,'lgHD₁'),(DC,'Lg-TH₁')]+[n for n in N3 if n[0]==DR]),
  (4,'',None)])
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('== 各文件代码行 (agda 块非空非注释)')
for m in ['DnFoldIf','DnFoldEv','DnFoldRd','DnFoldDc','DnFoldMu','DnFoldBr','DnFoldK','DnFoldObs','DnFold']:
    p=os.path.join(R,'probes','OCF','Align',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
