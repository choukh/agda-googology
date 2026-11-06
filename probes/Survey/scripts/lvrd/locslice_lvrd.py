# -*- coding: utf-8 -*-
# LvRd 一路的分层行数 (切片口径, 同 lvfb/locslice_lvfb.py 与 htfeed/locslice_four.py: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Align.LvRd, 再 python3 locslice_lvrd.py <H> [-v].
# 每层: 累计闭包里 LvRd* 模块的行 (本路新增) | 闭包全部树侧行 (含依赖) | 记号模块行.
# 切片看不见模块应用的实参与隐式参数: 本路的模块应用 (FF/FΩ 打开 GF, OG/Ev 打开 At) 都写成 open 形式;
# 另把 GF 的定义手工列为根 (fold, ch, chain), 以免少算.
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
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'LvRd'))
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
If=A+'LvRdIf'; Em=A+'LvRdEmb'; Pk=A+'LvRdPkg'; Wo=A+'LvRdWorld'; Fo=A+'LvRdFold'; Wk=A+'LvRdWk'; Sh=A+'LvRdShape'; Va=A+'LvRdVal'
GFr=[(Fo,'fold'),(Fo,'ch'),(Fo,'chain')]
show('闭项 T∞ω1 (第 ω+1 级折叠, 读 ω 层的槽)',[
  (1,'定义 (码, 世界, 更新, 读回包的类型)',[(If,'Cd'),(If,'Pc'),(If,'Wld'),(Wo,'raise'),(If,'RdC'),(Pk,'NdI'),(Em,'Emb')]),
  (2,'折叠 (含读回包, 下降, 闭项, FGH)',GFr+[(Fo,'T∞ω1'),(Fo,'fghω1'),(Fo,'Hω1'),(Fo,'V∞')]),
  (3,'证书',[(Fo,'Lg-T∞ω1'),(Fo,'lgV∞'),(Fo,'ch-lg')]),
  (4,'律/形状定理/值 (含 ω+1 的包 RdΩ1)',[(Wo,'RaiseI'),(Sh,'ωslot-s'),(Sh,'reads₀'),(Sh,'foldΩ1'),(Sh,'shapeΩ1'),(Sh,'fold-reads'),(Sh,'fin-zero'),(Wk,'wkLaw'),(Wk,'lvShapeδ'),(Wk,'lvlδ'),(Wk,'lvShape₁'),(Wk,'lvl₁'),(Va,'val-strict'),(Va,'val-mono'),(Pk,'RdΩ1'),(Pk,'pkgΩ')])])
show('对照: 只有有限级的对角 T∞F',[(1,'定义',[(If,'Cd'),(If,'Pc'),(If,'Wld'),(Wo,'raise')]),
  (2,'折叠',GFr+[(Fo,'T∞F')]),(3,'证书',[(Fo,'lΛF')]),(4,'',None)])
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('== 各文件代码行 (agda 块非空非注释)')
for m in ['LvRdIf','LvRdEmb','LvRdPkg','LvRdWorld','LvRdFold','LvRdShape','LvRdWk','LvRdVal','LvRd']:
    p=os.path.join(R,'probes','OCF','Align',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
