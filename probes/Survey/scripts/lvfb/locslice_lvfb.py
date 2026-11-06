# -*- coding: utf-8 -*-
# LvFb 一路的分层行数 (切片口径, 同 htfeed/locslice_four.py: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Align.LvFb, 再 python3 locslice_lvfb.py <H>.
# 每层: 累计闭包里 LvFb* 模块的行 (本路新增) | 闭包全部树侧行 (含依赖) | 记号模块行.
# 注意: 切片看不见模块应用 (module X = M args), 新增行可能少算; 另列各文件代码行总数作上界.
import os,sys,io
here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
A='OCF.Align.'
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'LvFb'))
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
Cd=A+'LvFbCode'; Fc=A+'LvFbFac'; St=A+'LvFbSet'; Fd=A+'LvFbFold'
show('W2 码世界',[(1,'定义 (码, 世界, 更新)',[(Cd,'Code'),(Cd,'tgt'),(Cd,'Cmpᶜ'),(Cd,'raiseC')]),
                 (2,'折叠',None),
                 (3,'证书',[(Cd,'legal')]),
                 (4,'值/律',[(Cd,'at'),(Cd,'off'),(Cd,'mono'),(Cd,'slot-at'),(Cd,'cd-tgt'),(Cd,'code-uip'),(Cd,'copy-split'),(Cd,'atω′')])])
show('W1 差树外层界',[(1,'定义 (部分和, 改贴, 差树极限)',[(Fc,'psum'),(Fc,'rl'),(Fc,'U'),(Fc,'Uω')]),
                 (2,'折叠',None),
                 (3,'证书',[(Fc,'Lg-rl'),(Fc,'Lg-U'),(Fc,'lU'),(Fc,'Lg-rlω')]),
                 (4,'律/否定',[(Fc,'fac-lim'),(Fc,'fac-tr'),(Fc,'fac-ps'),(Fc,'copy-lim'),(Fc,'kind-n')])])
show('W3 ≈',[(1,'定义',None),(2,'折叠',None),(3,'证书',None),
                 (4,'律/否定',[(St,'⊲≈'),(St,'≈→¬<'),(St,'resp⊲→ext'),(St,'respLg→ext'),(St,'fe→respLg')])])
show('折叠 LvFbFold (含它用到的 W2)',[(1,'定义',[(Cd,'Code'),(Cd,'Cmpᶜ'),(Cd,'raiseC')]),
                 (2,'折叠',[(Fd,'fold'),(Fd,'T∞c'),(Fd,'fghc'),(Fd,'Vω'),(Fd,'incω')]),
                 (3,'证书',[(Fd,'Lg-T∞c'),(Fd,'lgV'),(Fd,'ch-lg')]),
                 (4,'形状定理',[(Fd,'ωslot-s'),(Fd,'fin-zero'),(Fd,'lv1'),(Fd,'lv2'),(Fd,'slot-s'),(Fd,'monoV')])])
show('对照 FamFoldAll (族世界, 每级一个世界)',[(1,'定义',None),(2,'折叠',[(A+'FamFoldAll','fold'),(A+'FamFoldAll','T∞'),(A+'FamFoldAll','fgh∞')]),(3,'证书',[(A+'FamFoldAll','Lg-T∞')]),(4,'',None)])
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('== 各文件代码行 (agda 块非空非注释)')
for m in ['LvFbSet','LvFbCode','LvFbFac','LvFbFold','LvFb']:
    p=os.path.join(R,'probes','OCF','Align',m+'.lagda.md'); t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
