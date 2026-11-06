# -*- coding: utf-8 -*-
# NegCRw 的行数复核: 在同一份 html 上重跑 CRw 与 X1Up 的切片, 并分出 X1Up 第 3 层里 "CRw 不再证明" 的块.
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Lean.CRwCmp (它导入 CRw, X1Up, PathOut),
#       再 python3 audit_crw.py <H>.
# 口径同 crw/locslice_crw.py 与 x1up/locslice_x1up.py (定义级切片, agda 块非空非注释行); 两者的根表从原脚本读入, 不改原脚本.
import os,sys,io
here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
def roots_of(script):
    t=io.open(os.path.join(here,script),encoding='utf-8').read()
    t=t.split("\nlabs=")[0].split("exec(s)",1)[1]
    g=dict(globals()); exec(t,g); return g
X=roots_of('x1up/locslice_x1up.py')
Cw=roots_of('crw/locslice_crw.py')
def tot(P): return sum(lines(n) for n in P if n[0] not in NOT)
px=set()
for r in [X['L1'],X['L2']('TU2 yU fghU2'),X['L3']('LgB-TU2')]: px|=closure(r)
pc=set()
for r in [Cw['L1'],Cw['L2'],Cw['L3']]: pc|=closure(r)
print('X1Up 第 3 层 (TU2):',tot(px),'| CRw 第 3 层 (TU2):',tot(pc))
A='OCF.Align.'
DROP={'决定正确 (接口字段 correct 与它的证明)':[(A+'PathOutX1',n) for n in 'okΩ okI correct₁'.split()],
      '地板合法 (Lg-topL 及其引理, 叠层地板合法)':[(A+'PathOut',n) for n in 'gt-⊲ Lg-gt Lg-topL'.split()]+
         [(A+'X1UpFold',n) for n in 'Lg-topU Lg-ΣU'.split()]+[(A+'TySupSum',n) for n in 'Lg-topΣ Lg-ΣΩ'.split()]}
tot_drop=0
for k,ms in DROP.items():
    bl=set(x for m,n in ms for x in find(m,n))
    v=sum(lines(n) for n in bl&px); tot_drop+=v
    print('  X1Up 闭包里',k,':',v,'行', '(未找到: %s)'%[n for m,n in ms if not find(m,n)] if any(not find(m,n) for m,n in ms) else '')
print('X1Up 去掉这两项后:',tot(px)-tot_drop)
