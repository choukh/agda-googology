# -*- coding: utf-8 -*-
# GenAbs 的账, 口径同 locslice_htfeed.py (定义级切片, 按到达的块计 agda 非空非注释行). 用法: python3 locslice_genabs.py <H>
import os,sys,io,collections
import os; here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
A='OCF.Align.'
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def T(par): return sum(lines(n) for n in par if n[0] not in NOT)
def bymod(ns,top=20):
    c=collections.Counter()
    for n in ns:
        if n[0] not in NOT: c[n[0].replace('OCF.Align.','').replace('OCF.','')]+=lines(n)
    return ', '.join('%s %d'%(k,v) for k,v in c.most_common(top))
def cmp(label,old,new):
    O=C(old); N=C(new)
    print('== %s: 旧 %d | 新 %d | 共用 %d | 只在旧 %d | 只在新 %d'%(label,T(O),T(N),T(O&N),T(O-N),T(N-O)))
    print('   只在旧:',bymod(O-N)); print('   只在新:',bymod(N-O))
    bad=[n for n in N if n[0] in (A+'MonoPortBridge',A+'SumOneTree',A+'DValCanon',A+'BrwMidZero')]
    print('   新切片里 Bridge/SumOneTree/DValCanon/BrwMidZero 的块:',len(bad))

GG=lambda m:(A+m,'module GG')
cmp('MonoPortZero cong0+chain (含模块别名 GG)', [(A+'MonoPortZero','cong0'),(A+'MonoPortZero','chain'),GG('MonoPortZero')], [(A+'GenAbsHt','cong0'),(A+'GenAbsHt','chain'),GG('GenAbsHt')])
cmp('MonoPort2Zero cong0₂+chain₂ (含 GG)', [(A+'MonoPort2Zero','cong0₂'),(A+'MonoPort2Zero','chain₂'),GG('MonoPort2Zero')], [(A+'GenAbsM2','cong0₂'),(A+'GenAbsM2','chain₂'),GG('GenAbsM2')])
cmp('SumOne 实例: Gen 的 cong0 (不含结构律)', [(A+'DValCanon','cong0')], [(A+'GenAbsCanon','cong0'),(A+'GenAbsSO','σS')])
O=C([(A+'MonoPortZero','cong0'),(A+'MonoPortZero','chain'),GG('MonoPortZero'),(A+'MonoPort2Zero','cong0₂'),(A+'MonoPort2Zero','chain₂'),GG('MonoPort2Zero')])
N=C([(A+'GenAbsHt','cong0'),(A+'GenAbsHt','chain'),GG('GenAbsHt'),(A+'GenAbsM2','cong0₂'),(A+'GenAbsM2','chain₂'),GG('GenAbsM2')])
print('== 合并两处: 旧 %d 新 %d 省 %d'%(T(O),T(N),T(O)-T(N)))
print('   只在旧:',bymod(O-N)); print('   只在新:',bymod(N-O))
for n in N:
    if n[0] in (A+'MonoPortBridge',A+'SumOneTree',A+'DValCanon',A+'BrwMidZero'):
        print('  新切片里:',n[0],chunk(n[0]).chunks[n[1]]['name'],lines(n))
for m in ['GenAbs','GenAbsSig','GenAbsCanon','GenAbsSO','GenAbsHtInst','GenAbsHt','GenAbsHtCmp','GenAbsM2','GenAbsM2Cmp','MonoPort2Zero','MonoPortBridge','MonoPortZero','DValCanon']:
    f=chunk(A+m); print('  文件',m,sum(lines((A+m,i)) for i in range(len(f.chunks))))
