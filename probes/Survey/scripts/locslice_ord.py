# -*- coding: utf-8 -*-
# 四层行数表 EBO 列, 口径: 最接近最终形态的路线 (不累加, 证书与阶段无关, LadderOrd).
# 用法: 用 agda --html 编译 LadderOrdClosed, OrdLabAccept, OrdLabReadTop, EmbVVInstO2, 再 python3 locslice_ord.py <H>.
# 复用 locslice.py 的切片函数 (取到 "B4=" 之前).
import os,sys,io,collections,re
here=os.path.dirname(os.path.abspath(__file__))
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
BASE={'OCF.BTBO','OCF.Align.Level','OCF.Align.NoCumsum','OCF.Align.Uniform','OCF.Align.Label','OCF.Align.Standard','OCF.Align.StandardOmega','OCF.Align.SystemOmega','OCF.Align.EBO','OCF.Align.Correspond','OCF.Align.Closure','OCF.Align.Bachmann','OCF.Align.Diagonal','OCF.Align.Finite','OCF.Align.Translate'}
A='OCF.Align.'
def RT(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def tot(par,minus=()):
    ms=set()
    for p in minus: ms|=p
    q=[n for n in par if n not in ms and n[0] not in BASE]
    t=collections.Counter()
    for n in q: t[n[0].replace(A,'')]+=lines(n)
    return sum(t.values()),t
L1=RT([(A+'LadderOrdTree','Q₊'),('OCF.Free.Force','Goodᴺ'),(A+'LadderOrdBase','HtB'),(A+'LadderOrdPos','Code')])
L2=RT([(A+'LadderOrdTree','Tᵠ'),(A+'LadderOrdTree','ψᵠ'),(A+'LadderOrdTree','ψ̄ᵠ'),(A+'LadderOrdTree','Ω̇'),('OCF.Free.Force','forceᴺ'),('OCF.Free.Force','forceᴺ-HS'),('OCF.Free.Level','FGH')])
L3=RT([(A+'LadderOrdMain','GᴺTᵠ'),(A+'LadderOrdPos','HB'),(A+'LadderOrdCert','Gᵖ'),(A+'LadderOrdClosed','Tᶜ')])
L4=RT([(A+'OrdLabAccept','ord-top₂'),(A+'OrdLabAccept','ord-top²'),(A+'OrdLabReadTop','label-Tᴸ'),(A+'OrdLabReadTop','same-M₂')])
L5=RT([(A+'EmbVVInstO2','vv-ω²')])
c1,_=tot(L1); c2,t2=tot(L1|L2); c3,t3=tot(L1|L2|L3); c4,t4=tot(L1|L2|L3|L4); c5,t5=tot(L1|L2|L3|L4|L5)
print('L1',c1); print('L2',c2); print('L3',c3,'not in L3 notation',sum(1 for n in (L1|L2|L3) if n[0] in NOT))
print('L4',c4); print('L5 with EmbVV',c5)
def grp(t):
    g=collections.Counter()
    for k,v in t.items():
        k2='clone-OrdLabZ/LadderLabZ' if re.match(r'(OrdLabZ|LadderLabZ)',k) else ('clone-EmbVVOZ/LZ/B' if re.match(r'EmbVV(OZ|LZ|B[A-Z])',k) else ('OCF.Free' if k.startswith('OCF.Free') else 'other'))
        g[k2]+=v
    return dict(g)
print('L3 groups',grp(t3)); print('L4 groups',grp(t4)); print('L5 groups',grp(t5))
print('L3 top',t3.most_common(8))
