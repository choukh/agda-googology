# -*- coding: utf-8 -*-
# 同一站 ψ₀(Ω_Ω): 把 TLRule 加进 locslice_station 的比较. 用法: 用 agda --html 编译 TLRuleAccept, NoCumAcceptOmega, Label, 再 python3 locslice_tlrule.py <H>.
import os,sys,io,collections
here=os.path.dirname(os.path.abspath(__file__))
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
A='OCF.Align.'
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def T(par): return sum(lines(n) for n in par if n[0] not in NOT)
ref=C([(A+'Label','BTBO-label')])
D=C([(A+'TLRuleDiag','TopΣ'),(A+'TLRuleSum','Top'),(A+'TLRuleSum','ord')])
Va=C([(A+'TLRuleAccept','TΣ≈'),(A+'TLRuleAccept','T≈')])|D|ref
print('TLRule 定义(含合法性)',T(D),'加序数值验收(含参照)',T(Va),'共用参照',T(ref))
