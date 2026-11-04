# -*- coding: utf-8 -*-
# 第 1, 2 层: 类型定义; 加折叠, 闭项与 FGH. 同口径比较 SumOne, TLRule, CumUp (累加), NoCum/Om1Hn (不累加).
# 用法: 用 agda --html 编译导入 SumOneClosed, SumOneAccept, TLRuleSum, TLRuleDiag, CumUp, NoCumForce, Om1HnMain 的文件, 再 python3 locslice_l12.py <H>.
import os,sys,io,collections
here=os.path.dirname(os.path.abspath(__file__))
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
A='OCF.Align.'
SH={'OCF.BTBO','OCF.Free.Level'}
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def T(par,ex=False): return sum(lines(n) for n in par if n[0] not in NOT and (not ex or n[0] not in SH))
base=[(A+'CumReadCF','A'),(A+'CumReadCF','Lg')]
ROUTES={
 'SumOne (和, 过 Ω+1)':([(A+'SumOneTree','D₊')]+base,[(A+'SumOneClosed','fgh'),(A+'SumOneClosed','ord')]),
 'TLRule (和, 只到 Ω)':([(A+'TLRuleSum','D₊')]+base,[(A+'TLRuleSum','fgh'),(A+'TLRuleDiag','TopΣ')]),
 'CumUp (累加, 一切 Ω·p+a)':([(A+'CumUpW','O₊')]+base,[(A+'CumUpW','Tψ'),(A+'CumUp','TΩ+1'),('OCF.Free.Level','FGH')]),
 'NoCum/Om1Hn (不累加, 一切 Ω·p+a)':([(A+'NoCumW','O₊')]+base,[(A+'NoCumW','Tᴰ'),(A+'NoCumForce','force'),('OCF.Free.Level','FGH')]),
}
for k,(l1,l2) in ROUTES.items():
    P1=C(l1); P2=C(l2)|P1
    print(k,'| 层1',T(P1),'(去共用',T(P1,True),') | 层2',T(P2),'(去共用',T(P2,True),')')
