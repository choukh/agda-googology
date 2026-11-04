# -*- coding: utf-8 -*-
# ψ₀(Ω_{Ω+1}) 这一站, 和形式 (SumOne) 的账. 口径同 ../locslice_tlrule.py: 定义级切片, 计 agda 非空非注释行, 不排除任何层 (记号模块除外).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 SumOneAccept, TLRuleAccept, Om1Cum, Om1Hn, Om1HnAccept, NoCumAcceptOmega, Label, CumVal, 再 python3 locslice_sumone.py <H>.
import os,sys,io,collections
here=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
A='OCF.Align.'
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def T(par): return sum(lines(n) for n in par if n[0] not in NOT)
def bymod(ns,top=14):
    c=collections.Counter()
    for n in ns:
        if n[0] not in NOT: c[n[0].replace('OCF.Align.','').replace('OCF.','')]+=lines(n)
    return ', '.join('%s %d'%(k,v) for k,v in c.most_common(top))
LB=(A+'Label','BTBO-label')
routes=[
 # 名字, 定义(含合法性)根, 第 3 层根 (证书), 第 4 层根
 ('SumOne, Ω (T₀≈)',[(A+'SumOneFold','T₀'),(A+'SumOneClosed','ω⋅')],[(A+'SumOneFold','Lg-T₀')],[(A+'SumOneAccept','T₀≈'),LB]),
 ('SumOne, Ω+1 严格下界 (step-T₁)',[(A+'SumOneFold','T₁'),(A+'SumOneClosed','ω⋅')],[(A+'SumOneFold','Lg-T₁')],[(A+'SumOneAccept','step-T₁'),LB]),
 ('TLRule, Ω (TΣ≈)',[(A+'TLRuleDiag','TopΣ'),(A+'TLRuleDiag','Lg-TopΣ')],[(A+'TLRuleDiag','Lg-TopΣ')],[(A+'TLRuleAccept','TΣ≈'),LB]),
 ('累加 Tψ, Ω (TΩ≈)',[(A+'CumUpW','Tψ')],[(A+'CumUpMain','HS-T')],[(A+'CumVal','TΩ≈'),LB]),
 ('累加 Tψ, Ω+1 严格下界 (Om1Cum step-Ω+1)',[(A+'CumUpW','Tψ')],[(A+'CumUpMain','HS-T')],[(A+'Om1CumGrow','step-Ω+1'),LB]),
 ('不累加 T⁰, Ω',[(A+'NoCumOmega','T⁰')],[(A+'NoCumOmega','HS-T⁰')],[(A+'NoCumAcceptOmega','T⁰≈'),(A+'NoCumAcceptOmega','label-T⁰')]),
 ('不累加 T₁, Ω+1 (Om1Hn, 无严格下界)',[(A+'NoCumW','Tᴰ'),(A+'NoCumForce','force')],[(A+'Om1HnMain','HS-T₁')],[(A+'Om1HnAccept','term₀'),(A+'Om1HnAccept','low-T₁'),(A+'Om1HnAccept','label-term₀')]),
]
rows={}
for k,d,c,v in routes:
    Dd=C(d); Ce=C(c)|Dd; Va=C(v)|Ce
    rows[k]=(Dd,Ce,Va)
    print('%s: 定义 %d, 加证书 %d, 加第 4 层 %d, 第 4 层净增 %d'%(k,T(Dd),T(Ce),T(Va),T(Va)-T(Ce)))
print()
k='SumOne, Ω+1 严格下界 (step-T₁)'
print('净增按模块',k,':',bymod(rows[k][2]-rows[k][1]))
print('定义按模块',k,':',bymod(rows[k][0]))
# 单独的合法性证明: 只讲和的引理
leg=C([(A+'SumOneTree','Lg-sum')])
print('Lg-sum 切片 (合法性) %d 行, 其中 SumOneTree 内 %d 行'%(T(leg),sum(lines(n) for n in leg if n[0]==A+'SumOneTree')))

# SumOne 第 4 层与累加 Ω+1 的公共/独有
a=rows['SumOne, Ω+1 严格下界 (step-T₁)'][2]-rows['SumOne, Ω+1 严格下界 (step-T₁)'][1]
b=rows['累加 Tψ, Ω+1 严格下界 (Om1Cum step-Ω+1)'][2]-rows['累加 Tψ, Ω+1 严格下界 (Om1Cum step-Ω+1)'][1]
print('Ω+1 严格下界: 只在 SumOne 第 4 层 %d 行: %s'%(T(a-b),bymod(a-b)))
print('Ω+1 严格下界: 只在累加第 4 层 %d 行: %s'%(T(b-a),bymod(b-a)))
print('公共 %d 行'%T(a&b))
