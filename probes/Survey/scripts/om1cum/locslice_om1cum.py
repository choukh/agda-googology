# -*- coding: utf-8 -*-
# ψ₀(Ω_{Ω+1}) 这一站, 累加这边的第 4 层账. 口径与 ../locslice_station.py 相同: 定义级切片, 计 agda 非空非注释行, 不排除任何层 (记号模块除外).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 Om1Cum, NoCumAcceptOmega, NoCumHnAccept, Label, CumVal, OCF/Free/Lab/UniformNF5Accept, 再 python3 locslice_om1cum.py <H>.
import os,sys,io,collections
here=os.path.dirname(os.path.abspath(__file__))
par=os.path.dirname(here)
s=io.open(os.path.join(par,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(par,'locslice.py')
exec(s)
A='OCF.Align.'
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def T(par):
    return sum(lines(n) for n in par if n[0] not in NOT)
def bymod(ns,top=14):
    c=collections.Counter()
    for n in ns:
        if n[0] not in NOT: c[n[0].replace('OCF.Align.','').replace('OCF.','')]+=lines(n)
    return ', '.join('%s %d'%(k,v) for k,v in c.most_common(top))
LB=(A+'Label','BTBO-label')
D_cum=[(A+'CumUpW','Tψ')]; C_cum=[(A+'CumUpMain','HS-T')]
routes=[
 # 名字, 定义根, 证书根, 第 4 层根
 ('累加 Tψ, Ω 基线 (TΩ≈)',D_cum,C_cum,[(A+'CumVal','TΩ≈'),LB]),
 ('累加 Tψ, Ω+1 严格下界 (step-Ω+1)',D_cum,C_cum,[(A+'Om1CumGrow','step-Ω+1'),LB]),
 ('累加 Tψ, Ω+1 只有 T-strict',D_cum,C_cum,[(A+'Om1CumGrow','T-strict')]),
 ('累加 Tψ, 下标不要 St (Fʸ-next)',D_cum,C_cum,[(A+'Om1CumIdx','Fʸ-next')]),
 ('累加 src BTBO, Ω',[('OCF.BTBO','BTBO')],[('OCF.BTBO','BTBO')],[(A+'BTBOFull','BTBO≈'),LB]),
 ('累加世界 Tᶜ, Ω',[(A+'CumReadTop','HS-Tᶜ')],[(A+'CumReadTop','HS-Tᶜ')],[(A+'CumUpAcceptVal','Tᶜ≈'),LB]),
 ('不累加世界 T⁰, Ω',[(A+'NoCumOmega','T⁰')],[(A+'NoCumOmega','HS-T⁰')],[(A+'NoCumAcceptOmega','T⁰≈'),(A+'NoCumAcceptOmega','label-T⁰')]),
 ('不累加 (p,a) TΩᴺ, Ω',[(A+'NoCumHon','TΩᴺ')],[(A+'NoCumHon','TΩᴺ')],[(A+'NoCumHnAccept','TΩᴺ≈'),(A+'NoCumHnAccept','label-TΩᴺ')]),
]
rows={}
for k,d,c,v in routes:
    D=C(d); Ce=C(c)|D; Va=C(v)|Ce
    rows[k]=(D,Ce,Va)
    print('%s: 定义 %d, 加证书 %d, 加第 4 层 %d, 第 4 层净增 %d, 其中记号块 %d'%(k,T(D),T(Ce),T(Va),T(Va)-T(Ce),sum(1 for n in Va if n[0] in NOT)))
print()
k='累加 Tψ, Ω 基线 (TΩ≈)'; print('净增按模块',k,':',bymod(rows[k][2]-rows[k][1]))
k='累加 Tψ, Ω+1 只有 T-strict'; print('净增按模块',k,':',bymod(rows[k][2]-rows[k][1]))
k='累加 Tψ, 下标不要 St (Fʸ-next)'; print('净增按模块',k,':',bymod(rows[k][2]-rows[k][1]))
k='不累加世界 T⁰, Ω'; print('净增按模块',k,':',bymod(rows[k][2]-rows[k][1]))
# 累加这一站比不累加多出来的第 4 层: 毛刺的实测下界
a=rows['累加 Tψ, Ω 基线 (TΩ≈)'][2]-rows['累加 Tψ, Ω 基线 (TΩ≈)'][1]
b=rows['不累加世界 T⁰, Ω'][2]-rows['不累加世界 T⁰, Ω'][1]
print('Ω 这一站, 只在累加第 4 层的块 %d 行: %s'%(T(a-b),bymod(a-b)))
print('Ω 这一站, 只在不累加第 4 层的块 %d 行: %s'%(T(b-a),bymod(b-a)))
print('两边公共 %d 行'%T(a&b))
# 对照树: 两条路线在这一站共用
Ref=C([('OCF.Free.Main','GᴺΩ̇')]); RefL=C([('OCF.Free.Main','GᴺΩ̇'),('OCF.Free.Lab.Uniform5Label','TΩ-label')])
print('对照树 GᴺΩ̇ 证书 %d, 加标签 TΩ-label %d, 其中记号块 %d'%(T(Ref),T(RefL),sum(1 for n in RefL if n[0] in NOT)))
# 估计用的标定: 同类件的代码行, 按文件, 不是切片
import re
def code(f):
    p=os.path.join(par,'..','..','OCF',*f.split('.'))+'.lagda.md'
    n=0; on=False
    for l in io.open(p,encoding='utf-8'):
        t=l.strip()
        if t.startswith('```'): on=t.startswith('```agda'); continue
        if on and t and not t.startswith('--'): n+=1
    return n
for name,fs in [('⊴ 的折叠单调',['Align.CumUpLe']),('闭包定理全文',['Align.CumUpMain']),('Level 上 E 单调',['Align.BTBOFullLe','Align.BTBOFullEmb']),('左右结构模拟',['Align.CumUpAcceptSim','Align.CumValZ']),('下标嵌入',['Align.BTBOFullEb','Align.BTBOFullV1','Align.BTBOFullV3','Align.CumUpAcceptVal']),('Level 上值严格',['Align.BTBOFullLv','Align.BTBOFullSt']),('本路新增',['Align.Om1CumGrow','Align.Om1CumIdx','Align.Om1CumTest','Align.Om1Cum'])]:
    print('标定',name,sum(code(f) for f in fs),' '.join('%s=%d'%(f.split('.')[-1],code(f)) for f in fs))
