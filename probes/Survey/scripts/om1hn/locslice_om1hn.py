# -*- coding: utf-8 -*-
# ψ₀(Ω_{Ω+1}) 不累加这一路的账, 口径同 locslice_station.py: 定义级切片, 计 agda 非空非注释行, 不排除任何层 (记号模块除外).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 Om1Hn, Om1HnAccept, NoCumAcceptOmega, 再 python3 locslice_om1hn.py <H>.
import os,sys,io,re
here=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
A='OCF.Align.'
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def T(par):
    return sum(lines(n) for n in par if n[0] not in NOT)
routes={
 '不累加世界 T⁰ (Ω 这一站, 对照)':([(A+'NoCumOmega','T⁰')],[(A+'NoCumOmega','HS-T⁰')],[(A+'NoCumAcceptOmega','T⁰≈'),(A+'NoCumAcceptOmega','label-T⁰')]),
 '不累加世界 T₁ (Ω+1), 证书不经 Hn':([(A+'NoCumW','Tᴰ'),(A+'NoCumForce','force')],[(A+'Om1HnMain','HS-T₁')],[(A+'Om1HnAccept','term₀'),(A+'Om1HnAccept','low-T₁'),(A+'Om1HnAccept','label-term₀')]),
}
base=None
for k,(d,c,v) in routes.items():
    D=C(d); Ce=C(c)|D; Va=C(v)|Ce
    print(k,'定义',T(D),'加证书',T(Ce),'加已证的验收(含参照标签)',T(Va),'其中记号块',sum(1 for n in Va if n[0] in NOT))
# 新增: 只数 Om1Hn* 里到达的块
_,c,_=routes['不累加世界 T₁ (Ω+1), 证书不经 Hn']
Ce=C(c)
print('证书闭包里 Om1Hn* 的行数', sum(lines(n) for n in Ce if n[0].startswith(A+'Om1Hn')))
print('证书闭包里 NoCum* 的行数', sum(lines(n) for n in Ce if n[0].startswith(A+'NoCum')))
