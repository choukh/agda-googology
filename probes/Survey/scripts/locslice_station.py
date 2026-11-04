# -*- coding: utf-8 -*-
# 同一站比同一站: 到 ψ₀(Ω_Ω) 的几条路线, 按定义级切片计 agda 非空非注释行, 不排除任何层 (记号模块除外).
# 用法: 用 agda --html 编译 BTBOFull, NoCumAcceptOmega, CumUpAcceptVal, Label, 再 python3 locslice_station.py <H>.
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
def T(par):
    return sum(lines(n) for n in par if n[0] not in NOT)
routes={
 '累加 src BTBO':([('OCF.BTBO','BTBO')],[('OCF.BTBO','BTBO')],[(A+'BTBOFull','BTBO≈'),(A+'Label','BTBO-label')]),
 '不累加 BTBOᴵ':([(A+'NoCumsum','BTBOᴵ')],[(A+'NoCumsum','BTBOᴵ'),(A+'NoCumsum','BTBO-HS')],[(A+'Label','BTBO-label')]),
 '累加世界 Tᶜ':([(A+'CumReadTop','Tᶜ')],[(A+'CumReadTop','HS-Tᶜ')],[(A+'CumUpAcceptVal','Tᶜ≈'),(A+'Label','BTBO-label')]),
 '不累加世界 T⁰':([(A+'NoCumOmega','T⁰')],[(A+'NoCumOmega','HS-T⁰')],[(A+'NoCumAcceptOmega','T⁰≈'),(A+'NoCumAcceptOmega','label-T⁰')]),
}
for k,(d,c,v) in routes.items():
    D=C(d); Ce=C(c)|D; Va=C(v)|Ce
    print(k,'定义',T(D),'加证书',T(Ce),'加序数值验收(含参照标签)',T(Va),'其中记号块',sum(1 for n in Va if n[0] in NOT))
