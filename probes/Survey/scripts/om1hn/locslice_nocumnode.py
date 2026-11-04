# -*- coding: utf-8 -*-
# NoCumNode 这一路的账, 口径同 locslice_station.py / locslice_om1hn.py: 定义级切片, 计 agda 非空非注释行, 不排除任何层 (记号模块除外).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 NoCumNode, NoCumNodeAccept, Om1Hn, Om1HnAccept, NoCumAcceptOmega, TLRule, TLRuleAccept, 再 python3 locslice_nocumnode.py <H>.
import os,sys,io
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
 '不累加 T⁰, ψ₀(Ω_Ω) (对照)':([(A+'NoCumOmega','T⁰')],[(A+'NoCumOmega','HS-T⁰')],[(A+'NoCumAcceptOmega','T⁰≈'),(A+'NoCumAcceptOmega','label-T⁰')]),
 'Om1Hn T₁, ψ₀(Ω_{Ω+1}), 链读 W⊕x':([(A+'NoCumW','Tᴰ'),(A+'NoCumForce','force')],[(A+'Om1HnMain','HS-T₁')],[(A+'Om1HnAccept','term₀'),(A+'Om1HnAccept','low-T₁'),(A+'Om1HnAccept','label-term₀')]),
 'NoCumNode T₁, ψ₀(Ω_{Ω+1}), 第 0 层是值':([(A+'NoCumW','Ω̇'),(A+'NoCumNodeE','val')],[(A+'NoCumNodeMain','HS-T₁')],[(A+'NoCumNodeAccept','BTBO≺T₁'),(A+'NoCumNodeAccept','same-Ω'),(A+'NoCumNodeAccept','label-Ω')]),
 'TLRule Top, ψ₀(Ω_Ω) (和节点)':([(A+'TLRuleSum','Top')],[(A+'TLRuleSum','Top')],[(A+'TLRuleAccept','T≈')]),
}
for k,(d,c,v) in routes.items():
    D=C(d); Ce=C(c)|D; Va=C(v)|Ce
    print(k,'定义',T(D),'加证书',T(Ce),'加已证验收(含参照标签)',T(Va),'第4层净增',T(Va)-T(Ce),'其中记号块',sum(1 for n in Va if n[0] in NOT))
_,c,v=routes['NoCumNode T₁, ψ₀(Ω_{Ω+1}), 第 0 层是值']
Ce=C(c); Va=C(v)|Ce
print('NoCumNode 证书闭包: NoCumNode* 行', sum(lines(n) for n in Ce if n[0].startswith(A+'NoCumNode')), 'Om1Hn* 行', sum(lines(n) for n in Ce if n[0].startswith(A+'Om1Hn')), 'NoCum*(旧) 行', sum(lines(n) for n in Ce if n[0].startswith(A+'NoCum') and not n[0].startswith(A+'NoCumNode')))
print('NoCumNode 第4层新块 (NoCumNode*):', sum(lines(n) for n in Va-Ce if n[0].startswith(A+'NoCumNode')))
