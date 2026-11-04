from common import *
s=rd('NoCumMain'); s=common(s)
s=s.replace('''# 不累加的世界: 闭包定理

> 不含记号. 结论写在 [NoCum](NoCum.lagda.md). **`ψW`: 折叠保 `WF`, 对一切高度, 一切层, 一切目标, 一步. 这条定理不碰链.** `HS-T` 的 $(p,a)$ 部分全在这里.''','''# 树的算子语言 (五): 闭包定理

> 不含记号. 入口 [TLOps](TLOps.lagda.md). 由 [NoCumMain](NoCumMain.lagda.md) 改写. **`ψW`: 折叠保 `WF`, 对一切字面合法的高度 $p:A$, 一切层, 一切目标, 一步. 这条定理不碰链, 不按算子以外的东西分情况.** `WF` 逐节点就是三个算子的条件: `ol` 相邻 $\\trianglelefteq$; `oi` 与 `od` ($\\Omega$-极限) 分支单调; `oc` (回灌闭包) 第一支 $\\trianglelefteq$ 分支, 分支单调.''')
# arg insertion: name then one balanced token then " H H′"
def arg_after(line,name,ins,offset=1):
    res='';i=0
    pat=re.compile(r'(?<![^\s(])'+re.escape(name)+r' ')
    while True:
        m=pat.search(line,i)
        if not m: res+=line[i:];break
        j=m.end()
        res+=line[i:j]
        # skip implicit args
        k=j
        while line.startswith('{',k):
            d=0;e=k
            while True:
                if line[e]=='{':d+=1
                if line[e]=='}':
                    d-=1
                    if d==0:break
                e+=1
            k=e+2
        # token count
        for _ in range(offset):
            if k<len(line) and line[k]=='(':
                d=0;e=k
                while True:
                    if line[e]=='(':d+=1
                    if line[e]==')':
                        d-=1
                        if d==0:break
                    e+=1
                k=e+1
            else:
                e=k
                while e<len(line) and line[e] not in ' )':e+=1
                k=e
            if _<offset-1: k+=1
        res+=line[j:k]+' '+ins
        i=k
    return res
a=s.index('## §2 折叠保第一位置'); b=s.index('## §3 `WF`')
sec=s[a:b]
# signatures
sec=sec.replace('→ x ⊴ y → (gu : Gw u) (gu′ : Gw u′)','→ x ⊴ y → (H : Hk p q) (H′ : Hk p′ q) (gu : Gw u) (gu′ : Gw u′)')
sec=sec.replace('→ x ⊴ outL j y → (gu : Gw u) (gu′ : Gw u′)','→ x ⊴ outL j y → (H : Hk p q) (H′ : Hk h q) (gu : Gw u) (gu′ : Gw u′)')
sec=sec.replace('→ outL j x ⊴ y → (gu : Gw u) (gu′ : Gw u′)','→ outL j x ⊴ y → (H : Hk h q) (H′ : Hk p′ q) (gu : Gw u) (gu′ : Gw u′)')
sec=sec.replace('ψ⁰ q t x gu','ψ⁰ q t H x gu').replace('ψ⁰ q t y gu′','ψ⁰ q t H′ y gu′').replace('ψᵐ q t x gu','ψᵐ q t H x gu').replace('ψᵐ q t y gu′','ψᵐ q t H′ y gu′')
sec=sec.replace('ψ q t x gu','ψ q t H x gu').replace('ψ q t y gu′','ψ q t H′ y gu′')
sec=sec.replace('ψL q t j y gu′','ψL q t H′ j y gu′').replace('ψL q t j x gu','ψL q t H j x gu')
sec=sec.replace('ψ q t (h ','ψ q t H′ (h ')
sec=sec.replace('rf (ψ⁰Q x y gu','rf (ψ⁰Q H H′ refl x y gu')
lines=sec.split('\n');new=[]
for l in lines:
    if re.match(r'^(ψL′|Ωfst) ',l) or l.startswith('--') or l.startswith('  tR {x = o0'):
        new.append(l);continue
    for n in ['tRm','tLm','tR','tL','tmm']:
        if l.startswith(n+' :'): break
        l=arg_after(l,n,'H H′')
    new.append(l)
sec='\n'.join(new)
# path variants
sec=re.sub(r'^tRL (\S+|\(\S+ \S+\)|\(\S+ \S+ \S+\)) y d gu gu′',lambda m:'tRL '+m.group(1)+' y d H H′ gu gu′',sec,flags=re.M)
sec=re.sub(r'^tLL (\S+|\(\S+ \S+\)|\(\S+ \S+ \S+\)) x d gu gu′',lambda m:'tLL '+m.group(1)+' x d H H′ gu gu′',sec,flags=re.M)
sec=sec.replace('= tRL j y d gu gu′','= tRL j y d H H′ gu gu′').replace('= tLL j x d gu gu′','= tLL j x d H H′ gu gu′')
sec=sec.replace('tRL j y d gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e um′)','tRL j y d H (hk◁ j H′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e um′)')
sec=sec.replace('tLL j x d gu gu′ m gm um tm (⊲-tr e um)','tLL j x d (hk◁ j H) H′ gu gu′ m gm um tm (⊲-tr e um)')
sec=sec.replace('with ◁-dec p′ q','with trH H′').replace('with ◁-dec h₀ q','with trH (hk◁ j H′)')
sec=sec.replace('... | injᵃ i','... | tlt i').replace('... | injᵇ _','... | tgt _').replace('... | injᶜ refl','... | teq')
# ψL′ , Ωfst
sec=sec.replace('ψL′ : ∀ {p a u p′ a′ u′} q t {x','ψL′ : ∀ {p a u p′ a′ u′} q t (H : Hk p q) (H′ : Hk p′ q) {x')
sec=sec.replace('ψL′ q t d gu gu′','ψL′ q t H H′ d gu gu′')
sec=sec.replace('lw₂ (tR d H H′ gu gu′','lw₂ (tR d H H′ gu gu′')
sec=sec.replace('Ωfst : ∀ {p a u} q t (x','Ωfst : ∀ {p a u} q t (H : Hk p q) (x')
sec=sec.replace('Ωfst q t x gu','Ωfst q t H x gu')
sec=sec.replace('tR {x = o0 {zero} {azero} {Vs zero azero} {Low zero}} (z⊴ x) gm gu','tR {x = o0 {azero} {azero} {Vs azero azero} {Low azero}} (z⊴ x) (hkZ H) H gm gu')
sec=sec.replace('ψ q t H′ (h (⊲-tr um′ w) g (inL j z)) g v g','ψ q t H′ (h (⊲-tr um′ w) g (inL j z)) g v g')
sec=re.sub(r'(tmm \(rL [^\n]*= )tRL j y d H H′',lambda m:m.group(1)+'tRL j y d H (hk◁ j H′)',sec)
sec=re.sub(r'(tmm \(lL [^\n]*= )tLL j x d H H′',lambda m:m.group(1)+'tLL j x d (hk◁ j H) H′',sec)
sec=sec.replace("{y : 𝓞 p′ a′ u′} → x ⊴ y → (H : Hk p q) (H′ : Hk p′ q) (gu : Gw u) (gu′ : Gw u′) →\n      ∀ v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v) →\n      ∀ v′","{y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →\n      ∀ v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v) →\n      ∀ v′")
s=s[:a]+sec+s[b:]
# WF part
s=s.replace('''ΩW : ∀ p a → Lg a → WF (Ω̇ p a)
ΩW p (asuc c) w = (λ q g y y′ d → eL {stp = es} (eR {stp = es} d)) , (λ q g y _ u → u)
ΩW p (alim f) (st , w) = (λ n → eL {stp = el n} (eR {stp = el (suc n)} (Ω⊴ p (st n)))) , (λ n → ΩW p (f n) (w n))
ΩW zero azero w = tt
ΩW (suc p) azero w =
  (λ q g → lL (rL (rw (Ω⊴ p (pos g))))) , (λ q q′ g g′ vv → lL (rL (lw₂ (rw (Ω⊴ p vv))))) , ΩW p one tt , (λ {v} q g → ΩW p v (lgw g))
''','''ΩW : ∀ p a → Lg p → Lg a → WF (Ω̇ p a)
ΩW p (asuc c) lp w = (λ q g y y′ d → eL {stp = es} (eR {stp = es} d)) , (λ q g y _ u → u)
ΩW p (alim f) lp (st , w) = (λ n → eL {stp = el n} (eR {stp = el (suc n)} (Ω⊴ p (st n)))) , (λ n → ΩW p (f n) lp (w n))
ΩW azero azero lp w = tt
ΩW (asuc p) azero lp w =
  (λ q g → lL (rL (rw (Ω⊴ p (pos g))))) , (λ q q′ g g′ vv → lL (rL (lw₂ (rw (Ω⊴ p vv))))) , ΩW p one lp tt , (λ {v} q g → ΩW p v lp (lgw g))
ΩW (alim f) azero (st , lp) w =
  (λ n → lL (rL (Ωh⊴ (st n)))) , (λ n → ΩW (f n) azero (lp n) tt)
''')
a=s.index('## §4 闭包定理')
t=s[a:]
t=t.replace('ψW  : ∀ {p a u} q t (x','ψW  : ∀ {p a u} q t (H : Hk p q) (x').replace('ψWm : ∀ {p a u} q t (x','ψWm : ∀ {p a u} q t (H : Hk p q) (x').replace('ψW⁰ : ∀ {p a u} q t (x','ψW⁰ : ∀ {p a u} q t (H : Hk p q) (x')
t=t.replace('ψWL : ∀ {p h k u} q t (j','ψWL : ∀ {p h k u} q t (H : Hk h q) (j')
t=t.replace('WF (ψ q t x gu','WF (ψ q t H x gu').replace('WF (ψᵐ q t x gu','WF (ψᵐ q t H x gu').replace('WF (ψ⁰ q t x gu','WF (ψ⁰ q t H x gu').replace('WF (ψL q t j x gu','WF (ψL q t H j x gu')
t=re.sub(r'^ψW q t x','ψW q t H x',t,flags=re.M)
t=t.replace('= ψWm q t x','= ψWm q t H x').replace('ψWm q t x gu v','ψWm q t H x gu v')
t=t.replace('= ψW⁰ q t x','= ψW⁰ q t H x')
t=re.sub(r'^ψW⁰ q t ','ψW⁰ q t H ',t,flags=re.M)
t=re.sub(r'^ψW⁰ \{p\} \{a\} q t ','ψW⁰ {p} {a} q t H ',t,flags=re.M)
t=t.replace('ψW q t x gu','ψW q t H x gu').replace('ψW q t (','ψW q t H (')
t=t.replace('ψL′ q t (','ψL′ q t H H (').replace('ψL′ p k (','ψL′ p k (hkR H) (hkR H) (').replace('ψL′ h₀ k (','ψL′ h₀ k (hkD j H) (hkD j H) (')
t=t.replace('ψQ x x gu gu','ψQ H H refl x x gu gu')
t=t.replace('ψ p k (f um','ψ p k (hkR H) (f um').replace('ψ h₀ k (f um','ψ h₀ k (hkD j H) (f um')
t=t.replace('ψW p k (f um','ψW p k (hkR H) (f um').replace('ψW h₀ k (f um','ψW h₀ k (hkD j H) (f um')
t=t.replace('Ωfst p k (f um','Ωfst p k (hkR H) (f um').replace('Ωfst h₀ k (f um','Ωfst h₀ k (hkD j H) (f um')
t=t.replace('ΩW q t (lg⊲ tm (lgw gm))','ΩW q t (lgH (hkR′ H)) (lg⊲ tm (lgw gm))')
t=t.replace('ΩW p k (lg⊲','ΩW p k (lgH (hkR H)) (lg⊲').replace('ΩW h₀ k (lg⊲','ΩW h₀ k (lgH (hkR′ (hkD j H))) (lg⊲')
# zP: distinguish
parts=t.split('ψW⁰ q t H (od {h = h₀}')
parts[0]=parts[0].replace('zP (suc n) = ψQ (f um','zP (suc n) = ψQ (hkR H) (hkR H) refl (f um')
parts[1]=parts[1].replace('zP (suc n) = ψQ (f um','zP (suc n) = ψQ (hkD j H) (hkD j H) refl (f um')
t='ψW⁰ q t H (od {h = h₀}'.join(parts)
t=t.replace('with ◁-dec p q','with trH H').replace('with ◁-dec h₀ q','with trH (hk◁ j H)')
t=t.replace('... | injᵃ i','... | tlt i').replace('... | injᵇ _','... | tgt _').replace('... | injᶜ refl','... | teq')
t=t.replace('ψWL q t j x gu m gm um tm (⊲-tr e₁ um)','ψWL q t (hk◁ j H) j x gu m gm um tm (⊲-tr e₁ um)')
t=t.replace('ψWL q t zero x gu m gm um tm km e w = ψW q t H x','ψWL q t H zero x gu m gm um tm km e w = ψW q t H x')
t=t.replace('ψWL q t (suc j) x gu m gm um tm km e w = ψWL q t j x','ψWL q t H (suc j) x gu m gm um tm km e w = ψWL q t H j x')
t=t.replace('ψW q t H H x','ψW q t H x').replace('ψW⁰ q t H H ','ψW⁰ q t H ').replace('ψW q t x','ψW q t H x').replace('= ψWL q t H H j','= ψWL q t H j')
s=s[:a]+t
s=s.replace('## §3 `WF`','''lgH : ∀ {p q} → Hk p q → Lg p
lgH (hk w a b) = lg⊲ a w

hkR′ : ∀ {p q} → Hk p q → Hk q q
hkR′ (hk w a b) = hk w b b

## §3 `WF`''',1) if False else s
s=s.replace('-- 加法保 WF','''lgH : ∀ {p q} → Hk p q → Lg p
lgH (hk w a b) = lg⊲ a w

hkR′ : ∀ {p q} → Hk p q → Hk q q
hkR′ (hk w a b) = hk w b b

-- 加法保 WF''')
s=dup_paths(s)
wr('TLOpsMain',s)
