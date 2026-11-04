from common import *
s=rd('NoCumEq'); s=common(s)
s=s.replace('''# 不累加的世界: 结构等价

> 不含记号. 结论写在 [NoCum](NoCum.lagda.md). 与 [CumUpEq](CumUpEq.lagda.md) 同形.''','''# 树的算子语言 (二): 结构等价

> 不含记号. 入口 [TLOps](TLOps.lagda.md). 由 [NoCumEq](NoCumEq.lagda.md) 改写, 高度是 $A$. 高度比较 (`p ≡ p′`) 仍是字面的, 因为高度都是同一棵合法树里的字面子项 (`⊲◁`).''')
s=s.replace('''Ω≈ zero z≈ = refl , z≈ , s≈ z≈ , tt
Ω≈ (suc p) z≈ =''','''Ω≈ azero z≈ = refl , z≈ , s≈ z≈ , tt
Ω≈ (alim f) z≈ = λ n → ≈oL {a′ = azero} {k = azero} {u₀ = one} (Ω̇ (f n) azero) (self n) (z⊲ one) (Ω̇ (f n) azero) (Ω≈ (f n) z≈)
Ω≈ (asuc p) z≈ =''')
s=s.replace('''<irr : ∀ {n} → n ◁ n → ⊥
<irr {suc n} (suc q) = <irr (<shrink q)
  where
  <shrink : ∀ {a b} → suc a ◁ b → a ◁ b
  <shrink zero = suc zero
  <shrink (suc q′) = suc (<shrink q′)
''','''◁→⊏ : ∀ {a b} → a ◁ b → a ⊏ b
◁→⊏ zero = sf C.self
◁→⊏ (suc i) = sf (◁⊲ i)
◁→⊏ (self n) = lf n C.self
◁→⊏ (lim n i) = lf n (◁⊲ i)

<irr : ∀ {n} → n ◁ n → ⊥
<irr {n} i = irr (◁→⊏ i) (≈ᴬ-refl n)

no◁◁ : ∀ {a b} → a ◁ b → b ◁ a → ⊥
no◁◁ i j = <irr (◁-tr i j)
''')
s=s.replace('(zero) C.self','zero C.self')
s=dup_paths(s)
wr('TLOpsEq',s)
