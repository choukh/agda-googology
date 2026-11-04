from common import *
s=rd('NoCumForce'); s=common(s)
i=s.index('```agda')
s='''# 树的算子语言 (十): 去掉前缀的全部义务

> 不含记号. 入口 [TLOps](TLOps.lagda.md). 由 [NoCumForce](NoCumForce.lagda.md) 改写, 高度是 $A$. 链点是输出的字面读出 (`tie`), **没有前缀, 没有累加.** `C′`: `WF` 加 `Hn` 就有证书. **`Hn` 就是不能一般化的那一条义务:** 闭包的第一支的读出以闭包的世界为第一位置, 只在链点上的分支要求. 它在 [TLOpsPre](TLOpsPre.lagda.md) 里由前缀 `⊞-fst` 字面给出, 在这里是一条关于输出的定理, 没有证明. **暂停, 未走通, 不是否定.**

'''+s[i:]
s=s.replace('𝓡 u = 𝓞 zero azero u','𝓡 u = 𝓞 azero azero u')
s=s.replace('''WF-T : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → WF (Tᴰ p a u₀ g e)
WF-T p a u₀ g e = ψW zero azero (Ω̇ p a) g₀ u₀ g (pos g) (z⊲ u₀) e (Ω≈ p (≈ᴬ-refl a)) (ΩW p a (lg⊲ e (lgw g)))''','''WF-T : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) → WF (Tᴰ p a u₀ lp g e)
WF-T p a u₀ lp g e = ψW azero azero (hk₀ lp) (Ω̇ p a) g₀ u₀ g (pos g) (z⊲ u₀) e (Ω≈ p (≈ᴬ-refl a)) (ΩW p a lp (lg⊲ e (lgw g)))''')
s=s.replace('''≈-T : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → Tᴰ p a u₀ g e ≈ Tᴰ p a u₀ g e
≈-T p a u₀ g e = ψQ (Ω̇ p a) (Ω̇ p a) g₀ g₀ u₀ g''','''≈-T : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) → Tᴰ p a u₀ lp g e ≈ Tᴰ p a u₀ lp g e
≈-T p a u₀ lp g e = ψQ (hk₀ lp) (hk₀ lp) refl (Ω̇ p a) (Ω̇ p a) g₀ g₀ u₀ g''')
s=s.replace('''G-T : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → Hn (Tᴰ p a u₀ g e) → G (Tᴰ p a u₀ g e)
G-T p a u₀ g e h = C′ _ g (≈-T p a u₀ g e) (WF-T p a u₀ g e) h''','''G-T : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) → Hn (Tᴰ p a u₀ lp g e) → G (Tᴰ p a u₀ lp g e)
G-T p a u₀ lp g e h = C′ _ g (≈-T p a u₀ lp g e) (WF-T p a u₀ lp g e) h''')
s=s.replace('''Tᴺ : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → Hn (Tᴰ p a u₀ g e) → Ord₀
Tᴺ p a u₀ g e h = force (G-T p a u₀ g e h)''','''Tᴺ : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) → Hn (Tᴰ p a u₀ lp g e) → Ord₀
Tᴺ p a u₀ lp g e h = force (G-T p a u₀ lp g e h)''')
s=s.replace('''HS-Tᴺ : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) (h : Hn (Tᴰ p a u₀ g e)) → HS (Tᴺ p a u₀ g e h)
HS-Tᴺ p a u₀ g e h = HS-force (G-T p a u₀ g e h)''','''HS-Tᴺ : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) (h : Hn (Tᴰ p a u₀ lp g e)) → HS (Tᴺ p a u₀ lp g e h)
HS-Tᴺ p a u₀ lp g e h = HS-force (G-T p a u₀ lp g e h)''')
wr('TLOpsForce',s)
