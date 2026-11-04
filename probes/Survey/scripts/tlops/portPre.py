from common import *
s=rd('NoCumPre'); s=common(s)
s=s.replace('''# 只剩世界前缀: 无条件的版本

> 不含记号. [NoCumForce](NoCumForce.lagda.md) 的链点是输出的读出, 要 `Hn`. 这里把链点改成 $u+\\mathrm{rd}\\,y$: **只留世界前缀 $u+$**, 没有 `cumA`, 没有 `asuc`, 没有 $\\eta+$ (不是链上累加, 每个链点只前缀一次世界), 极限的基本列不累加 (`lit`). 守卫由 `⊞-fst` 字面给出.
>
> `HS-Tᵖ` 对一切 $p$, $a$ 无条件. **这不是作者要的终点**: 前缀 $u+$ 还在, 第 $k$ 项仍可能高于不累加的树. 它量出累加的职责只剩守卫这一件.
''','''# 树的算子语言 (六): 计值, 证书, 无条件

> 不含记号. 入口 [TLOps](TLOps.lagda.md). 由 [NoCumPre](NoCumPre.lagda.md) 改写, 高度是 $A$. 数据树里的闭包 `oc` 的链点是 $u+\\mathrm{rd}\\,y$: **世界前缀 $u+$ 在这里, 写明.** 它不是链上累加 (没有 `cumA`, 没有 `asuc`, 没有 $\\eta+$, 每个链点只前缀一次世界), 但它不是作者要的终点. 去掉它的义务就是 `Hn` ([NoCumForce](NoCumForce.lagda.md)), 见 [TLOps](TLOps.lagda.md) 的翻译账. 最外层的闭包不必走这里, [TLOpsClo](TLOpsClo.lagda.md) 没有前缀.
>
> `HS-Tᵖ`: 对一切字面合法的 $p$, $a$ 无条件.
''')
s=s.replace('𝓡 u = 𝓞 zero azero u','𝓡 u = 𝓞 azero azero u')
s=s.replace('''WF-T : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → WF (Tᴰ p a u₀ g e)
WF-T p a u₀ g e = ψW zero azero (Ω̇ p a) g₀ u₀ g (pos g) (z⊲ u₀) e (Ω≈ p (≈ᴬ-refl a)) (ΩW p a (lg⊲ e (lgw g)))''','''WF-T : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) → WF (Tᴰ p a u₀ lp g e)
WF-T p a u₀ lp g e = ψW azero azero (hk₀ lp) (Ω̇ p a) g₀ u₀ g (pos g) (z⊲ u₀) e (Ω≈ p (≈ᴬ-refl a)) (ΩW p a lp (lg⊲ e (lgw g)))''')
s=s.replace('''≈-T : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → Tᴰ p a u₀ g e ≈ Tᴰ p a u₀ g e
≈-T p a u₀ g e = ψQ (Ω̇ p a) (Ω̇ p a) g₀ g₀ u₀ g''','''≈-T : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) → Tᴰ p a u₀ lp g e ≈ Tᴰ p a u₀ lp g e
≈-T p a u₀ lp g e = ψQ (hk₀ lp) (hk₀ lp) refl (Ω̇ p a) (Ω̇ p a) g₀ g₀ u₀ g''')
s=s.replace('''G-Tᵖ : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → G (Tᴰ p a u₀ g e)
G-Tᵖ p a u₀ g e = C′ _ g (≈-T p a u₀ g e) (WF-T p a u₀ g e)''','''G-Tᵖ : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) → G (Tᴰ p a u₀ lp g e)
G-Tᵖ p a u₀ lp g e = C′ _ g (≈-T p a u₀ lp g e) (WF-T p a u₀ lp g e)''')
s=s.replace('''Tᵖ : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → Ord₀
Tᵖ p a u₀ g e = force (G-Tᵖ p a u₀ g e)''','''Tᵖ : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) → Ord₀
Tᵖ p a u₀ lp g e = force (G-Tᵖ p a u₀ lp g e)''')
s=s.replace('''HS-Tᵖ : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → HS (Tᵖ p a u₀ g e)
HS-Tᵖ p a u₀ g e = HS-force (G-Tᵖ p a u₀ g e)''','''HS-Tᵖ : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) → HS (Tᵖ p a u₀ lp g e)
HS-Tᵖ p a u₀ lp g e = HS-force (G-Tᵖ p a u₀ lp g e)

Lit-Tᵖ : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) → Lit₀ (Tᵖ p a u₀ lp g e)
Lit-Tᵖ p a u₀ lp g e = Lit-force (G-Tᵖ p a u₀ lp g e)''')
wr('TLOpsPre',s)
