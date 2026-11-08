# 新全有限混合闭项严格超过原P地板

值定理直接针对Bulk.closed。利用其真实第1分量的首反馈项，不把
合法性当强度，也不要求新逐层折叠等于旧direct fold。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedFiniteRegBulkValue where
open import Data.Nat using (zero)
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l; ≤Ω; Ω≤Ω)
open import OCF.Lean.Fold1Base using (≤-trans; ⊞-≤ˡ; ⊞-≤ʳ)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Align.BoundedFiniteRegIf using (F)
open import OCF.Align.BoundedFiniteRegFold using (down)
open import OCF.Align.BoundedFiniteRegUp using (floor)
import OCF.Align.BoundedFiniteRegBulk as B
open import OCF.Align.BoundedValueFloors using (right-add)

add-mono : ∀ {S} {a b c d : HB S} → a ≤ᵛ b → c ≤ᵛ d → (a ⊞ c) ≤ᵛ (b ⊞ d)
add-mono {b = b} p q = ≤-trans (⊞-≤ˡ p _) (⊞-≤ʳ b q)

act : HB (F zero) → HB (F zero)
act c = down zero (up c)
positive : ∀ c → hs hz ≤ᵛ act c
positive hz = s≤s z≤
positive (hs c) = ≤l 0 (positive c)
positive (hl f) = ≤l 0 (positive (f 0))
positive (hΩ κ g) = ≤Ω (bot (F zero) κ) (positive (g (bot (F zero) κ)))
inflate : ∀ c → c ≤ᵛ act c
inflate hz = z≤
inflate (hs c) = ≤l 1 (add-mono (inflate c) (positive c))
inflate (hl f) = l≤ (λ n → ≤l n (inflate (f n)))
inflate (hΩ κ g) = Ω≤Ω (λ c → inflate (g c))

first-strict : hs (floor zero) ≤ᵛ B.component 1
first-strict = ≤l 0 (≤l 1 (add-mono (inflate (floor zero)) (positive (floor zero))))

strict-floor : hs (floor zero) ≤ᵛ B.closed
strict-floor = ≤-trans first-strict (≤l 1 (right-add (B.component 0) (B.component 1)))

not-bounded-by-floor : B.closed ≤ᵛ floor zero → ⊥
not-bounded-by-floor p = ¬s≤ᵛ (floor zero) (≤-trans strict-floor p)
```

这是合法新闭项在P层内的严格下界；没有给某个ψ₀的读法或上界。
也不能由此把严格界传过原生跨底/末段折叠，已知无条件值单调不成立。
