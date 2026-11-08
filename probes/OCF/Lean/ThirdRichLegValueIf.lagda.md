# 全 raw 分支的树值覆盖

这里的 Ω 规则比较同一种类的全部 raw 分支上确界，允许每个左坐标
选取不同的右坐标。它不是原动态折叠的单调定理，也不宣称等同高层
`TreeValue` 的全有序坐标规则。在第零层没有 Ω，关系确实导出原标准
`≤ᵛ`。合法低坐标的版本还须检查所选坐标合法，不能从 raw 结论省略。
关系不给下标判等、三歧或更新操作；此处比较的是值侧树的分支覆盖。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Lean.ThirdRichLegValueIf where

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
import OCF.Lean.Fold1If as V
open import OCF.Lean.NegFold1Base using (≤ᵛ-refl; ≤ᵛ-trans)

module _ {S : KS} where
  infix 4 _≼ʳ_
  data _≼ʳ_ : HB S → HB S → Set where
    rz : ∀ {b} → hz ≼ʳ b
    rs : ∀ {a b} → a ≼ʳ b → hs a ≼ʳ hs b
    rr : ∀ {a b} → a ≼ʳ b → a ≼ʳ hs b
    rl : ∀ {f b} → (∀ n → f n ≼ʳ b) → hl f ≼ʳ b
    ri : ∀ {a f} n → a ≼ʳ f n → a ≼ʳ hl f
    ro : ∀ {κ f g} → (∀ d → Σ (E S κ) (λ e → f d ≼ʳ g e)) →
      hΩ κ f ≼ʳ hΩ κ g
    ru : ∀ {a κ g} → (∀ e → a ≼ʳ g e) → a ≼ʳ hΩ κ g
    rt : ∀ {a b c} → a ≼ʳ b → b ≼ʳ c → a ≼ʳ c

  reflʳ : ∀ a → a ≼ʳ a
  reflʳ hz = rz
  reflʳ (hs a) = rs (reflʳ a)
  reflʳ (hl f) = rl (λ n → ri n (reflʳ (f n)))
  reflʳ (hΩ κ g) = ro (λ d → d , reflʳ (g d))

  left : ∀ a b → a ≼ʳ a ⊞ b
  left a hz = reflʳ a
  left a (hs b) = rr (left a b)
  left a (hl f) = ri 0 (left a (f 0))
  left a (hΩ κ g) = ru (λ e → left a (g e))

  right : ∀ a b → b ≼ʳ a ⊞ b
  right a hz = rz
  right a (hs b) = rs (right a b)
  right a (hl f) = rl (λ n → ri n (right a (f n)))
  right a (hΩ κ g) = ro (λ d → d , right a (g d))

zero-sound : ∀ {a b : Cd} → a ≼ʳ b → a V.≤ᵛ b
zero-sound rz = V.z≤
zero-sound (rs p) = V.s≤s (zero-sound p)
zero-sound (rr p) = V.≤s (zero-sound p)
zero-sound (rl p) = V.l≤ (λ n → zero-sound (p n))
zero-sound (ri n p) = V.≤l n (zero-sound p)
zero-sound (ro {κ = ()} p)
zero-sound (ru {κ = ()} p)
zero-sound (rt p q) = ≤ᵛ-trans (zero-sound p) (zero-sound q)
```

`ru` 要全部右分支的统一下界，不能任选一个右 Ω 坐标。因此加法
左前缀保留没有借用任意坐标选取。`ro` 的重编号只在同种类内发生。
