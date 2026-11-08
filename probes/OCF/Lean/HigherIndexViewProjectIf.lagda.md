# 固定世界的最大枝投影与明确值口径

使用新有界语义：两个有界树的值序由其Cd投影的原≤ᵛ定义。它不等于
原高层≤ᵛ；后者没有Ω-left，常零Ω压到零的上界已有编译否定。
最大枝依据同一合法原世界的界，不要求比较无界坐标。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexViewProjectIf where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.LHRecTy
open import OCF.Lean.HigherIndexViewIf

cap : ∀ x κ → Wd (Lv x) → E (Lv x) κ
cap lz () W
cap (ls x) (inj₁ κ) W = cap x κ (proj₁ W)
cap (ls x) (inj₂ _) W = proj₂ W
cap (ll f) (n , κ) W = cap (f n) κ (W n)
cap (lΩ k g) (inj₁ u , inj₁ κ) W = cap k κ (proj₁ (W (inj₁ u)))
cap (lΩ k g) (inj₁ u , inj₂ _) W = proj₂ (W (inj₁ u))
cap (lΩ k g) (inj₂ d , κ) W = cap (g d) κ (W (inj₂ d))

cap-bd : ∀ x κ W → Bd (Lv x) κ (cap x κ W) W
cap-bd lz () W
cap-bd (ls x) (inj₁ κ) W = cap-bd x κ (proj₁ W)
cap-bd (ls x) (inj₂ _) W = hself
cap-bd (ll f) (n , κ) W = cap-bd (f n) κ (W n)
cap-bd (lΩ k g) (inj₁ u , inj₁ κ) W = cap-bd k κ (proj₁ (W (inj₁ u)))
cap-bd (lΩ k g) (inj₁ u , inj₂ _) W = hself
cap-bd (lΩ k g) (inj₂ d , κ) W = cap-bd (g d) κ (W (inj₂ d))

cap-upper : ∀ x κ {W e} → Bd (Lv x) κ e W → Pr (Lv x) κ W e (cap x κ W)
cap-upper lz () p
cap-upper (ls x) (inj₁ κ) p = cap-upper x κ p
cap-upper (ls x) (inj₂ _) p = p
cap-upper (ll f) (n , κ) p = cap-upper (f n) κ p
cap-upper (lΩ k g) (inj₁ u , inj₁ κ) p = cap-upper k κ p
cap-upper (lΩ k g) (inj₁ u , inj₂ _) p = p
cap-upper (lΩ k g) (inj₂ d , κ) p = cap-upper (g d) κ p

module Semantics (x : LH) (W : Wd (Lv x)) (lw : LgW (Lv x) W) where
  open Domain (Lv x) W lw public
  maximum : ∀ κ → E Target κ
  maximum κ = cap x κ W , cap-bd x κ W
  project : HB Target → Cd
  project hz = hz
  project (hs a) = hs (project a)
  project (hl f) = hl (λ n → project (f n))
  project (hΩ κ f) = project (f (maximum κ))
  infix 4 _≼ᴮ_
  _≼ᴮ_ : HB Target → HB Target → Set
  a ≼ᴮ b = project a ≤ᵛ project b
  object-value : Object → Cd
  object-value a = project (value a)
```

此定义尚需合法树上最大枝确实统摄所有分支的定理，以及Cd上的保守
连接；不能仅因把序定义成project≤project就称校准完成。
