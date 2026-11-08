# 两低槽的可运行直接语义

mid保底Ω、坍缩中Ω；low直接到可数层。两者均保留原世界seed及更新。
不是terminal与mid的复合，也不是固定seed1解释器。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldValueTwoSlot where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
import OCF.Lean.Fold1If as I
import OCF.Lean.Fold1Fold as F

U = step S⊥
V = step U
mid : HB U → HB V → HB U
mid b hz = hs hz
mid b (hs a) = hl (I.mul (mid b a))
mid b (hl f) = hl (λ n → mid b (f n))
mid b (hΩ (inj₁ (inj₁ ())) g)
mid b (hΩ (inj₁ (inj₂ _)) g) = hΩ (inj₂ tt) (λ e → mid b (g e))
mid b (hΩ (inj₂ _) g) = hl (F.Col.oO _⊞_ _⊞_ b b (λ _ e → e)
  (λ b′ e → mid b′ (g e)) (λ b′ e → mid b′ (g e)))

low : Cd → HB U → HB V → Cd
low u b hz = hs hz
low u b (hs a) = hl (I.mul (low u b a))
low u b (hl f) = hl (λ n → low u b (f n))
low u b (hΩ (inj₁ (inj₁ ())) g)
low u b (hΩ (inj₁ (inj₂ _)) g) = hl (F.Col.oO _⊞_ _⊞_ u u (λ _ e → e)
  (λ u′ e → low u′ b (g e)) (λ u′ e → low u′ b (g e)))
low u b (hΩ (inj₂ _) g) = hl (F.Col.oO _⊞_ _⊞_ b b (λ _ e → e)
  (λ b′ e → mid b′ (g e)) (λ b′ e → low u b′ (g e)))
```

每次co只更新被消去种类的槽；low的另一个参数固定。模型的正确性须由
对原Φ的结构模拟证明，定义本身不构成值验收。
