# 有界实际层族的合法混合树

整个混合树的分支仍返回整个混合签名。每个分量世界从共同目标拉回，
而非给任意积世界另附相干证明。本模块给构造与合法性，不给折叠值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedContextTree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.LHRecLeg using (pw; lgpw)
open import OCF.Lean.LHRecFl using (flL; Lg-flL)
open import OCF.Lean.BoundedContextRun
import OCF.Lean.ContextPullback as CP

module Family (P k : LH) (w : Wd (Lv k)) (B : HB (Lv k)) where
  I : Set
  I = Σ (HB (Lv k)) (λ c → c ⊲[ w ] B)
  g : HB (Lv k) → LH
  g c = P ⊕L upL k c
  F : I → KS
  F i = Lv (g (proj₁ i))
  T : KS
  T = Lv (g B)
  ctx = λ (i : I) → path-context P k (proj₂ i)
  module Q = CP.Pull F T ctx
  open Q public using (S; embed; embed-position; embed-legal)

  inject : ∀ i → HB (F i) → HB S
  inject i hz = hz
  inject i (hs a) = hs (inject i a)
  inject i (hl f) = hl (λ n → inject i (f n))
  inject i (hΩ κ f) = hΩ (i , κ) (λ c → inject i (f c))

  inject-position : ∀ i {a b W} → a ⊲[ pw (ctx i) W ] b →
    inject i a ⊲[ W ] inject i b
  inject-position i hself = hself
  inject-position i (hsuc p) = hsuc (inject-position i p)
  inject-position i (hlim n p) = hlim n (inject-position i p)
  inject-position i (hLim b p) = hLim b (inject-position i p)

  inject-legal : ∀ i a → LgB a → LgB (inject i a)
  inject-legal i hz l = l
  inject-legal i (hs a) l = inject-legal i a l
  inject-legal i (hl f) (st , l) =
    (λ n → inject-position i (st n)) , (λ n → inject-legal i (f n) (l n))
  inject-legal i (hΩ κ f) (mo , l) =
    (λ lw b b′ p → inject-position i (mo (lgpw (ctx i) lw) b b′ p)) ,
    (λ lw b → inject-legal i (f _) (l (lgpw (ctx i) lw) b))

  floor : I → HB S
  floor i = inject i (flL (g (proj₁ i)))
  floor-legal : ∀ i → LgB (floor i)
  floor-legal i = inject-legal i _ (Lg-flL _)

  sums : (ℕ → I) → ℕ → HB S
  sums f zero = floor (f zero)
  sums f (suc n) = sums f n ⊞ floor (f (suc n))
  sums-legal : ∀ f n → LgB (sums f n)
  sums-legal f zero = floor-legal (f zero)
  sums-legal f (suc n) = Lg-⊞ _ _ (sums-legal f n) (floor-legal (f (suc n)))

  mixed : (ℕ → I) → HB S
  mixed f = hl (sums f)
  mixed-legal : ∀ f → LgB (mixed f)
  mixed-legal f = (λ n → ⊞-fst _ _) , sums-legal f

  relocated : (ℕ → I) → HB T
  relocated f = embed (mixed f)
  relocated-legal : ∀ f → LgB (relocated f)
  relocated-legal f = embed-legal _ (mixed-legal f)
```

每个成员 c 的证据直指同一 B。这里没有要求选择一个有限的最大 n，
也没有把 `flL` 的全部 Ω-sup 地板（包括待消去的指标种类）声称已经折叠。
