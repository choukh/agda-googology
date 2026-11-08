# 用一次后继补偿实际输出和

原末段fold不满足无条件超可加。对明确的VRel输入，先把两项都放到
fold(a⊞b)之下，再取其后继折叠的第1个部分和，可得带补偿的加法界。
下文把这一步迭代到真实旧第二地板的全部输出部分和。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionOutputPadding where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (Σ₀)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedCompletionTerminalValueIf
open import OCF.Align.BoundedCompletionTerminalValueRun using (eval)
open import OCF.Align.BoundedCompletionTerminalValueClosure using (prefix-rel; add-rel)
open import OCF.Align.BoundedCompletionTerminalValueAct using (old-coordinate-self)
import OCF.Align.BoundedCompletionValueAcceptOld as Old
import OCF.Align.BoundedNativeTerminalReady as T

right-rel : ∀ a {b c} → VRel b c → VRel b (a ⊞ c)
right-rel a vz = vz
right-rel a (vs p) = vs (right-rel a p)
right-rel a (vr p) = vr (right-rel a p)
right-rel a (vl p) = vl (λ n → right-rel a (p n))
right-rel a (vli n p) = vli n (right-rel a p)
right-rel a (vo p) = vo (λ q → right-rel a (p q))
right-rel a (vor p) = vor (λ c → right-rel a (p c))

padded-add : ∀ {a b u v w} → VRel a a → VRel b b → u ≤ᵛ w → v ≤ᵛ w →
  T.fold u a ⊞ T.fold v b ≤ᵛ T.fold w (a ⊞ hs b)
padded-add {a} {b} ra rb uw vw = ≤l 1
  (add-mono (eval (prefix-rel ra b) uw) (eval (right-rel a rb) vw))

pad : (ℕ → HB U) → ℕ → HB U
pad f zero = f zero
pad f (suc n) = pad f n ⊞ hs (f (suc n))

pad-self : ∀ f → (∀ n → VRel (f n) (f n)) → ∀ n → VRel (pad f n) (pad f n)
pad-self f r zero = r zero
pad-self f r (suc n) = add-rel (pad-self f r n) (vs (r (suc n)))

sum≤pad : ∀ f → (∀ n → VRel (f n) (f n)) → ∀ (seeds : ℕ → Cd) w →
  (∀ n → seeds n ≤ᵛ w) → ∀ n →
  Σ₀ (λ k → T.fold (seeds k) (f k)) n ≤ᵛ T.fold w (pad f n)
sum≤pad f r seeds w upper zero = eval (r zero) (upper zero)
sum≤pad f r seeds w upper (suc n) = ≤-trans
  (add-mono (sum≤pad f r seeds w upper n) (≤-refl _))
  (padded-add (pad-self f r n) (r (suc n)) (≤-refl w) (upper (suc n)))

old-padded-sums : ∀ n → Old.Pure.oO n ≤ᵛ T.fold hz (pad Old.Pure.ce n)
old-padded-sums zero = eval (old-coordinate-self zero) (≤-refl hz)
old-padded-sums (suc n) = ≤-trans
  (add-mono (old-padded-sums n) (≤-refl _))
  (padded-add (pad-self Old.Pure.ce old-coordinate-self n)
    (old-coordinate-self (suc n)) (≤-refl hz) (≤-refl hz))
```

old-padded-sums是全部真实Old.Pure输出和的无条件实例。尚须把pad的
原末段输出送到实际新轨道的共尾项，不能把本引理当作该覆盖已完成。
pad只在验收比较中出现，不替换旧坐标、新轨道或最终C。
