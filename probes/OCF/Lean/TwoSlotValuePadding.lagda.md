# 双槽输出和的联合补偿

输出相加时，输入多放一次后继即可容纳两份输出。两个原中槽可以
不同，但必须都由明确的共同中槽支配；它不是只按输入坐标的覆盖。
对有限前缀求和只要求已经访问的中槽有界，不要求整个无穷轨道有界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TwoSlotValuePadding where
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⇒m≤1+n)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (Σ₀)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedCompletionUniformIf
open import OCF.Align.BoundedCompletionUniformClosure using (add-rel; prefix-rel; right-rel)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedWorldValueTwoSlot using (U; V; mid; low)
open import OCF.Lean.TwoSlotValueRun using (middle; lower)

lower-add : ∀ {a b m n d x y z} → Value (num 1) a a → Value (num 1) b b →
  Value hz m d → Value hz n d → x ≤ᵛ z → y ≤ᵛ z →
  low x m a ⊞ low y n b ≤ᵛ low z d (a ⊞ hs b)
lower-add {a} {b} aa bb md nd xz yz = ≤l 1
  (add-mono (lower (prefix-rel aa b) md xz) (lower (right-rel a bb) nd yz))

middle-add : ∀ {a b m n d} → Value (num 1) a a → Value (num 1) b b →
  Value hz m d → Value hz n d →
  Value hz (mid m a ⊞ mid n b) (mid d (a ⊞ hs b))
middle-add {a} {b} aa bb md nd = vli 1
  (add-rel (middle (prefix-rel aa b) md) (middle (right-rel a bb) nd))

pad : (ℕ → HB V) → ℕ → HB V
pad f zero = f zero
pad f (suc n) = pad f n ⊞ hs (f (suc n))
pad-self : ∀ f → (∀ n → Value (num 1) (f n) (f n)) →
  ∀ n → Value (num 1) (pad f n) (pad f n)
pad-self f self zero = self zero
pad-self f self (suc n) = add-rel (pad-self f self n) (vs (self (suc n)))

sum≤pad : ∀ (f : ℕ → HB V) → (∀ n → Value (num 1) (f n) (f n)) →
  ∀ (slots : ℕ → HB U) (seeds : ℕ → Cd) n d z → Value hz d d →
  (∀ j → j ≤ n → Value hz (slots j) d) → (∀ j → j ≤ n → seeds j ≤ᵛ z) →
  Σ₀ (λ j → low (seeds j) (slots j) (f j)) n ≤ᵛ low z d (pad f n)
sum≤pad f self slots seeds zero d z dd bounds seeds-bound =
  lower (self zero) (bounds zero z≤n) (seeds-bound zero z≤n)
sum≤pad f self slots seeds (suc n) d z dd bounds seeds-bound = ≤-trans
  (add-mono
    (sum≤pad f self slots seeds n d z dd (λ j p → bounds j (m≤n⇒m≤1+n p))
      (λ j p → seeds-bound j (m≤n⇒m≤1+n p)))
    (≤-refl _))
  (lower-add (pad-self f self n) (self (suc n)) dd
    (bounds (suc n) (refl≤ (suc n))) (≤-refl z)
    (seeds-bound (suc n) (refl≤ (suc n))))
  where
  refl≤ : ∀ k → k ≤ k
  refl≤ zero = z≤n
  refl≤ (suc k) = s≤s (refl≤ k)
```

dd 是共同中槽的显式自证，用在递归求和后再次进行联合比较；不能由
slots j 到 d 的单向关系补出。实际反馈轨道的自证与有限前缀上界另由
其生成递推提供。本篇没有把 d 固定为与轨道无关的常量。
