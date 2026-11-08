# 实际旧闭项与纯指数塔的双向值界

验收专用。A仍取原Fold1.TΩ1；其累加坐标链与无累加塔使用错位共尾比较。
这里只先完成树值桥，不把塔的名字当作记号验收。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionCalibrateTower where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ⊞-≤ʳ)
open import OCF.Align.FrozenAbsorbNegUpper using (P; mono; base≤)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedNativeValueFirst using (sm-value; sm-sym; terminal-pure; up-pure; right≤)
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Lean.Fold1 as Old

one : Cd
one = hs hz
F : Cd → Cd
F = P one
tower : ℕ → Cd
tower zero = one
tower (suc n) = F (tower n)
tower-limit : Cd
tower-limit = hl tower
module O = T.Orbit hz (up {S⊥})

output≤ : ∀ n → O.C.oo n ≤ᵛ F (O.C.ce n)
output≤ n = sm-value (terminal-pure _ (up-pure (O.C.ce n)))
≤output : ∀ n → F (O.C.ce n) ≤ᵛ O.C.oo n
≤output n = sm-value (sm-sym (terminal-pure _ (up-pure (O.C.ce n))))

strict-F : ∀ {a b} → hs a ≤ᵛ b → hs (F a) ≤ᵛ F b
strict-F {a} p = ≤-trans (≤l 1 (⊞-≤ʳ (F a) (base≤ one a))) (mono (≤-refl one) p)
tower-step : ∀ n → hs (tower n) ≤ᵛ tower (suc n)
tower-step zero = ≤l 1 (≤-refl _)
tower-step (suc n) = strict-F (tower-step n)
tower-weak : ∀ n → tower n ≤ᵛ tower (suc n)
tower-weak n = ≤-trans (≤s (≤-refl _)) (tower-step n)

lower-coordinate : ∀ n → tower n ≤ᵛ O.C.ce (suc n)
lower-coordinate zero = ≤-refl one
lower-coordinate (suc n) = ≤-trans (mono (≤-refl one) (lower-coordinate n))
  (≤-trans (≤output (suc n)) (right≤ (O.C.ce (suc n)) (O.C.oo (suc n))))
coordinate≤sum : ∀ n → O.C.ce (suc n) ≤ᵛ O.C.oO n
coordinate≤sum zero = ≤-refl one
coordinate≤sum (suc n) = add-mono (coordinate≤sum n) (≤-refl _)
sum≤coordinate : ∀ n → O.C.oO n ≤ᵛ O.C.ce (suc n)
sum≤coordinate zero = ≤-refl one
sum≤coordinate (suc n) = add-mono (sum≤coordinate n) (≤-refl _)

-- 一次累加坐标步由两次纯指数塔步覆盖。
double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))
absorb-step : ∀ k → tower k ⊞ F (tower k) ≤ᵛ tower (suc (suc k))
absorb-step k = ≤-trans (add-mono (tower-weak k) (≤-refl _))
  (≤-trans (≤l 1 (≤-refl _)) (mono (≤-refl one) (tower-step k)))
upper-coordinate : ∀ n → O.C.ce n ≤ᵛ tower (double n)
upper-coordinate zero = z≤
upper-coordinate (suc n) = ≤-trans
  (add-mono (upper-coordinate n) (≤-trans (output≤ n) (mono (≤-refl one) (upper-coordinate n))))
  (absorb-step (double n))

E≤A : tower-limit ≤ᵛ Old.TΩ1
E≤A = l≤ (λ n → ≤l n (≤-trans (lower-coordinate n) (coordinate≤sum n)))
A≤E : Old.TΩ1 ≤ᵛ tower-limit
A≤E = l≤ (λ n → ≤l (double (suc n)) (≤-trans (sum≤coordinate n) (upper-coordinate (suc n))))
```

已比较全部轨道而非有限测试：下界逐项，上界每一步允许两个塔步。
A与E基本列并不逐项相同，故本结论不声称FGH相同。
