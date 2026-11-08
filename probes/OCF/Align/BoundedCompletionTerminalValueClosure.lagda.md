# 末段值关系的实际闭包与前缀下界

加法与up闭包由关系证明本身归纳。前缀下界使用所有Ω分支的统一
下界规则，不把某个任意坐标值当作Ω折叠的下界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionTerminalValueClosure where
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l; mul)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Align.BoundedCompletionTerminalValueIf
open import OCF.Align.BoundedCompletionTerminalValueRun using (eval)
import OCF.Align.BoundedNativeTerminalReady as T

prefix-rel : ∀ {a b} → VRel a b → ∀ c → VRel a (b ⊞ c)
prefix-rel p hz = p
prefix-rel p (hs c) = vr (prefix-rel p c)
prefix-rel p (hl f) = vli 0 (prefix-rel p (f 0))
prefix-rel p (hΩ (inj₁ ()) g)
prefix-rel p (hΩ (inj₂ _) g) = vor (λ c → prefix-rel p (g c))

add-rel : ∀ {a b c d} → VRel a b → VRel c d → VRel (a ⊞ c) (b ⊞ d)
add-rel p vz = prefix-rel p _
add-rel p (vs q) = vs (add-rel p q)
add-rel p (vr q) = vr (add-rel p q)
add-rel p (vl q) = vl (λ n → add-rel p (q n))
add-rel p (vli n q) = vli n (add-rel p q)
add-rel p (vo q) = vo (λ r → add-rel p (q r))
add-rel p (vor q) = vor (λ c → add-rel p (q c))

mul-rel : ∀ {a b} → VRel a b → ∀ n → VRel (mul a n) (mul b n)
mul-rel p zero = p
mul-rel p (suc n) = add-rel (mul-rel p n) p
repeat-rel : ∀ {a b} → VRel a b → VRel (hl (mul a)) (hl (mul b))
repeat-rel p = vl (λ n → vli n (mul-rel p n))

up-mono : ∀ {a b : Cd} → a ≤ᵛ b → VRel (up a) (up b)
up-mono z≤ = vz
up-mono (s≤s p) = vs (up-mono p)
up-mono (≤s p) = vr (up-mono p)
up-mono (l≤ p) = vl (λ n → up-mono (p n))
up-mono (≤l n p) = vli n (up-mono p)

floor : HB U
floor = hΩ (inj₂ tt) up
floor-self : VRel floor floor
floor-self = vo up-mono

seed-mono : ∀ {a} → VRel a a → ∀ {u v} → u ≤ᵛ v → T.fold u a ≤ᵛ T.fold v a
seed-mono r uv = eval r uv
terminal-prefix : ∀ {a} → VRel a a → ∀ b u → T.fold u a ≤ᵛ T.fold u (a ⊞ b)
terminal-prefix r b u = eval (prefix-rel r b) (≤-refl u)
```

floor-self直接实例化真实最低Ω地板；其有限和由add-rel给出实例。
terminal-prefix是保前缀下界，不是加法同态或超可加定理。
