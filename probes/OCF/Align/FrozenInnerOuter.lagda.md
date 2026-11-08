# 第二分量全部外层坐标：同下标结构双模拟

外层坐标折到第 1 层，实际分支中的两种 Ω₁ 都被保留，不读取坍缩界。
因此先证明整个分支族不依赖世界，再比较全部外层坐标；不需要函数外延。
此结论不包含折到第 0 层的输出比较。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenInnerOuter where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (Lv; mul; _≤ᵛ_)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo; same-value; same-sym)
import OCF.Lean.Fold1Fold as O
import OCF.Lean.SupCollapseFrozen as N
import OCF.Lean.SupCollapseClosed as C
import OCF.Align.FrozenValueSecond as S

same-refl : ∀ {U} (a : HB U) → Same a a
same-refl hz = zz
same-refl (hs a) = ss (same-refl a)
same-refl (hl f) = ll (λ n → same-refl (f n))
same-refl (hΩ κ g) = oo (λ c → same-refl (g c))

same-add : ∀ {U} {a b c d : HB U} → Same a b → Same c d → Same (a ⊞ c) (b ⊞ d)
same-add p zz = p
same-add p (ss q) = ss (same-add p q)
same-add p (ll q) = ll (λ n → same-add p (q n))
same-add p (oo q) = oo (λ c → same-add p (q c))

same-mul : ∀ {U} {a b : HB U} → Same a b → ∀ n → Same (mul a n) (mul b n)
same-mul p zero = p
same-mul p (suc n) = same-add (same-mul p n) p

-- 第一分量前缀的 Ω₁ 被保留，其分支是任意可数树。
P : Wd (Lv C.ω) → Cd → HB (step S⊥)
P w c = O.Φ C.ω C.legal-ω (hs hz) (hlim 2 (hsuc hself)) w (hz ⊞ ι 1 (up c))
Q : Wd (Lv C.ω) → Cd → HB (step S⊥)
Q w c = N.Φ C.ω C.legal-ω (hs hz) (hlim 2 (hsuc hself)) w (hz ⊞ ι 1 (up c))

pure-same : ∀ w v {a b} → Same a b → Same (P w a) (Q v b)
pure-same w v zz = ss zz
pure-same w v (ss p) = ll (same-mul (pure-same w v p))
pure-same w v (ll p) = ll (λ n → pure-same w v (p n))
pure-same w v (oo {κ = ()} p)

branch-same : ∀ w v {a b} → Same a b → Same (S.OX w a) (S.NX v b)
branch-same w v zz = oo (λ c → pure-same w v (same-refl c))
branch-same w v (ss p) = ll (same-mul (branch-same w v p))
branch-same w v (ll p) = ll (λ n → branch-same w v (p n))
branch-same w v (oo {κ = inj₁ ()} p)
branch-same w v (oo {κ = inj₂ tt} p) = oo (λ c → branch-same w v (p c))

-- 两侧世界任意，不需要把原高界与冻结高界对齐。
coordinates-same : ∀ n → Same (S.Old.ce n) (S.Frozen.ce n)
coordinates-same zero = same-refl _
coordinates-same (suc n) = same-add (coordinates-same n)
  (branch-same (S.Old.cw n) (S.Frozen.cw n) (coordinates-same n))

coordinates≤ : ∀ n → S.Old.ce n ≤ᵛ S.Frozen.ce n
coordinates≤ n = same-value (coordinates-same n)
coordinates≥ : ∀ n → S.Frozen.ce n ≤ᵛ S.Old.ce n
coordinates≥ n = same-value (same-sym (coordinates-same n))
```

该实例说明第二分量外层坐标不必采用错位共尾模拟：整个轨道已按相同 n
逐构造子双模拟。余下目标是输出 `OT/NT`，它们把旧 Ω₁ 坍缩到可数层，
这时低界更新确实被读取。本定理没有把结构双模拟冒充该输出折叠的同余律。
