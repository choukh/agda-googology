# 实际旧第二轨道不存在统一有限 Ω 深度界

一个待检验的上界不变量是：每个固定 ce n 的所有分支只含有界多个 Ω。
此命题在真实 ce 2 已失败。原因是 act 在含 Ω 前缀的后继上生成
任意长的有限重复。本篇只否定该有限深度不变量，不否定序数上界路线。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformAcceptUpperDepth where
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul)
import OCF.Align.BoundedCompletionValueAcceptOld as Old

U : KS
U = step S⊥

Bound : ℕ → HB U → Set
Bound d hz = ⊤
Bound d (hs a) = Bound d a
Bound d (hl f) = ∀ n → Bound d (f n)
Bound d (hΩ (inj₁ ()) g)
Bound zero (hΩ (inj₂ _) g) = ⊥
Bound (suc d) (hΩ (inj₂ _) g) = ∀ c → Bound d (g c)

-- 路径可以略过节点；hit精确记录计入的Ω个数。
data Hits : ℕ → HB U → Set where
  stop : ∀ {h} → Hits zero h
  next : ∀ {d a} → Hits d a → Hits d (hs a)
  pick : ∀ {d f} n → Hits d (f n) → Hits d (hl f)
  skip : ∀ {d g} c → Hits d (g c) → Hits d (hΩ (inj₂ tt) g)
  hit : ∀ {d g} c → Hits d (g c) → Hits (suc d) (hΩ (inj₂ tt) g)

weaken : ∀ {n d} → n ≤ d → n ≤ suc d
weaken z≤n = z≤n
weaken (s≤s p) = s≤s (weaken p)
count-bound : ∀ {n d h} → Hits n h → Bound d h → n ≤ d
count-bound stop b = z≤n
count-bound (next p) b = count-bound p b
count-bound (pick n p) b = count-bound p (b n)
count-bound {d = zero} (skip c p) ()
count-bound {d = suc d} (skip c p) b = weaken (count-bound p (b c))
count-bound {d = zero} (hit c p) ()
count-bound {d = suc d} (hit c p) b = s≤s (count-bound p (b c))

prefix : ∀ (a : HB U) {n b} → Hits n b → Hits n (a ⊞ b)
prefix a stop = stop
prefix a (next p) = next (prefix a p)
prefix a (pick n p) = pick n (prefix a p)
prefix a (skip c p) = skip c (prefix a p)
prefix a (hit c p) = hit c (prefix a p)

floor : HB U
floor = hΩ (inj₂ tt) up
many : ∀ n → Hits (suc n) (mul (Old.act floor) n)
many zero = hit hz stop
many (suc n) = hit hz (next (many n))

actual-witness : ∀ n → Hits (suc n) (Old.Pure.ce 2)
actual-witness n = skip hz (pick n (prefix (Old.Pure.ce 1) (many n)))

no-suc-bound : ∀ n → suc n ≤ n → ⊥
no-suc-bound zero ()
no-suc-bound (suc n) (s≤s p) = no-suc-bound n p

no-finite-bound : ∀ d → Bound d (Old.Pure.ce 2) → ⊥
no-finite-bound d b = no-suc-bound d (count-bound (actual-witness d) b)

-- Bound不是矛盾前提；每棵纯可数树可在深度0实例化，地板在1实例化。
pure-bound : ∀ (c : Cd) → Bound zero (up c)
pure-bound hz = tt
pure-bound (hs c) = pure-bound c
pure-bound (hl f) = λ n → pure-bound (f n)
floor-bound : Bound 1 floor
floor-bound = pure-bound
```

每个实际证据只选坐标0（合法），自然数分支n任意。它说明按固定自然数
Ω深度给 ce 2 封顶不可用；超限深度或分支闭包仍未被本定理排除。
