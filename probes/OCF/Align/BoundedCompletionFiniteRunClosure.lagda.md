# 分层关系的实际地板与回灌闭包

真实有限flL全部自相关，含会被消去的最高Ω分支。未要求任意raw树自相关。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFiniteRunClosure where
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecLay using (_⊕L_; upL)
open import OCF.Lean.LHRecFl using (flL)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunIf
open import OCF.Align.BoundedDescentValueBridge using (Native)


rel-add : ∀ {S Q a a′ b b′} → TreeRel S Q a a′ → TreeRel S Q b b′ →
  TreeRel S Q (a ⊞ b) (a′ ⊞ b′)
rel-add p rz = p
rel-add p (rs q) = rs (rel-add p q)
rel-add p (rl q) = rl (λ n → rel-add p (q n))
rel-add p (ro q) = ro (λ x y r → rel-add p (q x y r))

rel-partial : ∀ {S Q a b} → TreeRel S Q a b → ∀ n →
  TreeRel S Q (Ops.partial S (λ _ → a) n) (Ops.partial S (λ _ → b) n)
rel-partial p zero = p
rel-partial p (suc n) = rel-add (rel-partial p n) p
rel-repeat : ∀ {S Q a b} → TreeRel S Q a b →
  TreeRel S Q (Ops.repeat S a) (Ops.repeat S b)
rel-repeat p = rl (rel-partial p)

pure-reflexive : ∀ (c : Cd) → Same c c
pure-reflexive hz = zz
pure-reflexive (hs c) = ss (pure-reflexive c)
pure-reflexive (hl f) = ll (λ n → pure-reflexive (f n))

pure-up : ∀ {a b : Cd} → Same a b → Rel hz (up a) (up b)
pure-up zz = rz
pure-up (ss p) = rs (pure-up p)
pure-up (ll p) = rl (λ n → pure-up (p n))

up-rel : ∀ c {a b} → Rel c a b → Rel (hs c) (up a) (up b)
up-rel c rz = rz
up-rel c (rs p) = rs (up-rel c p)
up-rel c (rl p) = rl (λ n → up-rel c (p n))
up-rel c (ro p) = ro (λ x y r → up-rel c (p x y r))

floor : ∀ n → HB (Native (num n))
floor n = flL (ls lz ⊕L upL lz (num n))

floor-rel : ∀ n → Rel (num n) (floor n) (floor n)
floor-rel zero = ro (λ x y r → pure-up r)
floor-rel (suc n) = ro (λ x y r → up-rel (num n) r)

zero-same : ∀ {a b} → Rel hz a b → Same a b
zero-same rz = zz
zero-same (rs p) = ss (zero-same p)
zero-same (rl p) = ll (λ n → zero-same (p n))
zero-same (ro {κ = inj₁ ()} p)
zero-same (ro {κ = inj₂ _} p) = oo (λ c → zero-same (p c c (pure-reflexive c)))
```

floor-rel是全部实际有限flL的非空实例；最高Ω的坐标关系递归使用低层Rel。
zero-same仅在目标0提取全Same，未把此结论扩展到高层raw坐标。
