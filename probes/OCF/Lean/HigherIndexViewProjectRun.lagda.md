# 合法最大枝是上确界，投影保位置与合法

保位置明确要求右树合法；Ω情况下先由其单调把选中枝搬到最大枝。
Cd连接给双向等价，不把新的有界语义伪装成旧高层关系。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexViewProjectRun where
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤s; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; same-value; same-sym)
open import OCF.Lean.LHRecTy
open import OCF.Lean.HigherIndexViewProjectIf

cd-position-value : ∀ {a b : Cd} → a ⊲ b → a ≤ᵛ b
cd-position-value hself = ≤-refl _
cd-position-value (hsuc p) = ≤s (cd-position-value p)
cd-position-value (hlim n p) = ≤l n (cd-position-value p)
cd-position-value (hLim {κ = ()} bd p)

module Theory (x : LH) (W : Wd (Lv x)) (lw : LgW (Lv x) W) where
  open Semantics x W lw public
  position : ∀ {a} b → LgB b → a ⊲[ tt ] b → project a ⊲ project b
  position b l hself = hself
  position (hs b) l (hsuc p) = hsuc (position b l p)
  position (hl f) (st , l) (hlim n p) = hlim n (position (f n) (l n) p)
  position (hΩ κ g) (mo , l) (hLim {c = e} bd p) =
    ⊲ᴮ-tr (position (g e) (l tt tt) p)
      (position (g (maximum κ)) (l tt tt)
        (mo tt tt tt (cap-upper x κ (proj₂ e))))

  legal : ∀ a → LgB a → LgB (project a)
  legal hz l = tt
  legal (hs a) l = legal a l
  legal (hl f) (st , l) = (λ n → position (f (Data.Nat.suc n)) (l (Data.Nat.suc n)) (st n)) ,
    λ n → legal (f n) (l n)
    where import Data.Nat
  legal (hΩ κ g) (mo , l) = legal (g (maximum κ)) (l tt tt)

  branch-below : ∀ κ g → LgB (hΩ κ g) → ∀ e → project (g e) ≤ᵛ project (hΩ κ g)
  branch-below κ g (mo , l) e = cd-position-value
    (position (g (maximum κ)) (l tt tt) (mo tt tt tt (cap-upper x κ (proj₂ e))))
  least-upper : ∀ κ g d → (∀ e → project (g e) ≤ᵛ d) → project (hΩ κ g) ≤ᵛ d
  least-upper κ g d upper = upper (maximum κ)

  pure : Cd → HB Target
  pure hz = hz
  pure (hs a) = hs (pure a)
  pure (hl f) = hl (λ n → pure (f n))
  pure (hΩ () f)
  pure-value : ∀ a → Same (project (pure a)) a
  pure-value hz = zz
  pure-value (hs a) = ss (pure-value a)
  pure-value (hl f) = ll (λ n → pure-value (f n))
  pure-value (hΩ () f)
  cd-forward : ∀ {a b} → a ≤ᵛ b → pure a ≼ᴮ pure b
  cd-forward {a} {b} p = ≤-trans (same-value (pure-value a))
    (≤-trans p (same-value (same-sym (pure-value b))))
  cd-backward : ∀ {a b} → pure a ≼ᴮ pure b → a ≤ᵛ b
  cd-backward {a} {b} p = ≤-trans (same-value (same-sym (pure-value a)))
    (≤-trans p (same-value (pure-value b)))
```

branch-below与least-upper给合法Ω节点的上确界特征；pure-value和
cd-forward/backward把这一语义在Cd域上连接到原≤ᵛ。未推出旧高层Ω-left。
