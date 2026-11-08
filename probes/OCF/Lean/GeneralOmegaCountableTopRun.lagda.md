# 全可数高度的最高反馈与无累加轨道

原分类器对旧种类实际返回同种类keep，其坐标逐点往返。以下证明
不对任意分支假设同余；Same证明只在相同原坐标递归。供后续低层
观察消费的版本另用遗传Rel，而非把高层Same穿过观察器。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableTopRun where
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
import OCF.Lean.GeneralOmegaCountableTopIf as I
open import OCF.Lean.GeneralOmegaCountableTopClass
open import OCF.Lean.GeneralOmegaCountableRelIf
open import OCF.Lean.GeneralOmegaCountableRelRun using (floor-related; add-rel)
import OCF.Lean.GeneralOmegaSeededRun as Proof
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo; same-value; same-sym)
open import OCF.Lean.BoundedDiagonalSame using (same-refl; same-add)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)

module At (B : Cd) (lB : LgB B) where
  open I.At B lB
  module Q = Proof.Run (F B) (floor B)
  mul-same : ∀ {a b} → Same a b → ∀ i → Same (leftMul a i) (P.leftMul b i)
  mul-same p zero = zz
  mul-same p (suc i) = same-add p (mul-same p i)
  keep-cross : ∀ {a b} → Same a b → Same (callback a) (P.Typed b)
  keep-cross zz = same-refl (floor B)
  keep-cross (ss p) = ll (mul-same (keep-cross p))
  keep-cross (ll p) = ll (λ n → keep-cross (p n))
  keep-cross (oo {κ} {f} {g} p) with classify (hs B) lB B (hsuc hself) (inj₁ κ) | class-old B lB κ
  ... | C.keep .κ fr | returned .fr eq = oo (λ e → subst
    (λ z → Same (callback (f z)) (P.Typed (g e))) (sym (eq e)) (keep-cross (p e)))

  mul-rel : ∀ {a b} → Rel B a b → ∀ n → Rel B (P.leftMul a n) (leftMul b n)
  mul-rel p zero = rz
  mul-rel p (suc n) = add-rel p (mul-rel p n)
  typed-back : ∀ {a b} → Rel B a b → Rel B (P.Typed a) (callback b)
  typed-back rz = floor-related B
  typed-back (rs p) = rl (mul-rel (typed-back p))
  typed-back (rl p) = rl (λ n → typed-back (p n))
  typed-back (ro {κ} {f} {g} p) with classify (hs B) lB B (hsuc hself) (inj₁ κ) | class-old B lB κ
  ... | C.keep .κ fr | returned .fr eq = ro (λ {a} {b} r → subst
    (λ z → Rel B (P.Typed (f a)) (callback (g z))) (sym (eq b)) (typed-back (p r)))

  coordinates : ∀ n → Same (iterate callback (floor B) n) (P.NoSum n)
  coordinates zero = same-refl (floor B)
  coordinates (suc n) = keep-cross (coordinates n)
  outputs : ∀ n → Same (callback (iterate callback (floor B) n)) (P.NoSum (suc n))
  outputs n = keep-cross (coordinates n)
  whole : Same (observe (hs B) lB B (hsuc hself) (floor (hs B))) (hl (λ n → P.NoSum (suc n)))
  whole = ll outputs
  instance-top : TopLaws
  instance-top = record { callback-typed = keep-cross ; coordinates = coordinates ; whole = whole }

  noSum-mono : ∀ n → P.NoSum n ≤ᵛ P.NoSum (suc n)
  noSum-mono zero = Q.seed-lower (floor B)
  noSum-mono (suc n) = Q.typed-mono (noSum-mono n)
  typed-lower : P.whole ≤ᵛ observe (hs B) lB B (hsuc hself) (floor (hs B))
  typed-lower = l≤ (λ n → ≤l n (≤-trans (noSum-mono n) (same-value (same-sym (outputs n)))))
  typed-upper : observe (hs B) lB B (hsuc hself) (floor (hs B)) ≤ᵛ P.whole
  typed-upper = l≤ (λ n → ≤l (suc n) (same-value (outputs n)))
```

typed-lower/upper是原完整最高节点与原Typed无累加整输出的双向
值定理，适用于任意合法普通Cd高度，包含非有限极限。typed-back
提供后续观察所需的遗传证书；这些结论未自动断言最终Γ提升大小。
