# 关系式码树对应审查：零层种子为 1 时的实际最小 Ω 折叠

本篇仍只审查冻结的逐基本列关系 `JiaRep.Rep`，不改树或关系接口。
条件是当前目标零层种子字面为 1。最小正规 Ω 经原 ψ 折叠后，
根的前三项分别是零、1、ℕ-极限；下面检查这种序列是否能逐项对应
某个 EBO 裸项的基本列。条件实例只用来说明非空，不作为高层种子已正确。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaRepAuditOne where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.EboLeanDef
  using (T; PT; ψ; Ωt; cof; cω; fsn)
open import OCF.Align.EboLeanView
  using (Vω; ws; wl; w4; w5; w6; vω; fω; fω-eq)
open import OCF.Align.EboLeanBase using (n[])
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.JiaBase using (Seeds; Tree; Below; below; coe; module Layer)
open Seeds using (seed)
open import OCF.Align.JiaFold using (regular; lift; module Fold)
open import OCF.Align.JiaRep using (Rep; module RelLayer)

one : T
one = Ωt []

unitP : PT
unitP = ψ [] []

zero-code : ∀ (a : Acc′ []) {c} → Rep a Layer.z c → c ≡ []
zero-code a RelLayer.rz = refl

one-code : ∀ (a : Acc′ []) {c} → Rep a (Layer.s Layer.z) c → c ≡ one
one-code a (RelLayer.rs RelLayer.rz) = refl

limit-not-two : ∀ (a : Acc′ []) {f} →
  Rep a (Layer.l f) (unitP ∷ unitP ∷ []) → ⊥
limit-not-two a (RelLayer.rl () _)

-- 任何 ω-共尾裸项若第零项为空，只能走复制 n 次的规则。
-- 这是逐构造子的全称分类，不是搜索有限个记号码。
copy-steps : ∀ {c} (v : Vω c) → fω v 0 ≡ [] →
  Σ PT (λ p → (fω v 1 ≡ p ∷ []) × (fω v 2 ≡ p ∷ p ∷ []))
copy-steps (ws v) ()
copy-steps (wl e v) ()
copy-steps (w4 {u = u} {b} e) _ = ψ u (OCF.Align.EboLeanDef.pred b) , refl , refl
copy-steps (w5 e v) ()
copy-steps (w6 e g v) ()

singleton-inj : ∀ {p q : PT} → p ∷ [] ≡ q ∷ [] → p ≡ q
singleton-inj refl = refl

coe-zero : ∀ {ℓ} (a b : Acc′ ℓ) → coe a b Layer.z ≡ Layer.z
coe-zero (acc h) (acc k) = refl

coe-one : ∀ {ℓ} (a b : Acc′ ℓ) → coe a b (Layer.s Layer.z) ≡ Layer.s Layer.z
coe-one (acc h) (acc k) = refl

lift-zero : ∀ {i ℓ} (a : Acc′ i) (b : Acc′ ℓ) (p : Below i ℓ) →
  lift a b p Layer.z ≡ Layer.z
lift-zero (acc h) (acc k) p = refl

lift-one : ∀ {i ℓ} (a : Acc′ i) (b : Acc′ ℓ) (p : Below i ℓ) →
  lift a b p (Layer.s Layer.z) ≡ Layer.s Layer.z
lift-one (acc h) (acc k) p = refl

no-zero-one-limit : ∀ (a : Acc′ []) c {f} → cof c ≡ cω →
  Rep a Layer.z (fsn c 0) →
  Rep a (Layer.s Layer.z) (fsn c 1) →
  Rep a (Layer.l f) (fsn c 2) → ⊥
no-zero-one-limit a c {f} ec r₀ r₁ r₂ with
  copy-steps (vω c ec) (trans (sym (fω-eq (vω c ec) 0)) (zero-code a r₀))
... | p , e₁ , e₂ = limit-not-two a
  (subst (Rep a (Layer.l f)) to-two r₂)
  where
  p-one : p ≡ unitP
  p-one = singleton-inj
    (trans (sym (trans (fω-eq (vω c ec) 1) e₁)) (one-code a r₁))
  to-two : fsn c 2 ≡ unitP ∷ unitP ∷ []
  to-two = trans (trans (fω-eq (vω c ec) 2) e₂)
    (cong (λ q → q ∷ q ∷ []) p-one)

no-code-for-regular : ∀ (seeds : Seeds) (a₁ : Acc′ one) (a₀ : Acc′ []) →
  seed seeds [] a₀ ≡ Layer.s Layer.z → ∀ c →
  Rep a₀
    (Fold.ψ seeds a₁ a₀ (below n[] OCF.Align.EboLeanDef.[]<)
      (regular a₁ n[])) c → ⊥
no-code-for-regular seeds (acc h₁) (acc h₀) e c (RelLayer.rl ec branches) =
  no-zero-one-limit (acc h₀) c ec (branches 0)
    (subst (λ x → Rep (acc h₀) x (fsn c 1)) step-zero (branches 1))
    (subst (λ x → Rep (acc h₀) x (fsn c 2)) step-two (branches 2))
  where
  p : Below [] one
  p = below n[] OCF.Align.EboLeanDef.[]<
  aL : Acc′ []
  aL = h₁ n[] OCF.Align.EboLeanDef.[]<
  input : Tree [] (acc h₀) → Tree one (acc h₁)
  input y = lift aL (acc h₁) p (coe (acc h₀) aL y)
  F : Tree [] (acc h₀) → Tree [] (acc h₀)
  F y = Fold.ψ seeds (acc h₁) (acc h₀) p (input y)
  input-zero : input Layer.z ≡ Layer.z
  input-zero = trans (cong (lift aL (acc h₁) p) (coe-zero (acc h₀) aL))
    (lift-zero aL (acc h₁) p)
  input-one : input (Layer.s Layer.z) ≡ Layer.s Layer.z
  input-one = trans (cong (lift aL (acc h₁) p) (coe-one (acc h₀) aL))
    (lift-one aL (acc h₁) p)
  step-zero : F Layer.z ≡ Layer.s Layer.z
  step-zero = trans (cong (Fold.ψ seeds (acc h₁) (acc h₀) p) input-zero) e
  step-two : F (F Layer.z) ≡ Fold.ψ seeds (acc h₁) (acc h₀) p (Layer.s Layer.z)
  step-two = trans (cong F step-zero)
    (cong (Fold.ψ seeds (acc h₁) (acc h₀) p) input-one)

one-seeds : Seeds
seed one-seeds ℓ a = Layer.s Layer.z

one-seeds-zero : ∀ a → seed one-seeds [] a ≡ Layer.s Layer.z
one-seeds-zero a = refl
```

已编译定理的否定范围是：零层种子为 1 时，当前 `Rep` 不能
覆盖原树侧最小正规 Ω 的实际 ψ 输出。它不否定这棵树是合法对象，
不否定其序数值，不否定允许不同基本列的关系式对应，也不修改 ℕ 子句。
