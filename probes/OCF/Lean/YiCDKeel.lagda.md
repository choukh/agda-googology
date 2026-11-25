# 所选读回域与塔第 1 项的实际下标

验收文件；编译反例只针对 YiCDCanon 的具体域，不否定其他树侧读回域。
实际回灌的下标 0、1 在域内，下标 2 不在；下标 2 仍有当前链所用的关系见证。
只复用 YiLTKid、YiLTLift 的保持与有限实例；不改树、折叠或合法性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCDKeel where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiTBRow using (h₁)
open import OCF.Lean.YiCDCanon
open import OCF.Lean.YiLTKid using (ℓ¹; ΩΩ; module Sem)
open import OCF.Lean.YiLTLift using (Qfin; module Inst)
open import OCF.Lean.YiHCRel using (M⁰; mz; m1; mU)
open import OCF.Lean.YiANFam using (ψᴺ)
import OCF.Align.EboLeanDef as E
open E using (natT; γT)

module M = Sem (rbᶻ ℓ¹)
module F = M.Fold (B₀ ℓ¹) M.gb₀ˢ

actual-chain : ∀ k → idx k ≡ iter (F.feed G) zero k
actual-chain k = refl

not-idx2 : Canon (idx 2) → ⊥
not-idx2 (cl q) with q 0
... | ()

not-feed-closed : (∀ {c} → Canon c → Canon (feed c)) → ⊥
not-feed-closed closed = not-idx2 (closed idx1)

not-keel-domain : (∀ k → Canon (iter (F.feed G) zero k)) → ⊥
not-keel-domain all = not-idx2 (subst Canon (sym (actual-chain 2)) (all 2))

not-positive-chain-domain : (∀ k → Canon (iter (F.feed G) zero (suc k))) → ⊥
not-positive-chain-domain all = not-idx2 (subst Canon (sym (actual-chain 2)) (all 1))

one-below : zero ⊢ suc zero ◃ idx 1
one-below = ◃l 0

kid-one : M.Kdˢ (idx 1) (E.Ωt (natT 1)) (proj₁ (Ωt (h₁ (idx 1))))
kid-one = Inst.lift-mono (rbᶻ ℓ¹) one-below (Qfin 1)

branch-one : M.M¹ (E.Ωt (natT 1)) (G (idx 1))
branch-one = mU mz kid-one

idx2-related : M⁰ (ψᴺ 0 (E.Ωt (natT 1))) (idx 2)
idx2-related = F.LF¹ M.wi (Ωt zero) (m1 refl mz) branch-one tt

idx2-gamma : M⁰ (γT ΩΩ [] 1) (idx 2)
idx2-gamma = idx2-related
```
