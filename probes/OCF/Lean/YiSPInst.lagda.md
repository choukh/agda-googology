# 验收：非零左项的可满足实例与有限孩子的首个缺口
验收文件；编译定理：`Zero.lf¹` 无额外前提，允许左项推导任意，孩子限于字面 `zero`。
`Fin.shift-from-keep` 逐推导把有限孩子的前缀更新归约到 `Fin.Keep`；`keep-mz` 给可满足实例，任意推导的版本未证。
来源：有限孩子的关系、底、路径与 `YiKPInst.Fin` 相同；折叠律使用 `YiLTFold`。
不声称塔第 2 项的下标属于该域；最小槽位检查保存在实验文件。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSPInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([]; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiRBCrit using (h₁)
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ++[])
open import OCF.Lean.YiKCStep using (⊴-trans)
open import OCF.Lean.YiHCRel using (M⁰; mz; m1; mU)
open import OCF.Lean.YiCLFam using (nat; fn)
open import OCF.Lean.YiCLLow using (Sb; pth)
open import OCF.Lean.YiRBFam using (tu)
open import OCF.Lean.YiHCFam using (M; m⊴N)
open import OCF.Lean.YiHCFold using (GB; mkGB; gΩ; gM)
open import OCF.Lean.YiLTFold using (Qu; LF)
open import OCF.Lean.YiKPInst using (zq; zpt; pz-eq; pk-eq)
open import OCF.Lean.YiLTKid using (ℓ¹; o¹)
open import OCF.Lean.YiSPRel using (Kid⁺; module Top)
open import OCF.Lean.YiANFam using (ψᴺ)
import OCF.Align.EboLeanDef as E

module Zero (r : Rb ℓ¹) where
  Kd⁰ : (c : Tr zero) → E.T → Tr (h₁ c) → Set
  Kd⁰ c s y = Σ (c ≡ zero) λ e → M⁰ s (subst (λ c → Tr (h₁ c)) e y)

  fold⁰ : ∀ c (v : zero ≤ h₁ c) → ⊤ → (t : E.T)
        → (B : Base (h₁ c)) → ⊤ → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
        → ∀ {s y} → Kd⁰ c s y
        → M⁰ (ψᴺ 0 (t ++ s)) (proj₁ (ψ (h₁ c) (proj₂ o¹ c) (proj₂ r c) B zero v β y))
  fold⁰ _ v _ t B _ β hβ (refl , m) = Qu (proj₂ o¹ zero) (proj₂ r zero) B v β hβ m

  kid : Kid⁺ o¹ r
  kid = record { Kd = Kd⁰ ; GBc = λ _ _ _ → ⊤ ; Pc = λ _ _ → ⊤
               ; pz = λ _ → tt ; pk = λ _ → tt ; foldᶜ = fold⁰ }
  open Top o¹ r kid public

  shift : ∀ B t → Shift B t
  shift B t m c = tt

  lf¹ : (B : Base ℓ¹) (t : E.T) → M⁰ (ψᴺ 0 t) (proj₁ (B zero (ink self)))
      → ∀ {w} → Pw w → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
      → ∀ {a x} → M¹ a x → M⁰ (ψᴺ 0 (t ++ a)) (proj₁ (ψ ℓ¹ o¹ r B zero w β x))
  lf¹ B t hB = Fold.LF¹ B t (mkGB¹ hB (λ _ → tt)) (shift B t)

  nonzeroUp : Tr ℓ¹
  nonzeroUp = up (suc zero) zero (suc zero) ◃s

  nonzeroUp-m : M¹ (E.natT 1 ++ E.natT 1) nonzeroUp
  nonzeroUp-m = mU (m1 refl mz) (refl , m1 refl mz)

  nonzeroUp-fold : M⁰ (ψᴺ 0 (E.natT 1 ++ E.natT 1))
    (proj₁ (ψ ℓ¹ o¹ r (B₀ ℓ¹) zero (z≤ ℓ¹) (Ωt zero) nonzeroUp))
  nonzeroUp-fold = lf¹ (B₀ ℓ¹) [] (m1 refl mz) wu (Ωt zero) (m1 refl mz) nonzeroUp-m

module Fin (r : Rb ℓ¹) where
  Kdᶠ : (c : Tr zero) → E.T → Tr (h₁ c) → Set
  Kdᶠ c s y = Σ ℕ λ n → Σ (c ≡ nat n) λ e → M n s (subst (λ c → Tr (h₁ c)) e y)

  GBf : (n : ℕ) → E.T → Base (fn n) → Set
  GBf zero t B = ⊤
  GBf (suc n) t B = GB n B t

  GBcᶠ : (c : Tr zero) → E.T → Base (h₁ c) → Set
  GBcᶠ c t B = ∀ n (e : c ≡ nat n) → GBf n t (subst (λ c → Base (h₁ c)) e B)

  Pcᶠ : (c : Tr zero) → zero ≤ h₁ c → Set
  Pcᶠ c v = ∀ n (e : c ≡ nat n) → subst (λ c → zero ≤ h₁ c) e v ≡ zpt n

  pzᶠ : ∀ c → Pcᶠ c (z≤ (h₁ c))
  pzᶠ _ n refl = pz-eq n

  pkᶠ : ∀ c → Pcᶠ c (self ∙ proj₂ (proj₁ o¹) c)
  pkᶠ _ n refl = pk-eq n

  foldN : ∀ n (v : zero ≤ fn n) → v ≡ zpt n → (t : E.T) → (B : Base (fn n)) → GBf n t B
        → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β) → ∀ {s y} → M n s y
        → M⁰ (ψᴺ 0 (t ++ s)) (proj₁ (ψ (fn n) (proj₂ o¹ (nat n)) (proj₂ r (nat n)) B zero v β y))
  foldN zero _ refl t B _ β hβ m = Qu (proj₂ o¹ zero) (proj₂ r zero) B self β hβ m
  foldN (suc n) _ refl t B g β hβ m = LF (proj₂ o¹ (nat (suc n))) (proj₂ r (nat (suc n))) (tu (zq n)) t B g β hβ m

  foldᶠ : ∀ c (v : zero ≤ h₁ c) → Pcᶠ c v → (t : E.T)
        → (B : Base (h₁ c)) → GBcᶠ c t B
        → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β) → ∀ {s y} → Kdᶠ c s y
        → M⁰ (ψᴺ 0 (t ++ s)) (proj₁ (ψ (h₁ c) (proj₂ o¹ c) (proj₂ r c) B zero v β y))
  foldᶠ _ v pc t B g β hβ (n , refl , m) = foldN n v (pc n refl) t B (g n refl) β hβ m

  kid : Kid⁺ o¹ r
  kid = record { Kd = Kdᶠ ; GBc = GBcᶠ ; Pc = Pcᶠ
               ; pz = pzᶠ ; pk = pkᶠ ; foldᶜ = foldᶠ }
  open Top o¹ r kid public

  gbf-mono : ∀ n t {B B′ : Base (fn n)} → GBf n t B
           → (∀ i u → proj₁ (B i u) ⊴ proj₁ (B′ i u)) → GBf n t B′
  gbf-mono zero t g le = tt
  gbf-mono (suc n) t g le = mkGB (λ si → ⊴-trans (gΩ g si) (le _ _))
    (λ {i} si → m⊴N i (gM g si) (le _ _))

  gbx-same : ∀ B t → GB¹ B t → ∀ x c → GBcᶠ c t (cb B x c)
  gbx-same B t gb x _ n refl = gbf-mono n t (bC gb (nat n) n refl)
    (λ i u → ψ-⊵ ℓ¹ o¹ r B i (inc (nat n) u) (B i (inc (nat n) u)) x)

  Keep : (B : Base ℓ¹) (t : E.T) → ∀ {a x} → M¹ a x → Set
  Keep B t {a} {x} m = (n : ℕ) → ∀ {i} (si : Sb n i)
           → M i (ψᴺ i (t ++ a))
              (proj₁ (ψ ℓ¹ o¹ r B (fn i) (inc (nat (suc n)) (inc tt (pth si)))
                (B (fn i) (inc (nat (suc n)) (inc tt (pth si)))) x))

  keep-mz : ∀ B t → GB¹ B t → ∀ x → Keep B t (mz {x = x})
  keep-mz B t gb x n {i} si =
    ++[] (λ z → M i (ψᴺ i z)
      (proj₁ (ψ ℓ¹ o¹ r B (fn i) (inc (nat (suc n)) (inc tt (pth si)))
        (B (fn i) (inc (nat (suc n)) (inc tt (pth si)))) x))) t
      (gM (gbx-same B t gb x (nat (suc n)) (suc n) refl) si)

  shift-from-keep : ∀ B t → GB¹ B t → ∀ {a x} (m : M¹ a x) → Keep B t m
                  → ∀ c → GBcᶠ c (t ++ a) (cb B x c)
  shift-from-keep B t gb m keep c zero e = tt
  shift-from-keep B t gb {x = x} m keep _ (suc n) refl =
    mkGB (λ si → ⊴-trans (gΩ (bC gb (nat (suc n)) (suc n) refl) si)
      (ψ-⊵ ℓ¹ o¹ r B _ _ _ x)) (λ si → keep n si)
```
