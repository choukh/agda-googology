# YiXVSourceNodeEnvelope
> 验收文件。档位：编译定理。节点参照的保留／对角展开，按字面下标界分派。
> 按 YiXVCan2Sem、YiXVSourceAffine* 与 YiXVSourceGrowth 统一；未交实际全基底、所有 pre n、Need1 或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceNodeEnvelope where
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteVia as V
import OCF.Lean.YiXVFiniteTransportShape as T
import OCF.Lean.YiXVSourcePath as Path
import OCF.Lean.YiXVSourcePathInputs as In
import OCF.Lean.YiXVZeroRead as ZR

raise-bound : ∀ {a b} → I.Finite b → a L.<ᴵ b → L.suc a L.<ᴵ L.suc b
raise-bound I.fz ()
raise-bound (I.fs b) L.zero = L.zero
raise-bound (I.fs b) (L.suc q) = L.suc (raise-bound b q)
≤-case : ∀ {j m} → j ≤ m → (j ≡ m) ⊎ (L.natᴵ j L.<ᴵ L.natᴵ m)
≤-case {j = zero} {m = zero} z≤n = inj₁ refl
≤-case {j = zero} {m = suc m} z≤n = inj₂ (ZR.zero-bound m)
≤-case {j = suc j} {m = suc m} (s≤s t) with ≤-case t
... | inj₁ refl = inj₁ refl
... | inj₂ q = inj₂ (raise-bound (I.finite m) q)
no-retain : ∀ {j m} → j ≤ m → L.natᴵ m L.≺ᴵ L.natᴵ j → ⊥
no-retain t v with ≤-case t
... | inj₁ refl = L.≺ᴵ-irrefl v
... | inj₂ q = V.strict-both v (L.via (L.≅ᴵ-refl _) q)

module Node (N m H : ℕ) (q : L.natᴵ m L.<ᴵ L.natᴵ N) (ε : L.Simᴵ (L.natᴵ N) (L.natᴵ H)) (Z : I.T H)
  (f : L.U (L.natᴵ m) (L.<→◃ q) → I.T N) where
  qa = ε q
  ca : I.T m → L.U (L.natᴵ m) (L.<→◃ q)
  ca Y = L.coe (L.<→◃ qa) (L.<→◃ q) (L.into (L.<→◃ qa) Y)
  b : L.U (L.natᴵ m) (L.<→◃ qa) → I.T H
  b u = L.add Z ε (f (L.coe (L.<→◃ qa) (L.<→◃ q) u))
  P : I.T m → I.T m
  P Y = L.ψ qa (λ r → r) (b (L.into (L.<→◃ qa) Y))
  d : ℕ → I.T m
  d = iter P (L.Ω (L.natᴵ m))
  ν₀ : I.T m → I.T zero
  ν₀ Y = L.ψ⁰ (b (L.into (L.<→◃ qa) Y))
  bot-shape : L.ψ⁰ (L.add Z ε (L.limᵢ q f)) ≡ L.lim (λ n → ν₀ (d n))
  bot-shape = refl

  module Target (j : ℕ) {ambient : L.Ordᴵ} (pc : L.natᴵ j L.<ᴵ ambient) (ρ : L.Simᴵ (L.natᴵ H) ambient) where
    ν : I.T m → I.T j
    ν Y = L.ψ pc ρ (b (L.into (L.<→◃ qa) Y))
    diagonal : j ≤ m → L.ψ pc ρ (L.add Z ε (L.limᵢ q f)) ≡ L.lim (λ n → ν (d n))
    diagonal t with L.<ᴵ-dec (ρ qa) pc
    ... | injᵃ v = ⊥-elim (no-retain t v)
    ... | injᵇ w = refl
    ... | injᶜ e = refl
    inp : (r : L.natᴵ m L.<ᴵ L.natᴵ j) → L.U (L.natᴵ m) (L.<→◃ r) → L.U (L.natᴵ m) (L.<→◃ q)
    inp r u = L.coe (L.<→◃ qa) (L.<→◃ q) (L.into (L.<→◃ qa) (T.τ T.bwd m (L.out (L.<→◃ r) u)))
    act : (r : L.natᴵ m L.<ᴵ L.natᴵ j) → L.U (L.natᴵ m) (L.<→◃ r) → I.T j
    act r u = L.ψ pc ρ (L.add Z ε (f (inp r u)))
    retained : (r : L.natᴵ m L.<ᴵ L.natᴵ j) → L.ψ pc ρ (L.add Z ε (L.limᵢ q f)) ≡ L.limᵢ r (act r)
    retained r with L.<ᴵ-dec (ρ qa) pc
    ... | injᵃ v with V.exact (I.finite m) v
    ... | s , refl rewrite I.q-unique j s r = refl
    retained r | injᵇ w = ⊥-elim (V.strict-both (L.via (L.≅ᴵ-refl _) r) w)
    retained r | injᶜ e = ⊥-elim (V.strict-equal (L.via (L.≅ᴵ-refl _) r) e)

    module Canonical (l : ℕ) (e : l ≡ m) (qt : L.natᴵ l L.<ᴵ L.natᴵ j) where
      r = Path.cast-q e qt
      F′ : L.U (L.natᴵ l) (L.<→◃ qt) → I.T j
      F′ u = act r (In.convert e qt r refl u)
      ref-shape : L.ψ pc ρ (L.add Z ε (L.limᵢ q f)) ≡ L.limᵢ qt F′
      ref-shape = trans (retained r) (In.node-convert e qt r refl (act r))
      input : ∀ Y → inp r (In.convert e qt r refl (L.into (L.<→◃ qt) Y)) ≡ L.into (L.<→◃ q) (T.τ T.bwd m (subst I.T e Y))
      input Y = trans
        (cong (L.into (L.<→◃ q)) (L.out-into (L.<→◃ qa)
          (T.τ T.bwd m (L.out (L.<→◃ r) (In.convert e qt r refl (L.into (L.<→◃ qt) Y))))))
        (cong (λ X → L.into (L.<→◃ q) (T.τ T.bwd m X))
          (trans (In.out-convert e qt r refl (L.into (L.<→◃ qt) Y)) (cong (subst I.T e) (L.out-into (L.<→◃ qt) Y))))

module Model = Node 1 0 2 L.zero (λ q → L.suc q) (L.Ω (L.natᴵ 2)) (L.up L.zero)
module Keep = Model.Target 1 L.zero (λ q → q)
module Drop = Model.Target 0 (L.suc L.zero) (λ q → q)
actual-keep : L.ψ L.zero (λ q → q) (L.add (L.Ω (L.natᴵ 2)) (λ q → L.suc q) (L.Ω (L.natᴵ 1))) ≡ L.limᵢ L.zero (Keep.act L.zero)
actual-keep = Keep.retained L.zero
actual-drop : L.ψ (L.suc L.zero) (λ q → q) (L.add (L.Ω (L.natᴵ 2)) (λ q → L.suc q) (L.Ω (L.natᴵ 1))) ≡ L.lim (λ n → Drop.ν (Model.d n))
actual-drop = Drop.diagonal z≤n
```
