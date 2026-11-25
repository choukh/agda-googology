# YiXVFiniteFoldNodeAA
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteFoldNodeAA where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
import Data.Fin as F
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteInputs as Inputs
import OCF.Lean.YiXVFiniteRetainedInputs as R
import OCF.Lean.YiXVFiniteVia as V
import OCF.Lean.YiXVFiniteFoldNodeGood as G
import OCF.Lean.YiXVFiniteGroundFold as Ground

module Node (n m : ℕ) (q : L.natᴵ m L.<ᴵ L.natᴵ (suc n)) (X : I.T (suc n))
  (g : L.U (L.natᴵ m) (L.<→◃ q) → I.T (suc n)) (bg : G.Node.Body n m q g) where
  module D = A.Layer n (A.GoFam n) (A.LeFam n)
  module Parent = G.Node n m q g
  module NG = G.Node.Run n m q g bg
  record Bound : Set₁ where
    field
      alpha : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
        (σ : L.Simᴵ (L.natᴵ (suc n)) a) (τ : L.Simᴵ (L.natᴵ (suc n)) b) →
        A.Le j (L.ψ p σ X) (L.ψ p′ τ (g (D.start q)))
  module Run (bound : Bound) where
    open Bound bound
    retained : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
      (σ : L.Simᴵ (L.natᴵ (suc n)) a) (τ : L.Simᴵ (L.natᴵ (suc n)) b) (r : L.natᴵ m L.<ᴵ L.natᴵ j) →
      A.Le j (L.ψ p σ X)
        (L.limᵢ r (λ u → L.ψ p′ τ (g (L.into (L.<→◃ q) (L.tr⁻ (L.≅ᴵ-refl _) (L.out (L.<→◃ r) u))))))
    retained zero p p′ σ τ ()
    retained (suc j) p p′ σ τ r = E.pack (Dum.left first) (NG.retained j p′ τ r)
      (E.aa (E.trans first last))
      where
      module E = A.Layer j (A.GoFam j) (A.LeFam j)
      module Dum = A.Layer j (A.GoFam j) (A.LeFam j)
      module P = R.At n j m q r
      first = alpha (suc j) p p′ σ τ
      last = G.Node.Body.mono bg (suc j) p′ p′ τ τ (D.start q) (P.pull (E.start r))
        (Inputs.At.good-start n q) (P.good (E.start r) (Inputs.At.good-start j r))
        (Inputs.At.floor-start n q) P.start-rel
    diagonal : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
      (σ : L.Simᴵ (L.natᴵ (suc n)) a) (τ : L.Simᴵ (L.natᴵ (suc n)) b) →
      A.Le j (L.ψ p σ X) (L.lim (λ k → L.ψ p′ τ (NG.raw (NG.Chain.d k))))
    diagonal j p p′ σ τ = B.lr j F.zero {X = L.ψ p σ X} {a = λ k → L.ψ p′ τ (NG.raw (NG.Chain.d k))}
      (B.left j F.zero {X = L.ψ p σ X} {Y = L.ψ p′ τ (g (D.start q))} (alpha j p p′ σ τ))
      (λ k → G.Node.Body.good bg j p′ τ _
        (Parent.In.good-in _ (NG.Chain.good k)) (Parent.In.floor-in _ (NG.Chain.floor k))) 0 (alpha j p p′ σ τ)
    result : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
      (σ : L.Simᴵ (L.natᴵ (suc n)) a) (τ : L.Simᴵ (L.natᴵ (suc n)) b) →
      A.Le j (L.ψ p σ X) (L.ψ p′ τ (L.limᵢ q g))
    result j p p′ σ τ with L.<ᴵ-dec (τ q) p′
    ... | injᵃ v with V.exact (I.finite m) v
    ... | r , refl = retained j p p′ σ τ r
    result j p p′ σ τ | injᵇ w = diagonal j p p′ σ τ
    result j p p′ σ τ | injᶜ e = diagonal j p p′ σ τ

module Model = Node 0 0 L.zero (L.suc L.zero) (L.up L.zero) G.body
bound : Model.Bound
Model.Bound.alpha bound j p p′ σ τ = Ground.mono j p p′ (λ r → σ (L.suc r)) (λ r → τ (L.suc r)) (≼-refl (L.suc L.zero))
actual : A.Le 1 (L.ψ L.zero (λ q → L.suc q) (L.suc (L.zero {ℓ = L.natᴵ 1})))
  (L.ψ L.zero (λ q → L.suc q) (L.Ω (L.natᴵ 1)))
actual = Model.Run.result bound 1 L.zero L.zero (λ q → L.suc q) (λ q → L.suc q)
```
