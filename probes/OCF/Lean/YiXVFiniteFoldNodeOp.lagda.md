# YiXVFiniteFoldNodeOp
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteFoldNodeOp where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteCanonicalInputs as N
import OCF.Lean.YiXVFiniteVia as V
import OCF.Lean.YiXVFiniteChain as Ch
import OCF.Lean.YiXVFiniteFoldNodeGood as G
import OCF.Lean.YiXVFiniteFoldNodeMono as M

module Node (n m : ℕ) (q : L.natᴵ m L.<ᴵ L.natᴵ (suc n)) where
  op : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ (L.natᴵ (suc n)) a)
    (v : L.natᴵ m L.<ᴵ b) (ρ : L.Simᴵ (L.natᴵ (suc n)) b)
    (f : L.U (L.natᴵ m) (L.<→◃ q) → I.T (suc n)) → I.T j
  op j p σ v ρ f with L.<ᴵ-dec (σ q) p
  ... | injᵃ (L.via e r) = L.limᵢ r (λ y → L.ψ p σ (f (L.into (L.<→◃ q) (L.tr⁻ e (L.out (L.<→◃ r) y)))))
  ... | injᵇ w = L.lim (λ k → L.ψ p σ (f (L.into (L.<→◃ q)
    (iter (λ X → L.ψ v ρ (f (L.into (L.<→◃ q) X))) (L.Ω (L.natᴵ m)) k))))
  ... | injᶜ e = L.lim (λ k → L.ψ p σ (f (L.into (L.<→◃ q)
    (iter (λ X → L.ψ v ρ (f (L.into (L.<→◃ q) X))) (L.Ω (L.natᴵ m)) k))))

  normal : ∀ j {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ (L.natᴵ (suc n)) a) f →
    op j p σ q (λ r → r) f ≡ L.ψ p σ (L.limᵢ q f)
  normal j p σ f with L.<ᴵ-dec (σ q) p
  ... | injᵃ (L.via e r) = refl
  ... | injᵇ w = refl
  ... | injᶜ e = refl
  raised : ∀ j {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ (L.natᴵ (suc (suc n))) a) f →
    op j p (λ r → σ (L.suc r)) (L.suc q) (λ r → L.suc r) f ≡
      L.ψ p σ (L.limᵢ (L.suc q) (λ u → L.up L.zero (f u)))
  raised j p σ f with L.<ᴵ-dec (σ (L.suc q)) p
  ... | injᵃ (L.via e r) = refl
  ... | injᵇ w = refl
  ... | injᶜ e = refl

  module Compare (f g : L.U (L.natᴵ m) (L.<→◃ q) → I.T (suc n))
    (bf : G.Node.Body n m q f) (bg : G.Node.Body n m q g)
    (h : M.Node.Cross n m q f g bf bg) where
    module NF = G.Node.Run n m q f bf
    module NG = G.Node.Run n m q g bg
    module NM = M.Node.Run n m q f g bf bg h
    module In = N.At n m q
    open M.Node.Cross h using (mono)
    diagonal : ∀ j {a b c d} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
      (σ : L.Simᴵ (L.natᴵ (suc n)) a) (τ : L.Simᴵ (L.natᴵ (suc n)) b)
      (v : L.natᴵ m L.<ᴵ c) (w : L.natᴵ m L.<ᴵ d)
      (ρ : L.Simᴵ (L.natᴵ (suc n)) c) (ξ : L.Simᴵ (L.natᴵ (suc n)) d) →
      A.Le j
        (L.lim (λ k → L.ψ p σ (NF.raw (iter (λ X → L.ψ v ρ (NF.raw X)) (L.Ω (L.natᴵ m)) k))))
        (L.lim (λ k → L.ψ p′ τ (NG.raw (iter (λ X → L.ψ w ξ (NG.raw X)) (L.Ω (L.natᴵ m)) k))))
    diagonal j p p′ σ τ v w ρ ξ = Out.result
      where
      left : ∀ X → A.Gd m X → A.Le m (L.Ω (L.natᴵ m)) X → A.Gd m (L.ψ v ρ (NF.raw X))
      left X gx o = G.Node.Body.good bf m v ρ _ (In.good-in X gx) (In.floor-in X o)
      right : ∀ X → A.Gd m X → A.Le m (L.Ω (L.natᴵ m)) X → A.Gd m (L.ψ w ξ (NG.raw X))
      right X gx o = G.Node.Body.good bg m w ξ _ (In.good-in X gx) (In.floor-in X o)
      module Chain = Ch.Compare m v w ρ ξ NF.raw NG.raw left right
        (λ X Y gx gy o t → mono m v w ρ ξ _ _ (In.good-in X gx) (In.good-in Y gy) (In.floor-in X o) (In.rel-in X Y t))
      module Out = Chain.Lim j (λ X → L.ψ p σ (NF.raw X)) (λ X → L.ψ p′ τ (NG.raw X))
        (λ X gx o → G.Node.Body.good bf j p σ _ (In.good-in X gx) (In.floor-in X o))
        (λ X gx o → G.Node.Body.good bg j p′ τ _ (In.good-in X gx) (In.floor-in X o))
        (λ X Y gx gy o t → mono j p p′ σ τ _ _ (In.good-in X gx) (In.good-in Y gy) (In.floor-in X o) (In.rel-in X Y t))

    result : ∀ j {a b c d} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
      (σ : L.Simᴵ (L.natᴵ (suc n)) a) (τ : L.Simᴵ (L.natᴵ (suc n)) b)
      (v : L.natᴵ m L.<ᴵ c) (w : L.natᴵ m L.<ᴵ d)
      (ρ : L.Simᴵ (L.natᴵ (suc n)) c) (ξ : L.Simᴵ (L.natᴵ (suc n)) d) →
      A.Le j (op j p σ v ρ f) (op j p′ τ w ξ g)
    result j p p′ σ τ v w ρ ξ with L.<ᴵ-dec (σ q) p | L.<ᴵ-dec (τ q) p′
    ... | injᵃ a | injᵃ b with V.exact (I.finite m) a | V.exact (I.finite m) b
    ... | r , refl | s , refl rewrite I.q-unique j r s = NM.retained j p p′ σ τ s
    result j p p′ σ τ v w ρ ξ | injᵃ a | injᵇ b = ⊥-elim (V.strict-both a b)
    result j p p′ σ τ v w ρ ξ | injᵃ a | injᶜ e = ⊥-elim (V.strict-equal a e)
    result j p p′ σ τ v w ρ ξ | injᵇ a | injᵃ b = ⊥-elim (V.strict-both a b)
    result j p p′ σ τ v w ρ ξ | injᶜ e | injᵃ b = ⊥-elim (V.strict-equal b e)
    result j p p′ σ τ v w ρ ξ | injᵇ a | injᵇ b = diagonal j p p′ σ τ v w ρ ξ
    result j p p′ σ τ v w ρ ξ | injᵇ a | injᶜ e = diagonal j p p′ σ τ v w ρ ξ
    result j p p′ σ τ v w ρ ξ | injᶜ e | injᵇ b = diagonal j p p′ σ τ v w ρ ξ
    result j p p′ σ τ v w ρ ξ | injᶜ e | injᶜ d = diagonal j p p′ σ τ v w ρ ξ

module Model = Node 0 0 L.zero
module MC = Model.Compare (L.up L.zero) (L.up L.zero) G.body G.body M.cross
actual : A.Le 1 (Model.op 1 L.zero (λ q → L.suc q) L.zero (λ q → q) (L.up L.zero))
  (Model.op 1 L.zero (λ q → L.suc q) (L.suc L.zero) (λ q → L.suc q) (L.up L.zero))
actual = MC.result 1 L.zero L.zero (λ q → L.suc q) (λ q → L.suc q) L.zero (L.suc L.zero) (λ q → q) (λ q → L.suc q)
```
