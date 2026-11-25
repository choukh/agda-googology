# YiXVFiniteFoldNodeMono
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteFoldNodeMono where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteCoerce as C
import OCF.Lean.YiXVFiniteCanonicalInputs as N
import OCF.Lean.YiXVFiniteRetainedInputs as R
import OCF.Lean.YiXVFiniteVia as V
import OCF.Lean.YiXVFiniteChain as Ch
import OCF.Lean.YiXVFiniteFoldNodeGood as G

module Node (n m : ℕ) (q : L.natᴵ m L.<ᴵ L.natᴵ (suc n))
  (f g : L.U (L.natᴵ m) (L.<→◃ q) → I.T (suc n))
  (bf : G.Node.Body n m q f) (bg : G.Node.Body n m q g) where
  module D = A.Layer n (A.GoFam n) (A.LeFam n)
  module NF = G.Node.Run n m q f bf
  module NG = G.Node.Run n m q g bg
  module In = N.At n m q
  record Cross : Set₁ where
    field
      mono : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
        (σ : L.Simᴵ (L.natᴵ (suc n)) a) (τ : L.Simᴵ (L.natᴵ (suc n)) b) u v →
        D.GU q u → D.GU q v → D.Floor q u → D.RU q u v → A.Le j (L.ψ p σ (f u)) (L.ψ p′ τ (g v))
  module Run (h : Cross) where
    open Cross h
    retained : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
      (σ : L.Simᴵ (L.natᴵ (suc n)) a) (τ : L.Simᴵ (L.natᴵ (suc n)) b) (r : L.natᴵ m L.<ᴵ L.natᴵ j) →
      A.Le j (L.limᵢ r (λ u → L.ψ p σ (f (L.into (L.<→◃ q) (L.tr⁻ (L.≅ᴵ-refl _) (L.out (L.<→◃ r) u))))))
        (L.limᵢ r (λ u → L.ψ p′ τ (g (L.into (L.<→◃ q) (L.tr⁻ (L.≅ᴵ-refl _) (L.out (L.<→◃ r) u))))))
    retained zero p p′ σ τ ()
    retained (suc j) p p′ σ τ r = E.pack (NF.retained j p σ r) (NG.retained j p′ τ r)
      (E.nn (λ u v gu gv o t → mono (suc j) p p′ σ τ _ _ (P.good u gu) (P.good v gv) (P.floor u o) (P.rel u v t)))
      where
      module E = A.Layer j (A.GoFam j) (A.LeFam j)
      module P = R.At n j m q r

module Model = Node 0 0 L.zero (L.up L.zero) (L.up L.zero) G.body G.body
cross : Model.Cross
Model.Cross.mono cross = G.Model.Body.mono G.body
actual : A.Le 1 (L.ψ L.zero (λ q → L.suc q) (L.Ω (L.natᴵ 1))) (L.ψ L.zero (λ q → L.suc q) (L.Ω (L.natᴵ 1)))
actual = Model.Run.retained cross 1 L.zero L.zero (λ q → L.suc q) (λ q → L.suc q) L.zero
```
