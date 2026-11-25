# YiXV：自身层回灌的带前缀上界
> 验收文件。编译定理 `Fold.result`：在模拟推导的字面起点上给出回灌底的实例后，自身层折叠保持上界及起点证据。
> 条件为模块参数；实际前缀底与证据在 `YiXVCarry`、`YiXVAnchor`，所有量只在第 1 层。
> 用到 `YiXVPlus`、`YiXVCarry` 的上折与 `YiOverOps` 的参照单调；没有全塔上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVSelf where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (self; ins)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (T₀; read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVSim as S
import OCF.Lean.YiXVPlus as P
import OCF.Lean.YiXVCarry as K
import OCF.Lean.YiXVAnchor as H

module Fold (B : Base (suc zero)) (Z : R.T₁) (gz : O.Gd Z)
  (γ : Tr (suc zero)) (nγ : suc zero ⊢ zero ◃ γ)
  (hγ : S.Sim.U B γ (O.ψ₁ (Z L.+ O.Ω₁))) (cγ : H.Anchor.Closed B hγ) where
  module A = S.Sim B
  module C = P.Closure B
  module HC = H.Anchor B

  χ : Tr (suc zero) → Tr (suc zero)
  χ = ψs (suc zero) tt tt B (suc zero) self γ nγ
  nχ : (x : Tr (suc zero)) → suc zero ⊢ zero ◃ χ x
  nχ = nzs (suc zero) tt tt B (suc zero) self γ nγ

  Out : Tr (suc zero) → R.T₁ → Set
  Out x X = Σ (A.U (χ x) (O.ψ₁ (Z L.+ X))) HC.Closed

  suc-case : (x : Tr (suc zero)) (X : R.T₁) → O.Gd X → Out x X → Out (suc x) (L.suc X)
  suc-case x X gd (h , c) = C.next-comp (nχ x) (O.Gd-ψ₁ (O.Gd-+ gz gd)) h ,
    HC.next-closed (nχ x) (O.Gd-ψ₁ (O.Gd-+ gz gd)) h c

  weak-case : (x : Tr (suc zero)) (X Y : R.T₁) → O.Gd X → X R.≤ₚ Y → Out x X → Out x Y
  weak-case x X Y gd q (h , c) = A.uw (O.Gd-ψ₁ (O.Gd-+ gz gd)) h (O.ψ₁-mono (O.+ₚ (O.reflₚ gz) q)) , c

  up-case : (x : Tr (suc zero)) (y : Tr zero) (ny : zero ⊢ zero ◃ y) (X : R.T₁) (Y : T₀)
    (σ : L.Simᴵ L.zero (L.suc L.zero)) → O.Gd X → read y ≼ Y → Out x X → Out (up x tt y ny) (L.add X σ Y)
  up-case x y ny X Y σ gd q (h , c) =
    A.uw (O.Gd-ψ₁ (O.Gd-add⁰ (O.Gd-+ gz gd) (read y)))
      (K.Lift.upc-comp B (nχ x) (O.Gd-+ gz gd) h σ y)
      (O.ψ₁-mono (R.trans (O.add-mono⁰ (O.reflₚ (O.Gd-+ gz gd)) q) (P.assoc-tail {σ = σ} {τ = σ} gz gd Y))) ,
    HC.upc-closed (nχ x) (O.Gd-+ gz gd) h c σ y

  result : ∀ {x X} (gd : O.Gd X) (h : A.U x X) → HC.Closed h → Out x X
  result gd (A.uz p q) refl = hγ , cγ
  result (O.gs gd) (A.us {x = x} {X = X} h) c = suc-case x X gd (result gd h c)
  result gd (A.uw {x = x} {X = X} {Y = Y} gdX h q) c = weak-case x X Y gdX q (result gdX h c)
  result gd (A.ul h) c = A.ul (λ n → proj₁ (result gd (h n) (c n))) , λ n → proj₂ (result gd (h n) (c n))
  result (O.gi {f = f} law gb) (A.un h) c =
    A.un (λ a y q →
      let
        y′ = L.tr⁻ L.z≅ y
        q′ = ≼-trans q (proj₂ (O.tr⁻≈ y))
      in proj₁ (result (gb y′ (O.s→1 q′)) (h a y′ q′) (c a y′ q′))) ,
    (λ a y q →
      let
        y′ = L.tr⁻ L.z≅ y
        q′ = ≼-trans q (proj₂ (O.tr⁻≈ y))
      in proj₂ (result (gb y′ (O.s→1 q′)) (h a y′ q′) (c a y′ q′)))
  result gd (A.uu {x = x} {y = y} {ny = ny} {X = X} {Y = Y} {σ′ = σ} gdX h q) c = up-case x y ny X Y σ gdX q (result gdX h c)
```
