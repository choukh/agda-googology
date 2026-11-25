# YiXV：实际更新底的非零目标保持
> 验收文件。编译定理：B3 的实际第 1 层分量具有 ψ₁(Ω₂) 的模拟上界及字面起点证据。
> Fold 将 YiXVSelf 的源底与比较底分开；Slot 按 YiXVChain2 的归纳界处理原折叠，参照部分和估计复用 YiXVSlot2。
> Actual 的所有参数已实填；未证明 pre 2、所有 pre n 或外层回灌链的值上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSlotSrc where
open import Data.Nat using (ℕ; zero; suc)
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

module Fold (B SrcB : Base (suc zero)) (Z : R.T₁) (gz : O.Gd Z)
  (γ : Tr (suc zero)) (nγ : suc zero ⊢ zero ◃ γ)
  (hγ : S.Sim.U B γ (O.ψ₁ (Z L.+ O.Ω₁))) (cγ : H.Anchor.Closed B hγ) where
  module A = S.Sim B
  module C = P.Closure B
  module HC = H.Anchor B

  χ : Tr (suc zero) → Tr (suc zero)
  χ = ψs (suc zero) tt tt SrcB (suc zero) self γ nγ
  nχ : (x : Tr (suc zero)) → suc zero ⊢ zero ◃ χ x
  nχ = nzs (suc zero) tt tt SrcB (suc zero) self γ nγ

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

open import OCF.Lean.YiXVStart using (B2)
import OCF.Lean.YiXVLocal as I
import OCF.Lean.YiXVChain2 as C2
open import OCF.Lean.YiOverTwo using (Gd-γ; Inv-γ)
import OCF.Lean.YiXVThird as T
import OCF.Lean.YiXVSlot2 as S2

module Slot (Q : Base (suc (suc zero))) (B : Base (suc zero))
  (seed : S.Sim.U B (bs Q (suc zero) (ins self)) (O.ψ₁ (O.Ω₁ L.+ O.Ω₁)))
  (seedC : H.Anchor.Closed B seed)
  (zeroU : S.Sim.U B zero O.Ω₁) (zeroC : H.Anchor.Closed B zeroU) where
  β = bs Q (suc zero) (ins self)
  nβ = ns Q (suc zero) (ins self)
  module Ref = C2.Chain B β nβ seed seedC zeroU zeroC
  module SF = Fold B (dS (suc zero) tt tt Q zero) O.Ω₁ O.Gd-Ω β nβ seed seedC
  module A = S.Sim B
  module HC = H.Anchor B
  module PC = P.Closure B
  open Ref using (Γ; ix; jump)

  c : ℕ → Tr (suc zero)
  c = iter (λ x → SF.χ (suc x)) zero

  Bounds : ℕ → Set
  Bounds n = Σ (A.U (c n) (Γ (ix n))) HC.Closed

  bounds : ∀ n → Bounds n
  bounds zero = zeroU , zeroC
  bounds (suc n) =
    A.uw (O.Gd-ψ₁ (O.Gd-+ O.Gd-Ω (O.gs (Gd-γ (ix n)))))
      (proj₁ (SF.result {x = suc (c n)} {X = L.suc (Γ (ix n))} (O.gs (Gd-γ (ix n)))
        (A.us {x = c n} {X = Γ (ix n)} (proj₁ (bounds n))) (proj₂ (bounds n))))
      (jump (ix n)) ,
    proj₂ (SF.result {x = suc (c n)} {X = L.suc (Γ (ix n))} (O.gs (Gd-γ (ix n)))
      (A.us {x = c n} {X = Γ (ix n)} (proj₁ (bounds n))) (proj₂ (bounds n)))

  rows : ℕ → Tr (suc zero)
  rows n = c (suc n)
  k : ℕ → ℕ
  k n = ix (suc (suc n))
  step : ∀ n → Γ n R.≤ₚ Γ (suc n)
  step = S2.step
  grow3 : ∀ n → Γ n R.≤ₚ Γ (suc (suc (suc n)))
  grow3 = S2.grow3
  absorb : ∀ n → (Γ n L.+ Γ n) R.≤ₚ Γ (suc (suc (suc n)))
  absorb = S2.absorb
  Sums : ℕ → Set
  Sums n = Σ (A.U (cum rows n) (Γ (k n))) HC.Closed
  sums : ∀ n → Sums n
  sums zero = A.uw (Gd-γ (ix 1)) (proj₁ (bounds 1)) (grow3 (ix 1)) , proj₂ (bounds 1)
  sums (suc n) =
    A.uw (O.Gd-+ (Gd-γ (k n)) (Gd-γ (k n)))
      (PC.plus-comp (Gd-γ (k n)) (proj₁ (sums n)) (Gd-γ (k n)) (proj₁ (bounds (suc (suc n)))))
      (absorb (k n)) ,
    HC.plus-closed (Gd-γ (k n)) (proj₁ (sums n)) (proj₂ (sums n))
      (Gd-γ (k n)) (proj₁ (bounds (suc (suc n)))) (proj₂ (bounds (suc (suc n))))

  δ : Tr (suc zero)
  δ = ψs (suc (suc zero)) tt tt Q (suc zero) (ins self) β nβ (Ωt (suc (suc zero)))
  upper : A.U δ (L.ψ L.zero (λ r → r) (L.Ω (L.suc (L.suc L.zero))))
  upper = A.ul (λ n → A.uw (Gd-γ (k n)) (proj₁ (sums n)) (R.≤l (k n) (step (k n))))
  closed : HC.Closed upper
  closed n = proj₂ (sums n)

Q : Base (suc (suc zero))
Q = dS (suc (suc zero)) tt tt T.B31 zero
module Actual = Slot Q I.D1 K.γ₁U H.γ₁-closed I.zeroU refl

actual-upper : S.Sim.U I.D1 T.η₁ (L.ψ L.zero (λ r → r) (L.Ω (L.suc (L.suc L.zero))))
actual-upper = Actual.upper
actual-closed : H.Anchor.Closed I.D1 actual-upper
actual-closed = Actual.closed
```
