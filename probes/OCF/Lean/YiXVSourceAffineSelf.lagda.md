# YiXVSourceAffineSelf
> 验收文件。档位：编译定理。高参照前缀、源模拟或回灌链的工具；未交正源世界、所有 pre n 或 Goal。
> 从 YiXVSource* 与 YiXVCan2NodeOne 按有限层推广，前提均有完整闭模型；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceAffineSelf where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (sym; cong; subst)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteCanonicalInputs as C
import OCF.Lean.YiXVFiniteTransportShape as T
import OCF.Lean.YiXVFiniteCompose as Compose
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceNext as Next
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourcePathInputs as In
import OCF.Lean.YiXVSourceSelfInput as Model
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourceAffineRef as Ref
import OCF.Lean.YiXVSourceAffineGround as Ground
import OCF.Lean.YiXVSourceAffineLift as Lift
import OCF.Lean.YiXVSourceAffineSeed as Seed

module Self (n H : ℕ) {ambient : L.Ordᴵ} (pc : L.natᴵ (suc n) L.<ᴵ ambient)
  (ρ : L.Simᴵ (L.natᴵ H) ambient) (ε : L.Simᴵ (L.natᴵ (suc n)) (L.natᴵ H))
  (SrcB : Fold.Base (J.nat (suc n))) (Z : I.T H) (gz : A.Gd H Z)
  (γ : J.Tr (suc n)) (nγ : J.nat (suc n) S.⊢ S.zero ◃ γ)
  (seed : U.U (suc n) γ (L.ψ pc ρ (L.add Z ε (L.Ω (L.natᴵ (suc n)))))) where
  module D = U.Layer n (U.UR n)
  module R = A.Layer n (A.GoFam n) (A.LeFam n)
  module Fm = Ground.Frame n H pc ρ
  module Lf = Lift.Frame n H pc ρ ε
  χ : J.Tr (suc n) → J.Tr (suc n)
  χ = Fold.ψs (J.nat (suc n)) (Model.ev (suc n)) (Model.rt (suc n)) SrcB (J.nat (suc n)) Path.self γ nγ
  nχ : ∀ x → J.nat (suc n) S.⊢ S.zero ◃ χ x
  nχ = Fold.nzs (J.nat (suc n)) (Model.ev (suc n)) (Model.rt (suc n)) SrcB (J.nat (suc n)) Path.self γ nγ
  result : ∀ {x X} → R.Gd X → D.U x X → D.U (χ x) (Fm.φ (L.add Z ε X))
  result gx D.uz = seed
  result (R.gs {X} gx) (D.us {x} h) = Next.next (suc n) (nχ x)
    (Fm.good (Add.good H (suc n) {X = Z} gz ε X gx)) (result gx h)
  result gx (D.uw {X} {Y} h t) = D.uw (result (R.left t) h)
    (Fm.mono (Add.mono H (suc n) {X = Z} {X′ = Z} (B.rfl H F.zero {X = Z} gz) ε X Y t))
  result gx (D.ul h) = D.ul (λ k → result gx (h k))
  result (R.gn law gb) (D.un i {g} {f} h) = subst (D.U (S.Ω (J.slot n i) (λ a → χ (g a)))) (sym NR.ref-shape)
    (D.un i (λ a V Y gv gy o ha t → subst (D.U (χ (g (J.inB n i a))))
      (sym (cong (λ z → Fm.φ (L.add Z ε (f z))) (NR.input Y)))
      (result (gb (L.into (L.<→◃ (J.q n i)) (T.τ T.bwd (I.rank n i) Y))
        (C.At.good-in n (I.rank n i) (J.q n i) _ (GI.τ-good Y gy))
        (C.At.floor-in n (I.rank n i) (J.q n i) _ (GI.τ-floor Y o)))
        (h a V (T.τ T.bwd (I.rank n i) Y) gv (GI.τ-good Y gy) (GI.τ-floor Y o) ha (GI.τ-margin V Y gy t)))))
    where
    module NR = Ref.Node H pc ρ ε P.top i Z f
    module GI = In.Guards (P.top {suc n}) i
  result gx (D.uu {x} {X} {Y} gx₀ h gy hy) = D.uw
    (Lf.lift n (P.down P.top) (nχ x) (Add.good H (suc n) {X = Z} gz ε X gx₀) (result gx₀ h) gy hy)
    (Fm.mono (Compose.compose H (suc n) n Z ε X (λ q → L.suc q) Y gz gx₀ gy))

module Actual (n : ℕ) = Self n (suc (suc n)) L.zero (λ q → q) (λ q → L.suc q) (Model.B (suc n))
  (L.Ω (L.natᴵ (suc (suc n)))) (proj₁ (B.Ω-model (suc (suc n)) F.zero))
  (O.Ωt (J.nat (suc n))) (O.Ωt-nz (J.nat (suc n))) (Seed.Model.seed n)
actual : ∀ n → U.U (suc n) (Actual.χ n (O.Ωt (J.nat (suc n))))
  (L.ψ L.zero (λ q → q) (L.add (L.Ω (L.natᴵ (suc (suc n)))) (λ q → L.suc q)
    (L.Ω (L.natᴵ (suc n)) L.+ L.Ω (L.natᴵ (suc n)))))
actual n = Actual.result n (Add.plus-good (suc n) {X = L.Ω (L.natᴵ (suc n))} {Y = L.Ω (L.natᴵ (suc n))}
  (proj₁ (B.Ω-model (suc n) F.zero)) (proj₁ (B.Ω-model (suc n) F.zero))) (UB.ΩU (suc n))
```
