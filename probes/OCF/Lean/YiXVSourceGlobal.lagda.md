# YiXVSourceGlobal
> 验收文件。档位：编译定理。同一实际前缀下所有有界有限孩子的世界更新；原 pre 首步实例已填。
> 接 YiXVSourceSem、SourceAffine*、Finite*，有限搬运比较参照 YiXVCan2Embed；未交完整外层链或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceGlobal where
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
open import OCF.Lean.YiASIface using (Sbᶠ; s0; ss)
open import OCF.Lean.YiASProofLow using (sb≤)
open import OCF.Lean.YiLSRead using (read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceSlots as Slots
import OCF.Lean.YiXVSourceSelfInput as Default
import OCF.Lean.YiXVSourceWorldInput as W
import OCF.Lean.YiXVSourceSem as Sem
import OCF.Lean.YiXVZeroRead as ZR
import OCF.Lean.YiXVStart as Start
import OCF.Lean.YiXVSourceColumn as Col
import OCF.Lean.YiXVSourceEmbed as E
import OCF.Lean.YiXVSourceRefPath as Ref
import OCF.Lean.YiXVSourceCoordinates as C
import OCF.Lean.YiXVSourceFinitePath as FP
import OCF.Lean.YiXVSourceCast as Cast

module Context (g : ℕ → S.L) (ε : Path.Ev (S.lim g))
  (ρc : ∀ k → Path.Rt (g k)) (R : Path.Adj g) (coord : ∀ k → g k ≡ J.nat (suc k)) where
  ρ : Path.Rt (S.lim g)
  ρ = ρc , R
  B₀ : Fold.Base (S.lim g)
  B₀ = Fold.B₀ (S.lim g)
  actualB : (k : ℕ) → S.Tr (S.lim g) → Fold.Base (g k)
  actualB k x = Fold.dL g ε ρ B₀ k x
  child : ∀ k → S.Tr (S.lim g) → Fold.Base (J.nat (suc k))
  child k x = subst Fold.Base (coord k) (actualB k x)
  record Worlds (H : ℕ) (Z : I.T H) (x : S.Tr (S.lim g)) : Set where
    field
      good : A.Gd H Z
      each : ∀ m (h : Sbᶠ H (suc m)) → W.World (suc m) H (Ref.ref h) (child m x) Z
  initial : ∀ H → Worlds H (E.Ω H) S.zero
  Worlds.good (initial H) = B.actual H
  Worlds.each (initial H) m h = subst (λ B → W.World (suc m) H (Ref.ref h) B (E.Ω H))
    (sym (C.B₀cast (coord m))) (W.model (suc m) H (Ref.ref h))

  module Step (H : ℕ) (Z : I.T H) (x : S.Tr (S.lim g)) (worlds : Worlds H Z x) (k : ℕ) (hk : Sbᶠ H (suc k)) where
    K = suc (suc H)
    Z′ : I.T H
    Z′ = Z L.+ E.M H K
    x′ : S.Tr (S.lim g)
    x′ = S.up x k (O.Ωt (g k)) (O.Ωt-nz (g k))
    gz = Worlds.good worlds
    gz′ : A.Gd H Z′
    gz′ = Add.plus-good H {X = Z} {Y = E.M H K} gz (E.mg H K)
    worldK = Worlds.each worlds k hk
    pK = Ref.ref hk
    Xk : I.T (suc k)
    Xk = E.Ω (suc k) L.+ E.Ω (suc k)
    gXk : A.Gd (suc k) Xk
    gXk = Add.plus-good (suc k) {X = E.Ω (suc k)} {Y = E.Ω (suc k)} (B.actual (suc k)) (B.actual (suc k))
    capΩ : A.Le H (L.add Z (P.σ pK) Xk) Z′
    capΩ = B.trans H F.zero {X = L.add Z (P.σ pK) Xk} {Y = Z L.+ E.M H 2} {Z = Z′}
      (Ref.add-bound pK Z Xk 2 gz (E.cap-bound {n = suc k} {m = suc k} s0))
      (Add.plus H {X = Z} {X′ = Z} {Y = E.M H 2} {Y′ = E.M H K} (B.rfl H F.zero {X = Z} gz)
        (Ref.M-mono H (s≤s (s≤s z≤n))))
    bottom : read (Fold.ψ⊥ (S.lim g) ε ρ B₀ x′) ≼ L.ψ⁰ Z′
    bottom = ≼-trans (subst (λ y → read y ≼ L.ψ⁰ (L.add Z (P.σ pK) Xk))
      (sym (C.botΩ (suc k) (coord k) (ε k) (ρc k) (actualB k x)))
      (W.Out.bot {n = suc k} (Sem.upper (suc k) pK (child k x) Z worldK gXk (UB.ΩU (suc k))))) (ZR.mono H capΩ)

    module Target (m : ℕ) (hm : Sbᶠ H (suc m)) (j : ℕ) (s : Sbᶠ (suc m) j) where
      pM = Ref.ref hm
      worldM = Worlds.each worlds m hm
      w : J.nat j Path.≤ g m
      w = C.back (coord m) (Slots.pth s)
      β : J.Tr j
      β = Fold.bs (actualB m x) (J.nat j) w
      nβ : J.nat j S.⊢ S.zero ◃ β
      nβ = Fold.ns (actualB m x) (J.nat j) w
      seed : U.U j β (W.φ pM s Z)
      seed = subst (λ b → U.U j b (W.φ pM s Z)) (C.scast (coord m) (actualB m x) j (Slots.pth s)) (W.World.slots worldM j s)

      forward : ∀ (v : g k Path.≤ g m) → U.U j
        (Fold.ψs (g m) (ε m) (ρc m) (actualB m x) (J.nat j) w β nβ (Path.emb (g m) (ε m) v (O.Ωt (g k)) (O.Ωt-nz (g k)))) (W.φ pM s Z′)
      forward v = subst (λ y → U.U j y (W.φ pM s Z′))
        (sym (C.slotEmb (suc m) (suc k) j (coord m) (coord k) s t (ε m) (ρc m) (actualB m x) w β nβ v))
        (UB.weakU j (Col.upper (suc m) pM (child m x) Z worldM j s β nβ seed (E.cap-good t)
          (E.embed t (O.Ωt-nz (J.nat (suc k))) gXk (UB.ΩU (suc k)))) (W.φ-mix pM s pM s bound))
        where
        t : Sbᶠ (suc m) (suc k)
        t = proj₁ (FP.view (C.path (coord m) (coord k) v))
        le : E.weight t Data.Nat.≤ K
        le = ≤-trans (C.weight t) (s≤s (s≤s (sb≤ hm)))
        bound : A.Le H (L.add Z (P.σ pM) (E.cap t)) Z′
        bound = B.trans H F.zero {X = L.add Z (P.σ pM) (E.cap t)} {Y = Z L.+ E.M H (E.weight t)} {Z = Z′}
          (Ref.add-bound pM Z (E.cap t) (E.weight t) gz (E.cap-bound t))
          (Add.plus H {X = Z} {X′ = Z} {Y = E.M H (E.weight t)} {Y′ = E.M H K} (B.rfl H F.zero {X = Z} gz) (Ref.M-mono H le))
      backward : ∀ (v : g m Path.≤ g k) → U.U j
        (Fold.ψs (g k) (ε k) (ρc k) (actualB k x) (J.nat j) (w Path.∙ v) β nβ (O.Ωt (g k))) (W.φ pM s Z′)
      backward v = subst (λ y → U.U j y (W.φ pM s Z′))
        (sym (C.slotΩ (suc k) j (coord k) t (ε k) (ρc k) (actualB k x) (w Path.∙ v) β nβ))
        (UB.weakU j (Col.upper (suc k) pK (child k x) Z worldK j t β nβ hβ gXk (UB.ΩU (suc k)))
          (W.φ-mix pK t pM s capΩ))
        where
        t : Sbᶠ (suc k) j
        t = proj₁ (FP.view (subst (J.nat j Path.≤_) (coord k) (w Path.∙ v)))
        hβ : U.U j β (W.φ pK t Z)
        hβ = UB.weakU j seed (W.φ-mix pM s pK t (B.rfl H F.zero {X = Z} gz))
      result : U.U j (Fold.bs (child m x′) (J.nat j) (Slots.pth s)) (W.φ pM s Z′)
      result = subst (λ y → U.U j y (W.φ pM s Z′)) (sym (C.scast (coord m) (actualB m x′) j (Slots.pth s)))
        (Path.caseW-ind (λ y → U.U j y (W.φ pM s Z′)) (Path.way g R k m) forward backward)

    result : Worlds H Z′ x′
    Worlds.good result = gz′
    W.World.good (Worlds.each result m hm) = gz′
    W.World.bot (Worlds.each result m hm) = subst (λ y → read y ≼ L.ψ⁰ Z′) (sym (C.bcast (coord m) (actualB m x′))) bottom
    W.World.slots (Worlds.each result m hm) j s = Target.result m hm j s

module Actual = Context Start.fg Start.e1 (proj₁ Start.r1) (proj₂ Start.r1) Cast.fg
module First = Actual.Step 2 (E.Ω 2) S.zero (Actual.initial 2) 0 (ss s0)
actual : Actual.Worlds 2 First.Z′ (O.cumΩ Start.fg 0)
actual = First.result
```
