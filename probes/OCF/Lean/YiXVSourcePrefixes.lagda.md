# YiXVSourcePrefixes
> 验收文件。档位：编译定理。原全部 pre 的上界：read(pre n) ≼ ψ₀(Ω_{n+2})；实际全更新底已覆盖。
> 接 YiXVSourceSem、SourceAffine*、Finite*，有限搬运比较参照 YiXVCan2Embed；未交完整外层链或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourcePrefixes where
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
open import OCF.Lean.YiASIface using (Sbᶠ; s0; ss)
open import OCF.Lean.YiLSRead using (read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≼l)
open import OCF.Align.YiLvValBase using (γ; reference-row)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteGamma as Gamma
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceWorldInput as W
import OCF.Lean.YiXVZeroRead as ZR
import OCF.Lean.YiXVStart as Start
import OCF.Lean.YiXVSourceCast as Cast
import OCF.Lean.YiXVSourceCoordinates as C
import OCF.Lean.YiXVSourceEmbed as E
import OCF.Lean.YiXVSourceGlobal as Global

down : ∀ {H n} → Sbᶠ H (suc n) → Sbᶠ H n
down s0 = ss s0
down (ss s) = ss (down s)
ordered : ∀ H {n m} → n ≤ m → A.Le H (γ H n) (γ H m)
ordered H {n = zero} {m} z≤n = E.Bound.base H m
ordered H {n = suc n} {m = suc m} (s≤s t) = Gamma.At.ψ-mono H (ordered H t)

module Context (g : ℕ → S.L) (ε : Path.Ev (S.lim g))
  (ρc : ∀ k → Path.Rt (g k)) (R : Path.Adj g) (coord : ∀ k → g k ≡ J.nat (suc k)) where
  module G = Global.Context g ε ρc R coord
  prefix : ℕ → S.Tr (S.lim g)
  prefix zero = S.zero
  prefix (suc n) = S.up (prefix n) n (O.Ωt (g n)) (O.Ωt-nz (g n))
  form : ∀ n → prefix (suc n) ≡ O.cumΩ g n
  form zero = refl
  form (suc n) = cong (λ x → S.up x (suc n) (O.Ωt (g (suc n))) (O.Ωt-nz (g (suc n)))) (form n)
  Z : ∀ H → ℕ → I.T H
  Z H zero = E.Ω H
  Z H (suc n) = Z H n L.+ E.M H (suc (suc H))
  run : ∀ H n (h : Sbᶠ H n) → G.Worlds H (Z H n) (prefix n)
  run H zero h = G.initial H
  run H (suc n) h = G.Step.result H (Z H n) (prefix n) (run H n (down h)) n h
  good : ∀ H n → A.Gd H (Z H n)
  good H zero = B.actual H
  good H (suc n) = Add.plus-good H {X = Z H n} {Y = E.M H (suc (suc H))} (good H n) (E.mg H (suc (suc H)))
  bounded : ∀ H n → Σ ℕ (λ k → A.Le H (Z H n) (γ H k))
  bounded H zero = 0 , B.rfl H F.zero {X = E.Ω H} (B.actual H)
  bounded H (suc n) with bounded H n
  ... | k , t = suc (suc common) , B.trans H F.zero {X = Z H (suc n)} {Y = γ H common L.+ γ H common} {Z = γ H (suc (suc common))}
    (Add.plus H {X = Z H n} {X′ = γ H common} {Y = E.M H (suc (suc H))} {Y′ = γ H common}
      (B.trans H F.zero {X = Z H n} {Y = γ H k} {Z = γ H common} t (ordered H (m≤m⊔n k fixed)))
      (B.trans H F.zero {X = E.M H (suc (suc H))} {Y = γ H fixed} {Z = γ H common}
        (E.Bound.mult H (suc (suc H))) (ordered H (m≤n⊔m k fixed))))
    (E.Bound.double H common (B.rfl H F.zero {X = γ H common} (Gamma.At.good H common)))
    where
    fixed = E.idx (suc (suc H))
    common = k ⊔ fixed
  bottom : ∀ H n (h : Sbᶠ H (suc n)) →
    read (Fold.ψ₀ (S.lim g) ε G.ρ (O.cumΩ g n)) ≼ L.ψ⁰ (Z H (suc n))
  bottom H n h = subst (λ x → read (Fold.ψ₀ (S.lim g) ε G.ρ x) ≼ L.ψ⁰ (Z H (suc n))) (form n)
    (subst (λ x → read x ≼ L.ψ⁰ (Z H (suc n))) (C.bcast (coord n) (G.actualB n (prefix (suc n))))
      (W.World.bot (G.Worlds.each (run H (suc n) h) n h)))
  gamma-ceiling : ∀ H k → L.ψ⁰ (γ H k) ≼ L.ψ⁰ (E.Ω (suc H))
  gamma-ceiling H k = subst (λ y → L.ψ⁰ (γ H k) ≼ y) (sym (reference-row H)) (≼l k (≼-refl _))
  ceiling : ∀ n → read (Fold.ψ₀ (S.lim g) ε G.ρ (O.cumΩ g n)) ≼ L.ψ⁰ (E.Ω (suc (suc n)))
  ceiling n = ≼-trans (bottom (suc n) n s0) (≼-trans (ZR.mono (suc n) (proj₂ b)) (gamma-ceiling (suc n) (proj₁ b)))
    where b = bounded (suc n) (suc n)

module Actual = Context Start.fg Start.e1 (proj₁ Start.r1) (proj₂ Start.r1) Cast.fg
allpre : ∀ n → read (Start.pre n) ≼ L.ψ⁰ (E.Ω (suc (suc n)))
allpre = Actual.ceiling
```
