# 标准底旧 Ω₃ 的全部前缀与有限 ψ₂ 塔

第四层。旧第 n 个前缀由高度 2n+3 的 ψ₂ 塔盖住，每座有限塔又严格低于某个旧前缀。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FirstBranchOldScale where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import WVOne using (T₀; read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-suc; ≼-refl; l≼; ≼lim⁻; ≺→s≼)
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLegBlock as Leg
import OCF.Lean.YiLegOps as Op
import OCF.Lean.YiLSRead as V
import Survey.W4FirstBranchSelf as Self
import OCF.Lean.YiXVCan2Zero as Z
import B12Omega3Ref as Target
import B12BtboCut as Ref
import Survey.W4PTOFinite as PTO
import Survey.W4FirstBranchNativeThree as Old
open import Survey.W4FirstBranchRoom using (stage; rise)

opaque
  prefix : ℕ → T₀
  prefix k = V.read (Op.cum Old.Rows.rows k)
  height : ℕ → ℕ
  height = λ n → suc (suc (suc (Self.tower-index n)))

  ceiling : ∀ n → prefix n ≼ stage (height n)
  ceiling n = ≼-trans {b = Old.Rows.Gr (suc (suc (Self.tower-index n)))} (Self.prefix-bound n)
    (proj₂ (PTO.id₂-branch (suc (suc (Self.tower-index n)))))

  recover : ∀ k → Σ ℕ (λ n → L.suc (stage k) ≼ prefix n)
  recover k = ≼lim⁻ {f = prefix} (≼-trans {b = stage (suc k)} (rise k)
    (≼-trans {b = Ref.finite 3} (OCF.Align.Value.≼l (k) (proj₁ (PTO.id₂-branch k))) Old.standard))

  early : prefix 1 ≼ stage 2
  early = ≼-trans {b = L.ψ⁰ (Target.finitePower 3)} Old.first-prefix
    (≼-trans {b = Target.at (Ref.finite 3) 1} (Target.cuts-below 3) (proj₂ (PTO.id₂-branch 1)))
  zero-one : L.suc (prefix 0) ≼ prefix 1
  zero-one = ≺→s≼ (V.◃→≺ (Op.+-mono (Old.Rows.rows 0) (Fold.nz⊥ Old.two tt tt Old.E (Leg.suc (Old.Rows.c 1)))))

  powers-bound : T₀
  powers-bound = L.lim Old.observation

  finite-powers : powers-bound ≼ stage 2
  finite-powers = ≼-trans {b = Target.at (Ref.finite 3) 1}
    (l≼ (λ n → ≼-trans {b = L.ψ⁰ (Target.finitePower (suc (suc n)))} (Old.bound-observation n)
      (Target.cuts-below (suc (suc n))))) (proj₂ (PTO.id₂-branch 1))

  x-value : ℕ → T₀
  x-value = Self.value
  x-cofinal : Ref.finite 3 ≼ L.lim x-value
  x-cofinal = proj₁ Self.cofinal
  x-ceiling : ∀ n → x-value n ≼ stage (suc (Self.tower-index n))
  x-ceiling n = ≼-trans {b = Old.Rows.Gr (Self.tower-index n)} (Z.mono₀ (Self.bounded n))
    (proj₂ (PTO.id₂-branch (Self.tower-index n)))
  x-base : x-value 0 ≼ stage 2
  x-base = ≼-trans {b = stage 1} (x-ceiling 0) (≼-trans {b = L.suc (stage 1)} (≼-suc (≼-refl _)) (rise 1))

  covers : Ref.finite 3 ≼ L.lim prefix
  covers = Old.standard

```
