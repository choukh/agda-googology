# 有限 Ω 层的严格初段在序数运算下封闭

> 第四层验收。对每个 k≥2，低于 ψ₀(Ωₖ) 的两个树值相乘、取 ω 幂或取上方首个 ε 数，仍严格低于同一层；全部有限次 ε⁺ 的上确界也严格在该层内。证明保留标准名中最外 Ω 的下标。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteOmegaCut where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; s≤s; z≤n)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.EboLeanDef using (T; ψ; natT; HC; _<ᵀ_; hd<; ar<; tl<; lv<; []<)
open import OCF.Align.EboLeanBase using (NF; Ctbl; c∷; c[])
open import OCF.Lean.YiCFMono using (mono<ⁿ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; l≼; ≼lim⁻; ≅→≼; ≼-trans; ≼-refl; ≼-suc; s≼s)
import B12BtboCut as C
import B18Product as P
import B19IdealArithmetic as Ar
import B19IdealProduct as I
import B19IdealPowers as Pow
import B26Names as A
import B26Depth as D
import B26OSparse as S
import B22MovingIndex as E
import B27Epsilon as Lift
import B27Arithmetic as Roof
import B27Threshold as Ord
import B27CutArithmetic as Cut
import B28FFinite as Fin
import B28FHead as Head
import B26CForest as Forest
open import WVOne using (T₀; 𝟏)

name : ℕ → A.Name
name n = A.named (S.collapse (Fin.word (suc n)))
  (Head.normal-response (Head.pure-copies Forest.empty (suc n)) (Fin.R.normal (suc n))) (c∷ c[]) (Fin.R.at n)

index-lt : ∀ {u v q qs xs} → (ψ [] (ψ u q ∷ qs) ∷ xs) <ᵀ S.collapse v → u <ᵀ v
index-lt (hd< (ar< (hd< (lv< p)))) = p

module At (n : ℕ) where
  k = suc (suc n)
  b = name (suc n)
  q = C.finite k
  small : T₀ → Set
  small = λ x → L.suc x ≼ q
  same = Fin.point (suc n)

  pad : L.suc (A.value (name 0)) ≼ A.value b
  pad = mono<ⁿ (A.nt (name 0)) (A.nt b) (A.ct b) (A.hcN (name 0)) (A.hcN b)
    (hd< (ar< (hd< (lv< (tl< []<)))))

  stable : ∀ a (d : 2 ≤ D.height a) → L.suc (A.value a) ≼ A.value b →
    L.suc (A.value (Roof.b (Roof.build a d))) ≼ A.value b
  stable (A.named [] _ c[] _) () _
  stable (A.named (ψ [] [] ∷ xs) _ (c∷ _) _) () _
  stable (A.named (ψ [] (ψ [] u ∷ us) ∷ xs) _ (c∷ _) _) (s≤s ()) _
  stable a@(A.named (ψ [] (ψ (v ∷ vs) u ∷ us) ∷ xs) nf (c∷ ct) h) d lo =
    mono<ⁿ (A.nt next) (A.nt b) (A.ct b) (A.hcN next) (A.hcN b)
      (hd< (ar< (hd< (lv< (index-lt (Ord.strict-name a b lo))))))
    where next = Roof.b (Roof.build a d)

  module Inside = Cut.Generic (A.value b) (name 0) (s≤s (s≤s z≤n)) pad (Cut.approx b) stable

  product : ∀ x y → small x → small y → small (x P.· y)
  product x y px py = ≼-trans {b = A.value b}
    (Inside.product x y (≼-trans {b = q} px (≅→≼ (L.≅-sym same)))
      (≼-trans {b = q} py (≅→≼ (L.≅-sym same)))) (≅→≼ same)

  omega-power : ∀ x → small x → small (Ar.norm x)
  omega-power x px = ≼-trans {b = A.value b}
    (Inside.powω x (≼-trans {b = q} px (≅→≼ (L.≅-sym same)))) (≅→≼ same)

  one : small 𝟏
  one = ≼-trans {b = A.value b} (≼-trans {b = L.suc (A.value (name 0))}
    (s≼s (mono<ⁿ OCF.Align.EboLeanBase.n[] (A.nt (name 0)) (A.ct (name 0))
      (OCF.Align.EboLeanDef.h0 refl) (A.hcN (name 0)) []<)) pad) (≅→≼ same)

  omega : small L.ωᶜ
  omega = ≼-trans {b = L.suc (Ar.norm 𝟏)} (s≼s (P.one-left L.ωᶜ)) (omega-power 𝟏 one)

  power : ∀ x y → small x → small y → small (I.power x y)
  power x y px py = ≼-trans {b = L.suc (Ar.norm (x P.· y))}
    (s≼s (≼-trans {b = I.power (Ar.norm x) y} (Pow.base (Ar.up x) y) (proj₁ (Ar.pow-pow L.ωᶜ x y))))
    (omega-power (x P.· y) (product x y px py))

import Survey.EboPTOFinite as Code
import Survey.W4PTOFinite as Scale
open import OCF.Lean.YiRefTw2 using (Rt)
import W4Block as W

module Branch (m j : ℕ) where
  n = suc m
  head = ψ (natT n) (Code.tower n j)
  root = Code.tower-h n (suc j)
  ceiling = Code.tower-h n (suc (suc j))

  data Same : A.Name → Set where
    keep : ∀ {qs xs} {nt : NF (ψ [] (head ∷ qs) ∷ xs)} {ct : Ctbl xs} {h : HC (ψ [] (head ∷ qs) ∷ xs)}
      → Same (A.named (ψ [] (head ∷ qs) ∷ xs) nt (c∷ ct) h)

  next : ∀ a → Same a → Σ A.Name (λ b → Same b × E.above (A.value a) ≼ A.value b)
  next a (keep {qs} {xs} {nt} {ct} {h}) = Build.roof , keep , proj₂ (proj₂ Build.answer)
    where module Build = Lift.Build _ _ (Code.tower n j) qs xs nt ct h

  within : ∀ a → Same a → L.suc (A.value a) ≼ Rt ceiling
  within a keep = mono<ⁿ (A.nt a) (Code.nf-collapsed n (suc (suc j))) (c∷ c[]) (A.hcN a) ceiling
    (hd< (ar< (hd< (ar< (Code.rise n j)))))

  stages : ∀ x → x ≼ Rt root → ∀ k → Σ A.Name (λ a → Same a × W.iter E.above x k ≼ A.value a)
  stages x low zero = A.named _ (Code.nf-collapsed n (suc j)) (c∷ c[]) root , keep , low
  stages x low (suc k) with stages x low k
  ... | a , holds , p = let b , holds′ , cap = next a holds in b , holds′ ,
    ≼-trans {b = E.above (A.value a)} (E.least (W.iter E.above x k) (E.above (A.value a))
      (≼-trans {b = L.suc (A.value a)} (s≼s p) (E.strict (A.value a))) (proj₁ (E.fix (A.value a)))) cap

  all : ∀ x → x ≼ Rt root → L.lim (W.iter E.above x) ≼ Rt ceiling
  all x low = l≼ λ k → let a , holds , p = stages x low k in ≼-trans {b = L.suc (A.value a)}
    (≼-suc p) (within a holds)

  proper : L.suc (Rt ceiling) ≼ C.finite (suc n)
  proper = ≼-trans {b = Rt (Code.row-h n)}
    (mono<ⁿ (Code.nf-collapsed n (suc (suc j))) (Code.nf-row n) (c∷ c[]) ceiling (Code.row-h n)
      (hd< (ar< (Code.small (Code.tower-indices n (suc (suc j)))))))
    (proj₁ (Scale.scale n))

epsilon-orbit : T₀ → T₀
epsilon-orbit x = L.lim (W.iter E.above x)

orbit-inside : ∀ m x → At.small m x → At.small m (epsilon-orbit x)
orbit-inside m x small = let j , found = ≼lim⁻ {a = x} {f = values} (≼-trans {a = L.suc x} {b = C.finite (suc n)}
                                              {c = L.lim values} small rows)
                         in finish j (≼-trans {b = L.suc x} (≼-suc (≼-refl x)) found)
  where
  n = suc m
  values = λ j → Rt (Code.tower-h n j)
  rows : C.finite (suc n) ≼ L.lim values
  rows = ≼-trans {b = Rt (Code.row-h n)} (proj₂ (Scale.scale n)) (proj₁ (Code.row-sup n))
  finish : ∀ j → x ≼ values j → At.small m (epsilon-orbit x)
  finish j at-j = ≼-trans {b = L.suc (Rt B.ceiling)} (s≼s (B.all x (≼-trans {b = values j} at-j next))) B.proper
    where
    module B = Branch m j
    next : values j ≼ Rt B.root
    next = ≼-trans {b = L.suc (values j)} (≼-suc (≼-refl (values j)))
      (mono<ⁿ (Code.nf-collapsed n j) (Code.nf-collapsed n (suc j)) (c∷ c[])
        (Code.tower-h n j) (Code.tower-h n (suc j)) (hd< (ar< (Code.rise n j))))
```
