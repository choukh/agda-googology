# 在原二层参照上逐项盖住 g

第四层。一次 Ω₁ 分支的对角从任意已保留 Ω₂ 起点的前缀出发，所得折叠值严格增大且对 h 封闭。沿指标迭代这个正层操作给出 g 的逐点上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedCap where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼-trans; ≼-suc; ≼l; l≼; s≼s; ≅→≼; 1≼ψ⁰)
import OCF.Align.BTBOValUp as U
open import WVOne using (T₀; 𝟏)
open import WSLevel using (Ω₁ᴸ)
open import YiLAB7Replay using (Ω₂ᴸ)
import YiLAB10Src as Y
import B12LimitSrc as A
import B12Omega3Ref as R
import B12Omega3Cuts as Cut
import B13Target as P
import B17RefAllSource as Src
import B19OldSource as Sync
import B19RowSecond as Coeff
import B22RowSource as Tail
import B23RKernel as Copy
import B24RRows as Rows
import Survey.W4FourthLiftCeiling as Old
import Survey.W4FourthLiftValue as Index
import Survey.W4RoomDiagonal as H
import Survey.W4RoomDerivative as G

value = λ (p : A.Lev₂) → L.ψ⁰ (P.pass p)
record Base (p : A.Lev₂) : Set where
  constructor base
  field
    regular : p L.≅ p
    start : U.Mh Y.a p
    copies : ∀ left → L.ψ⁰ (left L.+ Coeff.p) ≼ L.ψ⁰ (left L.+ P.pass p)

initial : Base Ω₂ᴸ
initial = base (L.Ω-refl _) (A.Aligned.up A.omega2) (λ _ → ≼-refl _)

extend : ∀ {p} → Base p → Base (Old.more p)
extend {p} b = base (L.add-≅ {σ = L.suc} {σ′ = L.suc} (Base.regular b) (L.Ω-refl _))
  (U.M-add-r {σ = L.suc} Ω₁ᴸ (Base.start b))
  (λ left → ≼-trans {b = L.ψ⁰ (left L.+ P.pass p)} (Base.copies b left) (Old.lead p left))

limit-base : ∀ p → (∀ n → Base (p n)) → Base (L.lim p)
limit-base p good = base (L.l≅ (λ n → Base.regular (good n))) (U.Mlr 0 (Base.start (good 0)))
  (λ left → ≼l 0 (Base.copies (good 0) left))

rise : ∀ p → Base p → L.suc (value p) ≼ value (Old.more p)
rise p b = ≼-trans {b = L.ψ⁰ (P.pass p L.+ Coeff.p)} (Tail.Tail.one (P.pass p) (P.pass-pres rp))
  (≼-trans {b = L.ψ⁰ (P.pass p L.+ P.pass p)} (Base.copies b (P.pass p))
    (≼-trans {b = Row.gain 0 𝟏} (≼l 2 (≼-refl _)) (≼-trans (≼l 0 (≼-refl _)) (≅→≼ (L.≅-sym shape)))))
  where
  rp = Base.regular b
  module Row = Rows.At p rp
  shape = L.≅-trans (L.≅-sym (L.ψ⁰-≅ (Row.from-live (L.Ω-refl _)))) (Row.shape 0)

roll : A.Lev₂ → T₀ → A.Lev₂
roll p L.zero = Old.more p
roll p (L.suc x) = Old.more (roll p x)
roll p (L.lim f) = L.lim (λ i → roll p (f i))

pres : ∀ {p p′ x y} → p L.≅ p′ → x L.≅ y → roll p x L.≅ roll p′ y
pres rp L.z≅ = L.add-≅ {σ = L.suc} {σ′ = L.suc} rp (L.Ω-refl _)
pres rp (L.s≅ d) = L.add-≅ {σ = L.suc} {σ′ = L.suc} (pres rp d) (L.Ω-refl _)
pres rp (L.l≅ f) = L.l≅ (λ n → pres rp (f n))

roll-base : ∀ p → Base p → ∀ x → Base (roll p x)
roll-base p b L.zero = extend b
roll-base p b (L.suc x) = extend (roll-base p b x)
roll-base p b (L.lim f) = limit-base (λ n → roll p (f n)) (λ n → roll-base p b (f n))

above-old : ∀ p → Base p → ∀ t → U.Mh (Old.src (Copy.copy t)) (roll p t)
above-old p b L.zero = U.M-add {σ = R.idσ} (Base.start b) (A.Aligned.up Sync.omega-one)
above-old p b (L.suc t) = U.M-add {σ = R.idσ} (above-old p b t) (A.Aligned.up Sync.omega-one)
above-old p b (L.lim f) = U.Mll (λ j → U.Mlr j (above-old p b (f j)))

block = λ p → L.limᵢ (L.suc L.zero) (roll p)

module Lift (p : A.Lev₂) (b : Base p) where
  v = λ t → value (roll p t)
  r = Base.regular b
  cap = value (block p)

  normal : cap L.≅ L.lim (λ n → R.S.iter v 𝟏 (suc n))
  normal = L.≅-trans (L.ψ⁰-≅ arity) (L.l≅ (λ n → L.ψ⁰-≅ (P.pass-pres (pres r (indices n)))))
    where
    q = λ x → P.pass (roll p x)
    arity : P.pass (block p) L.≅ L.limᵢ (L.suc L.zero) q
    arity = L.lᵢ≅ L.z≅ (λ x y d → P.pass-pres (pres r (L.tr⁻-≅ L.z≅ d)))
    row = λ x → L.ψ (L.suc L.zero) R.idσ (q x)
    indices : ∀ n → R.S.iter row 𝟏 n L.≅ R.S.iter v 𝟏 n
    indices = L.iter-R L._≅_ {G = row} {G′ = v}
      (λ d → L.≅-sym (L.ψ⁰≅ψ {p = L.suc L.zero} {σ = R.idσ} (L.≅-sym (P.pass-pres (pres r d))))) (L.s≅ L.z≅)

  dominates : ∀ x → Index.h x ≼ v x
  dominates x = ≼-trans {b = Old.value x} (Old.indexed x)
    (Cut.sandwich {s = Src.pass (Old.src (Copy.copy x))}
      (Src.pass-down 1 (Old.backward x (Copy.copy x) (≅→≼ (L.≅-sym (Copy.copied x)))))
      (Src.pass-up 1 (above-old p b x))
      (P.pass-pres (Old.pres (L.≅-refl⁰ x))) (P.pass-pres (pres r (L.≅-refl⁰ x))))

  fixed : Index.h cap ≼ cap
  fixed = ≼-trans {b = Index.h (L.lim (λ n → R.S.iter v 𝟏 (suc n)))} (H.monotone (≅→≼ normal))
    (≼-trans {b = L.lim (λ n → R.S.iter v 𝟏 (suc n))}
      (l≼ λ n → ≼l (suc n) (dominates (R.S.iter v 𝟏 (suc n)))) (≅→≼ (L.≅-sym normal)))

  gain : L.suc (value p) ≼ cap
  gain = ≼-trans {b = value (Old.more p)} (rise p b)
    (≼-trans {b = v 𝟏} (≼-trans (≼-suc (≼-refl _)) (rise (Old.more p) (extend b)))
      (≼-trans (≼l 0 (≼-refl _)) (≅→≼ (L.≅-sym normal))))

  ready : Base (block p)
  ready = base (L.lᵢ≅ L.z≅ (λ x y d → pres r d))
    (U.Mir (λ z _ → Base.start (roll-base p b z)))
    (λ left → ≼l 0 (Base.copies (roll-base p b 𝟏) left))

family : T₀ → A.Lev₂
family L.zero = block Ω₂ᴸ
family (L.suc x) = block (family x)
family (L.lim f) = L.lim (λ i → family (f i))

ready : ∀ x → Base (family x)
ready L.zero = Lift.ready Ω₂ᴸ initial
ready (L.suc x) = Lift.ready (family x) (ready x)
ready (L.lim f) = limit-base (λ n → family (f n)) (λ n → ready (f n))

indexed : ∀ x → G.g x ≼ value (family x)
indexed L.zero = G.least L.zero (value (block Ω₂ᴸ)) (1≼ψ⁰ (P.pass (block Ω₂ᴸ))) (Lift.fixed Ω₂ᴸ initial)
indexed (L.suc x) = G.least (G.g x) _ (≼-trans {b = L.suc (value (family x))} (s≼s (indexed x)) (Lift.gain (family x) (ready x)))
  (Lift.fixed (family x) (ready x))
indexed (L.lim f) = l≼ λ n → ≼l n (indexed (f n))
```
