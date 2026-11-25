# H 不动点枚举的首个不动点有一个正层上界

第四层。沿参照前缀从 Ω₂+Ω₁ 开始每步加一份 Ω₁，其零层读值支配 H 不动点枚举的相应项。对角比较使用这个前缀自己的可数分支。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FourthLiftCeiling where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≼-refl; s≼s; l≼; ≼l; ≅→≼; z≼)
open import OCF.Align.Value using (≼i; i≼; ≼u; u≼)
open import OCF.Align.BTBOValBase using (tr₀)
import OCF.Align.BTBOValUp as U
import OCF.Align.BTBOValDn as D
open import WVOne using (T₀; 𝟏)
open import WSLevel using (Ω₁ᴸ)
open import YiLAB7Replay using (Ω₂ᴸ)
import YiLAB10Src as Y
import B12LimitSrc as A
import B12Omega3Ref as R
import B12Omega3Cuts as Cut
import B13Target as P
import B17RefAllSource as Src
import B15RefSource as Old
import B19OldSource as Sync
import B19RowSecond as Coeff
import B22RowSource as Tail
import B23RKernel as Copy
import B24ROrbit as O
import B24RKernel as H
import B24RRows as Rows
import B24RExit as Exit
import Survey.W4PTOSeededQuery as N
import Survey.W4FourthLiftValue as I
import Survey.W4RoomDiagonal as Diag

more : A.Lev₂ → A.Lev₂
more p = L.add p L.suc Ω₁ᴸ
prefix : T₀ → A.Lev₂
prefix L.zero = more Ω₂ᴸ
prefix (L.suc x) = more (prefix x)
prefix (L.lim f) = L.lim (λ i → prefix (f i))

pres : ∀ {x y : T₀} → x L.≅ y → prefix x L.≅ prefix y
pres L.z≅ = L.add-≅ {σ = L.suc} {σ′ = L.suc} (L.Ω-refl _) (L.Ω-refl _)
pres (L.s≅ p) = L.add-≅ {σ = L.suc} {σ′ = L.suc} (pres p) (L.Ω-refl _)
pres (L.l≅ f) = L.l≅ (λ n → pres (f n))

q = λ x → P.pass (prefix x)
value = λ x → L.ψ⁰ (q x)

lead : ∀ p left → L.ψ⁰ (left L.+ P.pass p) ≼ L.ψ⁰ (left L.+ P.pass (more p))
lead p left = ≼l 0 (≼l 1 (≼-refl _))
copies : ∀ x left → L.ψ⁰ (left L.+ Coeff.p) ≼ L.ψ⁰ (left L.+ q x)
copies L.zero left = lead Ω₂ᴸ left
copies (L.suc x) left = ≼-trans {b = L.ψ⁰ (left L.+ q x)} (copies x left) (lead (prefix x) left)
copies (L.lim f) left = ≼l 0 (copies (f 0) left)

base : ∀ x → U.Mh Y.a (prefix x)
base L.zero = U.M-add-r {σ = L.suc} Ω₁ᴸ (A.Aligned.up A.omega2)
base (L.suc x) = U.M-add-r {σ = L.suc} Ω₁ᴸ (base x)
base (L.lim f) = U.Mlr 0 (base (f 0))

module Step (x : T₀) where
  p = prefix x
  rp = pres (L.≅-refl⁰ x)
  module Aₓ = Rows.At p rp
  point = Aₓ.gain 0
  E = value (L.suc x)
  same : Aₓ.node 0 L.≅ E
  same = L.ψ⁰-≅ (Aₓ.from-live (L.Ω-refl _))
  shape : E L.≅ L.lim (λ n → Aₓ.iterate 0 (suc n))
  shape = L.≅-trans (L.≅-sym same) (Aₓ.shape 0)
  bigger : ∀ t → U.Mh (H.src-a (Copy.copy t)) (L.add p (λ i → L.suc (L.suc i)) t)
  bigger L.zero = base x
  bigger (L.suc t) = U.Ms (bigger t)
  bigger (L.lim f) = U.Mll (λ n → U.Mlr n (bigger (f n)))
  dominates : ∀ t → H.H t ≼ point t
  dominates t = Cut.sandwich {s = Src.pass (H.src-a (Copy.copy t))}
    (Src.pass-down 1 (A.Aligned.dn (H.coded t))) (Src.pass-up 1 (bigger t))
    (H.regular (L.≅-refl⁰ t)) (Aₓ.respects (Aₓ.regular 0 (L.≅-refl⁰ t)))
  fixed : H.H E ≼ E
  fixed = ≼-trans {b = H.H (L.lim (λ n → Aₓ.iterate 0 (suc n)))}
    (H.monotone {E} {_} (≅→≼ shape))
    (≼-trans {b = L.lim (λ n → Aₓ.iterate 0 (suc n))}
      (l≼ (λ n → ≼l (suc n) (dominates (Aₓ.iterate 0 (suc n))))) (≅→≼ (L.≅-sym shape)))
  gain : L.suc (value x) ≼ E
  gain = ≼-trans {b = L.ψ⁰ (q x L.+ Coeff.p)} (Tail.Tail.one (q x) (P.pass-pres rp))
    (≼-trans {b = L.ψ⁰ (q x L.+ q x)} (copies x (q x))
      (≼-trans {b = point 𝟏} (≼l 2 (≼-refl _)) (≼-trans (≼l 0 (≼-refl _)) (≅→≼ (L.≅-sym shape)))))

indexed : ∀ x → I.h x ≼ value x
indexed L.zero = ≼-trans {b = O.D} (proj₂ I.start) (≅→≼ Exit.input)
indexed (L.suc x) = N.least (I.h x) (value (L.suc x)) (≼-trans (s≼s (indexed x)) (Step.gain x)) (Step.fixed x)
indexed (L.lim f) = l≼ λ n → ≼l n (indexed (f n))

square : A.Lev₂
square = L.limᵢ (L.suc L.zero) prefix

bound : T₀
bound = L.ψ⁰ (P.pass square)
normal : bound L.≅ L.lim (λ n → R.S.iter value 𝟏 (suc n))
normal = L.≅-trans (L.ψ⁰-≅ arity) (L.l≅ (λ n → L.ψ⁰-≅ (P.pass-pres (pres (indices n)))))
  where
  arity : P.pass square L.≅ L.limᵢ (L.suc L.zero) q
  arity = L.lᵢ≅ L.z≅ (λ x y d → P.pass-pres (pres (L.tr⁻-≅ L.z≅ d)))
  row = λ x → L.ψ (L.suc L.zero) R.idσ (q x)
  indices : ∀ n → R.S.iter row 𝟏 n L.≅ R.S.iter value 𝟏 n
  indices = L.iter-R L._≅_ {G = row} {G′ = value}
    (λ d → L.≅-sym (L.ψ⁰≅ψ {p = L.suc L.zero} {σ = R.idσ} (L.≅-sym (P.pass-pres (pres d))))) (L.s≅ L.z≅)

ceiling : Diag.fixedPoint ≼ bound
ceiling = ≼-trans {b = L.lim (λ n → R.S.iter value 𝟏 (suc n))}
  (l≼ (λ { zero → z≼ ; (suc n) → ≼l n (each (suc n)) })) (≅→≼ (L.≅-sym normal))
  where
  each : ∀ n → Diag.stages n ≼ R.S.iter value 𝟏 n
  each zero = z≼
  each (suc n) = ≼-trans {b = I.h (R.S.iter value 𝟏 n)} (Diag.monotone (each n)) (indexed (R.S.iter value 𝟏 n))

module S = Src.S
module B = Src.B
unit = S.↑ B.zero (S.Ω Old.one)
src : S.Ord₀ → A.Src₂
src S.zero = Y.a S.+ unit
src (S.suc x) = src x S.+ unit
src (S.lim f) = S.lim (λ n → src (f n))

start = A.plus A.omega2 Sync.omega-one
small-up : ∀ y → U.Mh (src S.zero) (prefix y)
small-up L.zero = A.Aligned.up start
small-up (L.suc y) = U.M-add-r {σ = L.suc} Ω₁ᴸ (small-up y)
small-up (L.lim f) = U.Mlr 0 (small-up (f 0))
small-down : ∀ x → D.Dn (prefix L.zero) (src x)
small-down S.zero = A.Aligned.dn start
small-down (S.suc x) = D.Dn-add-r unit (small-down x)
small-down (S.lim f) = D.Rlr 0 (small-down (f 0))

toward : ∀ s y → tr₀ s ≼ y → U.Mh (src s) (prefix y)
toward (S.limᵢ () f) y d
toward S.zero y z≼ = small-up y
toward (S.suc s) (L.suc y) (s≼s d) = U.M-add {σ = R.idσ} (toward s y d) (A.Aligned.up Sync.omega-one)
toward s (L.lim g) (≼l n d) = U.Mlr n (toward s (g n) d)
toward (S.lim f) y (l≼ d) = U.Mll (λ n → toward (f n) y (d n))
toward s _ (≼i {p = ()} _ _ _)
toward s _ (≼u {r = ()} _)
backward : ∀ x s → x ≼ tr₀ s → D.Dn (prefix x) (src s)
backward x (S.limᵢ () f) d
backward L.zero s z≼ = small-down s
backward (L.suc x) (S.suc s) (s≼s d) = D.Dn-add {σ = R.idσ} (backward x s d) (A.Aligned.dn Sync.omega-one)
backward (L.lim f) s (l≼ d) = D.Rll (λ n → backward (f n) s (d n))
backward x (S.lim f) (≼l n d) = D.Rlr n (backward x (f n) d)
backward _ s (i≼ {p = ()} _)
backward _ s (u≼ {r = ()} _)

src-square : A.Src₂
src-square = S.limᵢ (B.suc B.zero) src
aligned : A.Aligned src-square square
aligned = A.aligned (U.Mii L.z≅ (λ s y d → toward s y (U.Mh→≼ d)))
                    (D.Rii L.z≅ (λ x s d → backward x s (D.Dn→≼ d)))
                    (L.lᵢ≅ L.z≅ (λ _ _ d → pres d))
source = S.ψ₀ (Src.pass src-square)
bridge : tr₀ source ≈ᵛ bound
bridge = A.fold (Exit.passed aligned)
source-ceiling : Diag.fixedPoint ≼ tr₀ source
source-ceiling = ≼-trans ceiling (proj₂ bridge)
```
