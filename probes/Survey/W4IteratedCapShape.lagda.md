# 二层闭项的零层展开

第四层。两次 Ω₁ 对角的原 src 闭项折叠后同值于明确的可数极限。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedCapShape where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (_,_; proj₁; proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≼-refl; ≼-suc; s≼s; l≼; ≼l; z≼; ≅→≼)
open import OCF.Align.BTBOValBase using (tr₀)
open import WVOne using (T₀; 𝟏)
import B12Omega3Ref as R
import B13Target as P
import Survey.W4IteratedCap as C
import Survey.W4IteratedCapCube as Cube

value = λ x → C.value (C.family x)
wall : T₀
wall = L.lim (λ n → R.S.iter value 𝟏 (suc n))
normal : C.value Cube.level L.≅ wall
normal = L.≅-trans (L.ψ⁰-≅ arity) (L.l≅ (λ n → L.ψ⁰-≅ (P.pass-pres (Cube.regular (indices n)))))
  where
  q = λ x → P.pass (C.family x)
  arity : P.pass Cube.level L.≅ L.limᵢ (L.suc L.zero) q
  arity = L.lᵢ≅ L.z≅ (λ x y d → P.pass-pres (Cube.regular (L.tr⁻-≅ L.z≅ d)))
  row = λ x → L.ψ (L.suc L.zero) R.idσ (q x)
  indices : ∀ n → R.S.iter row 𝟏 n L.≅ R.S.iter value 𝟏 n
  indices = L.iter-R L._≅_ {G = row} {G′ = value}
    (λ d → L.≅-sym (L.ψ⁰≅ψ {p = L.suc L.zero} {σ = R.idσ} (L.≅-sym (P.pass-pres (Cube.regular d))))) (L.s≅ L.z≅)

bridge : tr₀ Cube.source ≈ᵛ wall
bridge = ≼-trans {b = C.value Cube.level} (proj₁ Cube.exact) (≅→≼ normal) ,
         ≼-trans {b = C.value Cube.level} (≅→≼ (L.≅-sym normal)) (proj₂ Cube.exact)

```
