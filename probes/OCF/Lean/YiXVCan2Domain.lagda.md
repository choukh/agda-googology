# YiXV: 实际种子与内链的模拟
> 验收文件。档位：编译定理。实际 β₂、Third.γ₂ 及其后内链所有项已构造模拟推导；此处只交域，读回值界由 YiXVCan2Sem/Ceiling 给出。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Domain where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (self; ins)
open import OCF.Lean.YiLegFold
import OCF.Align.Level as L
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVRef2Add as A
import OCF.Lean.YiXVThird as T
import OCF.Lean.YiXVLocal as I
import OCF.Lean.YiXVAnchor as H
import OCF.Lean.YiXVWorld3 as W3
import OCF.Lean.YiXVCanTau as Tau
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVCan2Mix as M
import OCF.Lean.YiXVCan2Add as CA
import OCF.Lean.YiXVCan2Psi as P
import OCF.Lean.YiXVCan2Gamma as G
import OCF.Lean.YiXVCan2Rel as S
import OCF.Lean.YiXVCan2Lift as K
import OCF.Lean.YiXVCan2Self as SF
import OCF.Lean.YiXVCan2Embed as E

module U = S.Rel I.D1

ΩU : U.U (Ωt (suc (suc zero))) (F.Ω₂ L.+ F.Ω₂)
ΩU = U.un₁ (λ a X Y gx gy o ha ca q → U.uu C.Gd-Ω₂ U.uz gy (I.U.uw (O.gs gx) (I.U.us ha) q) ca)

twoΩ-base : C.Le (F.Ω₂ L.+ F.Ω₂) (P.B O.Ω₁)
twoΩ-base = C.pack (CA.good C.Gd-Ω₂ C.Gd-Ω₂) (P.goodB O.Gd-Ω) (C.aa₀
  (C.pack (CA.good C.Gd-Ω₂ C.Gd-Ω₂) (C.gl (P.good-iter C.Gd-Ω₂)) (C.lr 2 (C.refl (CA.good C.Gd-Ω₂ C.Gd-Ω₂)))))

twoΩ : C.Le (F.Ω₂ L.+ F.Ω₂) (P.Ψ F.Ω₂)
twoΩ = C.pack (CA.good C.Gd-Ω₂ C.Gd-Ω₂) (P.good C.Gd-Ω₂) (C.aa₁ (λ z hz → C.trans twoΩ-base
  (P.monoB (P.goodB O.Gd-Ω) (P.goodB (Tau.good (Tau.start-good hz))) (Tau.floor (Tau.start-floor hz)))))

ΩψU : U.U (Ωt (suc (suc zero))) (P.Ψ F.Ω₂)
ΩψU = U.uw ΩU twoΩ

Z : F.T₂
Z = L.add F.Ω₂ A.σ₁ (O.Ω₁ L.+ O.Ω₁)
gZ : C.Gd Z
gZ = M.good₁ C.Gd-Ω₂ (O.Gd-+ O.Gd-Ω O.Gd-Ω)

βU : U.U T.β₂ (P.Ψ Z)
βU = K.Lift.upc I.D1 (Ωt-nz (suc (suc zero))) C.Gd-Ω₂ ΩψU (O.Gd-+ O.Gd-Ω O.Gd-Ω) I.ΩU H.Ω-closed

seedβ : U.U T.β₂ (P.Ψ (Z L.+ F.Ω₂))
seedβ = U.uw βU (P.mono (CA.rightE (C.refl gZ) C.Gd-Ω₂ (CA.good gZ C.Gd-Ω₂)))

Q : Base (suc (suc zero))
Q = dS (suc (suc zero)) tt tt T.B31 zero
module SeedFold = SF.Fold I.D1 Q Z gZ T.β₂ T.nβ₂ seedβ

γU₀ : U.U T.γ₂ (P.Ψ (Z L.+ (F.Ω₂ L.+ F.Ω₂)))
γU₀ = SeedFold.result (CA.good C.Gd-Ω₂ C.Gd-Ω₂) ΩU

Z≤Γ₂ : C.Le Z (G.Γ 2)
Z≤Γ₂ = C.trans (CA.plus C.Ω₂-refl E.sample)
  (C.trans (CA.plus C.Ω₂-refl twoΩ) (G.step 0 C.Ω₂-refl))

γU : U.U T.γ₂ (G.Γ 5)
γU = U.uw γU₀ (P.mono (C.trans
  (CA.plus Z≤Γ₂ (C.trans twoΩ (C.trans (G.next 1) (G.next 2))))
  (G.step 2 (C.refl (G.good 2)))))

seedγ : U.U T.γ₂ (P.Ψ (G.Γ 4 L.+ F.Ω₂))
seedγ = U.uw γU (P.mono (CA.rightE (C.refl (G.good 4)) C.Gd-Ω₂ (CA.good (G.good 4) C.Gd-Ω₂)))
module ChainFold = SF.Fold I.D1 W3.E2 (G.Γ 4) (G.good 4) T.γ₂
  (ns T.B3 (suc (suc zero)) (ins self)) seedγ

c : ℕ → Tr (suc (suc zero))
c = iter (λ x → ChainFold.χ (suc x)) zero
idx : ℕ → ℕ
idx zero = 4
idx (suc n) = suc (suc (suc (idx n)))
floor : ∀ n → C.Le (G.Γ 4) (G.Γ (idx n))
floor zero = C.refl (G.good 4)
floor (suc n) = C.trans (floor n) (C.trans (G.next (idx n)) (C.trans (G.next (suc (idx n))) (G.next (suc (suc (idx n))))))

bounds : ∀ n → U.U (c n) (G.Γ (idx n))
bounds zero = U.uw U.uz (P.base (G.Γ 3) (G.good 4))
bounds (suc n) = U.uw (ChainFold.result (C.gs (G.good (idx n))) (U.us (bounds n)))
  (P.mono (C.trans (CA.plus (floor n) (G.inv (idx n))) (G.step (idx n) (C.refl (G.good (idx n))))))

second : U.U (c 1) (G.Γ 7)
second = bounds 1
```
