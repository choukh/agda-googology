# 首次回灌内的正层指数列各自的原 EBO 名字

第四层。令 q₀=Ω₁、qₙ₊₁=ψ₁(qₙ)。原项 ψ₀ψ₂(Ω₂+ψ₁(Ω₂)) 的第 n 枝恰给 ψ₀ψ₂(Ω₂+qₙ₊₁)。第二个这样的原可数标准项已经盖住统一上界 c。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LeadCapNames where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to pair)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.Align.EboLeanDef using (T; ψ; natT; Ωt; fsn; γT; HC)
open import OCF.Align.EboLeanBase using (NF; c∷; c[]; lt→<)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
open import OCF.Lean.YiRefTw2 using (Rt)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼; s≼s)
open import OCF.Align.BTBOValBase using (tr₀)
open import WVOne using (𝟏)
open import WSLevel using (Ω₁ᴸ)
import B13Target as P
import B14RefFixed as F
import B15RefAlgebra as A
import B24RRows as Q
import Survey.W4IteratedCap as C
import Survey.W4IteratedCapCube as Cube
import Survey.W4PTOFirstQuery as S
import Survey.W4OriginalIteratedBound as Old
import Survey.W4LeadCapPositive as Cap
import Survey.W4LeadCapExit as Exit
import Survey.W4LeadCapBranch as Z
open S.Names using (At; child; d)

i = natT 1
j = natT 2
term = λ t → d 0 (d 2 (ψ j [] ∷ t))
q : ℕ → T
q zero = Ωt i
q (suc n) = d 1 (q n)
row = term (d 1 (Ωt j))

start : At (fsn Old.next-branch 0) (Q.gain 1 𝟏)
start = child refl (pair Old.next-h (L.≅-trans Cap.branch (Q.shape 1))) 0

picked = child refl (child refl (child refl start 1) 0) 0
height : At (term (d 1 (d 2 (natT 1)))) (Cap.fold (A.H 𝟏 Ω₁ᴸ))
height = pair (proj₁ picked) (L.≅-trans (proj₂ picked) (Cap.cong (A.true-coeff 𝟏)))

named : At row (Cap.fold (A.Γ Ω₁ᴸ))
named = child refl height 1
indices : ∀ n → γT (Ωt j) i n ≡ q n
indices zero = refl
indices (suc n) = cong (d 1) (indices n)
shape : ∀ n → fsn row n ≡ term (q (suc n))
shape n = cong (λ t → term (d 1 t)) (indices n)

stage : ∀ n → At (term (q (suc n))) (Cap.fold (Cap.stage (suc n)))
stage n = subst (λ t → At t (Cap.fold (Cap.stage (suc n)))) (shape n) (child refl named n)

row-nf : NF row
row-nf = cl-fsn-NF (cl-fsn-NF (cl-fsn-NF (cl-fsn-NF (cl-fsn-NF Old.next-nf refl 0) refl 1) refl 0) refl 0) refl 1
stage-nf : ∀ n → NF (term (q (suc n)))
stage-nf n = subst NF (shape n) (cl-fsn-NF row-nf refl n)
inside : tr₀ Cube.source ≼ Rt (proj₁ (stage 1))
inside = ≼-trans {b = C.value Cube.level} (proj₁ Cube.exact) (≼-trans {b = Cap.fold (Cap.stage 2)} Exit.upper
  (≅→≼ (L.≅-sym (proj₂ (stage 1)))))

below-first : L.suc (Rt (proj₁ (stage 1))) ≼ Z.v 1
below-first = mono<ⁿ (stage-nf 1) (Z.normal 1) (c∷ c[]) (proj₁ (stage 1)) (Z.cert 1) (lt→< _ _ refl)
```
