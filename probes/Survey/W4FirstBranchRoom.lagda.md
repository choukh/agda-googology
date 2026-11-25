# ψ₀ψ₃(Ω₂) 的每一枝在目标内可乘 ω

第四层。目标的任意一枝乘 ω 仍由下一枝盖住。故把一列始终有同一枝作上界的实际输出作可数序数和，其值仍严格低于目标。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FirstBranchRoom where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_; replicate)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum.Base using (inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)
open import OCF.Align.EboLeanDef using (T; ψ; _<ᵀ_; _<ᴾ_; []<; hd<; ar<; HC; fsn)
open import OCF.Align.EboLeanBase
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF; trian-fsn)
open import OCF.Align.EboLeanTrian using (t<)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv; tree-≼)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
open import WVOne using (T₀)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼-suc; l≼; s≼s)
import Survey.W4FiniteRaiseBranches as Br
import Survey.W4FirstBranchCut as Cut
import Survey.EboPTOFinite as B
import B18Product as M
import B26PSuffix as V

stage = λ k → Rt (B.tower-h 2 k)
rise : ∀ k → L.suc (stage k) ≼ stage (suc k)
rise k = mono<ⁿ (B.nf-collapsed 2 k) (B.nf-collapsed 2 (suc k)) (c∷ c[]) (B.tower-h 2 k) (B.tower-h 2 (suc k)) (hd< (ar< (B.rise 2 k)))

h : HC (Cut.high 0)
h = Br.Step.lifted 0 0
nf : NF (Cut.high 0)
nf = cl-fsn-NF (B.nf-collapsed 3 2) (Br.count 2) 0
target = Rt h
branch = hω-inv h refl
child = λ k → Rt (branch k)

grows : ∀ k → Cut.orbit 0 k <ᵀ Cut.orbit 0 (suc k)
grows zero = hd< (ar< []<)
grows (suc k) = hd< (ar< (hd< (ar< (grows k))))

-- 两个主项严格有序时，较小主项的任意有限重复均在较大主项之下。
copies-bound : ∀ {a b} (na : NF (ψ [] a ∷ [])) (nb : NF (ψ [] b ∷ [])) →
  (ha : HC (ψ [] a ∷ [])) (hb : HC (ψ [] b ∷ [])) → a <ᵀ b → Rt ha M.· L.ωᶜ ≼ Rt hb
copies-bound {a} {b} na nb ha hb lt = l≼ finite
  where
  p = ψ [] a
  sorted : ∀ n → HdLe p (replicate n p)
  sorted zero = tt
  sorted (suc n) = inj₂ refl
  norm : ∀ n → NF (replicate n p)
  norm zero = n[]
  norm (suc n) = n∷ (nf-hd na) (sorted n) (norm n)
  count : ∀ n → Ctbl (replicate n p)
  count zero = c[]
  count (suc n) = c∷ (count n)
  cert = λ n → hc (norm n) (count n)
  before : ∀ n → replicate n p <ᵀ (ψ [] b ∷ [])
  before zero = []<
  before (suc _) = hd< (ar< lt)
  finite : ∀ n → Rt ha M.· L.natᶜ n ≼ Rt hb
  finite n = ≼-trans {b = Rt (cert 1) M.· L.natᶜ n}
    (M.mono (tree-≼ refl ha (cert 1)) (≼-refl _))
    (≼-trans {b = Rt (cert n)} (proj₂ (V.copies p cert n))
      (≼-trans (≼-suc (≼-refl _)) (mono<ⁿ (norm n) nb (c∷ c[]) (cert n) hb (before n))))

next : ∀ k → child k M.· L.ωᶜ ≼ child (suc k)
next k = ≼-trans {b = Rt (q k) M.· L.ωᶜ}
  (M.mono (tree-≼ (Cut.high-branch 0 k) (branch k) (q k)) (≼-refl _))
  (≼-trans {b = Rt (q (suc k))} (copies-bound (normal k) (normal (suc k)) (q k) (q (suc k)) (hd< (ar< (grows k))))
    (tree-≼ (sym (Cut.high-branch 0 (suc k))) (q (suc k)) (branch (suc k))))
  where
  q = λ k → subst HC (Cut.high-branch 0 k) (branch k)
  normal = λ k → subst NF (Cut.high-branch 0 k) (cl-fsn-NF nf refl k)

room : ∀ k → L.suc (child k M.· L.ωᶜ) ≼ target
room k = ≼-trans {b = L.suc (child (suc k))} (s≼s (next k))
  (mono<ⁿ (cl-fsn-NF nf refl (suc k)) nf (c∷ c[]) (branch (suc k)) h (t< (trian-fsn nf refl (suc k))))
```
