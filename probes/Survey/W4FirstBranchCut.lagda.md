# ψ₀ψⱼ(Ω₁) 的全部前驱升层到哪里

第四层。对每个 j≥2，提升 ψ₀ψⱼ(Ω₁) 的全部严格前驱，所取上确界恰为 ψ₀ψⱼ₊₁(Ω₁)。这个值是直接提升端点 ψ₀ψⱼ₊₁(Ω₂) 的第零枝。取 j=2 正好比较 b₂[0] 与本轮要覆盖的 b₃[0]。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FirstBranchCut where

open import Data.Nat.Base using (ℕ; zero; suc; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import OCF.Align.EboLeanDef using (T; ψ; natT; Ωt; _<ᵀ_; hd<; lv<; tl<; ar<; []<; HC; cof; cω; fsn; fsT; γT)
open import OCF.Align.EboLeanBase
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF)
open import OCF.Align.TightValBase using (s≼-irrefl)
open import Data.Empty using (⊥)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv; tree-≼)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; l≼)
import Survey.EboPTOFinite as B
import Survey.W4FiniteRaiseCut as C
import Survey.W4FiniteRaiseNames as R
import Survey.W4FiniteRaiseBranches as Br
import B26PSuffix as V

j = λ n → suc (suc n)
letter = λ n → Br.d (j n)
low = λ n → Br.d 0 (letter n (Ωt (natT 1)))
high = λ n → Br.d 0 (letter (suc n) (Ωt (natT 2)))
step = λ n z → Br.d 0 (letter n z)

seq : ℕ → ℕ → T
seq n zero = natT 1
seq n (suc k) = step n (seq n k)

left : ∀ n k → γT (letter n (Ωt (natT 1))) [] k ≡ seq n k
left n zero = refl
left n (suc k) = cong (step n) (left n k)

low-branch : ∀ n k → fsn (low n) k ≡ seq n (suc k)
low-branch n k = left n (suc k)

shift : ∀ n k → R.raise (seq n k) ≡ seq (suc n) k
shift n zero = refl
shift n (suc k) = cong (step (suc n)) (shift n k)

orbit : ℕ → ℕ → T
orbit n zero = Ωt (natT 1)
orbit n (suc k) = Br.d 1 (letter (suc n) (orbit n k))

right : ∀ n k → γT (letter (suc n) (Ωt (natT 2))) (natT 1) k ≡ orbit n k
right n zero = refl
right n (suc k) = cong (λ z → Br.d 1 (letter (suc n) z)) (right n k)

high-branch : ∀ n k → fsn (high n) k ≡ step (suc n) (orbit n k)
high-branch n k = cong (step (suc n)) (right n k)

endpoint : ∀ n → R.raise (low n) ≡ high n
endpoint n = refl
first : ∀ n → fsn (high n) 0 ≡ low (suc n)
first n = refl

before : ∀ n {t} → t <ᵀ low n → R.raise t <ᵀ low (suc n)
before n = C.under-d 0 (C.under-d (j n) C.below-unit)

standard : ∀ n → NF (low n)
standard n = nf-ψ n[] (nf-ψ (B.nf-num (j n)) (nf-Ω (B.nf-num 1)) guard) outer
  where
  guard : GB (natT (j n)) (Ωt (natT 1)) (Ωt (natT 1))
  guard (gp h) rewrite C.card-support 1 h = []<
  guard (gtl ())
  outer : GB [] (letter n (Ωt (natT 1))) (letter n (Ωt (natT 1)))
  outer (gp (gh _)) = hd< (lv< (tl< []<))
  outer (gp (gw _ h)) rewrite B.num-support (j n) h = []<
  outer (gp (gc _ (gp h))) rewrite C.card-support 1 h = []<
  outer (gp (gc _ (gtl ())))
  outer (gtl ())

opaque
  cert : ∀ n → HC (low n)
  cert n = hc (standard n) (c∷ c[])

seq< : ∀ n k → seq n (suc k) <ᵀ low n
seq< n k = hd< (ar< (hd< (ar< (small k))))
  where
  small : ∀ m → seq n m <ᵀ Ωt (natT 1)
  small zero = hd< (lv< []<)
  small (suc _) = hd< (lv< []<)

row-above : ∀ n → low n <ᵀ B.row (j n)
row-above n = hd< (ar< (hd< (lv< (B.numeral-strict (s≤s ≤-refl)))))

strict : ∀ n {t} (nt : NF t) (ct : Ctbl t) → t <ᵀ low n → (h : HC (R.raise t)) →
  L.suc (Rt h) ≼ Rt (cert (suc n))
strict n nt ct lt h = mono<ⁿ (R.normal (B.recover (j n) nt ct (<ᵀ-trans lt (row-above n))) nt)
  (standard (suc n)) (c∷ c[]) h (cert (suc n)) (before n lt)


least : ∀ n {y : L.Ordᶜ L.zero} →
  (∀ t → NF t → Ctbl t → t <ᵀ low n → (h : HC (R.raise t)) → Rt h ≼ y) →
  Rt (cert (suc n)) ≼ y
least n {y} upper = ≼-trans {b = L.lim (λ k → Rt (child k))}
  (proj₁ (V.limit parent refl (λ k → Rt (child k)) (λ k → V.same refl (child k) (child k))))
  (l≼ point)
  where
  parent = cert (suc n)
  child = hω-inv parent refl
  point : ∀ k → Rt (child k) ≼ y
  point k = ≼-trans {b = Rt h} (tree-≼ eq (child k) h)
    (upper (seq n (suc k)) (subst NF (low-branch n k) (cl-fsn-NF (standard n) refl k))
      (c∷ c[]) (seq< n k) h)
    where
    eq = trans (low-branch (suc n) k) (sym (shift n (suc k)))
    h = subst HC eq (child k)

gap : ∀ n (h : HC (high n)) → L.suc (Rt (cert (suc n))) ≼ Rt h
gap n h = mono<ⁿ (standard (suc n))
  (R.normal (B.recover (j n) (standard n) (c∷ c[]) (row-above n)) (standard n))
  (c∷ c[]) (cert (suc n)) h (hd< (ar< (hd< (ar< (hd< (lv< (tl< []<)))))))

miss : ∀ n (h : HC (high n)) → Rt h ≼ Rt (cert (suc n)) → ⊥
miss n h p = s≼-irrefl (Rt (cert (suc n))) (≼-trans (gap n h) p)

source : fsn (Br.b 1) 0 ≡ low 0
source = refl
demand : fsn (Br.b 2) 0 ≡ high 0
demand = refl
```
