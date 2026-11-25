# 两次塌缩在一切正前驱层的基本列升层

第四层。对 j≥2 以及每个 k，bⱼ₊₁ 的第 k 枝就是把 bⱼ 的第 k 枝的每个正下标提升一级。因而实证 bⱼ₊₁ 的值只需覆盖这列提升后的返回，各枝可选不同的实际地址。j=1 时首枝就出现严格差异。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteRaiseBranches where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.EboLeanDef using (T; ψ; natT; sucT; Ωt; γT; cof; cΩ; cω; fsT; fsn; HC; _<ᵀ_; []<; hd<; lv<; ar<)
open import OCF.Align.EboLeanBase using (cmpᵀ-refl; c∷; c[])
open import OCF.Align.EBO using (cof-natT; pred-natT)
open import OCF.Align.Translate using (sucT-natT)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF; Ctbl-fsn; trian-fsn)
open import OCF.Align.EboLeanTrian using (t<)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv; tree-≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; s≼s; ≼-suc; ≼-refl; l≼)
import B26PSuffix as V
import Survey.W4RouteTests as A
import Survey.W4FixedDepth as F
import Survey.EboPTOFinite as B
import Survey.W4FiniteRaiseNames as R
import B17CellNext as Feedback
import B12BtboCut as Cut
import Survey.W4PTOFinite as Named

d = λ i t → ψ (natT i) t ∷ []
inner = λ n → d (suc n) (Ωt (natT (suc n)))
b = λ n → B.collapsed (suc n) 2

reg : ∀ n → cof (Ωt (natT (suc n))) ≡ cΩ (natT n)
reg n rewrite cof-natT n | pred-natT n = refl

reg-at : ∀ n x → fsT (Ωt (natT (suc n))) x ≡ x
reg-at n x rewrite cof-natT n = refl

pass : ∀ n → cof (inner n) ≡ cΩ (natT n)
pass n rewrite reg n | sucT-natT n | cmpᵀ-refl (natT (suc n)) = refl

entry : ∀ n x → fsT (inner n) x ≡ d (suc n) x
entry n x rewrite reg n | sucT-natT n | cmpᵀ-refl (natT (suc n)) | reg-at n x = refl

count : ∀ n → cof (b n) ≡ cω
count n rewrite pass n | sucT-natT n = refl

orbit : ℕ → ℕ → T
orbit n zero = Ωt (natT n)
orbit n (suc k) = d n (d (suc n) (orbit n k))

chain : ∀ n k → γT (inner n) (natT n) k ≡ orbit n k
chain n zero = refl
chain n (suc k) = cong (d n) (trans (entry n _) (cong (d (suc n)) (chain n k)))

branch : ∀ n k → fsn (b n) k ≡ d 0 (d (suc n) (orbit n k))
branch n k rewrite pass n | sucT-natT n =
  cong (d 0) (trans (entry n _) (cong (d (suc n)) (chain n k)))

shift-orbit : ∀ n k → R.raise (orbit (suc n) k) ≡ orbit (suc (suc n)) k
shift-orbit n zero = refl
shift-orbit n (suc k) = cong (λ z → d (suc (suc n)) (d (suc (suc (suc n))) z)) (shift-orbit n k)

shift : ∀ n k → R.raise (fsn (b (suc n)) k) ≡ fsn (b (suc (suc n))) k
shift n k = trans (cong R.raise (branch (suc n) k))
  (trans (cong (λ z → d 0 (d (suc (suc (suc n))) z)) (shift-orbit n k)) (sym (branch (suc (suc n)) k)))

first-gap : R.raise (fsn (b 0) 0) <ᵀ fsn (b 1) 0
first-gap = hd< (ar< (hd< (ar< (hd< (lv< []<)))))

module Step (n : ℕ) where
  i = suc n
  parent = B.tower-h (suc (suc i)) 2
  child = hω-inv parent (count (suc i))
  lifted : ∀ k → HC (R.raise (fsn (b i) k))
  lifted k = subst HC (sym (shift n k)) (child k)

  exact : F.sample (suc i) ≈ᵛ L.lim (λ k → Rt (lifted k))
  exact = V.limit parent (count (suc i)) (λ k → Rt (lifted k))
    (λ k → V.same (sym (shift n k)) (child k) (lifted k))

  hits = ∀ k → Σ ℕ (λ m → L.suc (Rt (lifted k)) ≼ A.c m)

  consume : hits → F.sample (suc i) ≼ A.Y
  consume add = ≼-trans (proj₁ exact) (l≼ λ k → ≼-trans (≼-suc (≼-refl _))
    (≼-trans (proj₂ (add k)) (Feedback.actual (proj₁ (add k)) 0)))

  extract : F.sample (suc i) ≼ A.Y → hits
  extract pay k = A.cross (Rt (lifted k)) (≼-trans {b = F.sample (suc i)}
    (≼-trans {b = L.suc (Rt (child k))} (s≼s (tree-≼ (shift n k) (lifted k) (child k)))
      (mono<ⁿ (cl-fsn-NF nf (count (suc i)) k) nf (c∷ c[]) (child k) parent (t< (trian-fsn nf (count (suc i)) k)))) pay)
    where nf = B.nf-collapsed (suc (suc i)) 2

positive : ∀ n k → [] <ᵀ orbit n k
positive n zero = []<
positive n (suc k) = []<

above-row : ∀ n k → B.row n <ᵀ fsn (b n) k
above-row n k = subst (B.row n <ᵀ_) (sym (branch n k))
  (hd< (ar< (hd< (ar< (positive n k)))))

row-into-branch : ∀ n k (h : HC (fsn (b n) k)) → L.suc (Cut.finite (suc n)) ≼ Rt h
row-into-branch n k h = ≼-trans {b = L.suc (Rt (B.row-h n))} (s≼s (proj₂ (Named.scale n)))
  (mono<ⁿ (B.nf-row n) (cl-fsn-NF (B.nf-collapsed (suc n) 2) (count n) k)
    (Ctbl-fsn (c∷ c[]) (count n) k) (B.row-h n) h (above-row n k))

-- 升层前的全部原枝共用实付地址 1。升层后即使第零枝也严格越过 ψ₀(Ω₃)。
original-paid : ∀ k (h : HC (fsn (b 1) k)) → L.suc (Rt h) ≼ A.c 1
original-paid k h = ≼-trans {b = F.sample 1}
  (mono<ⁿ (cl-fsn-NF nf (count 1) k) nf (c∷ c[]) h (B.tower-h 2 2) (t< (trian-fsn nf (count 1) k)))
  (≼-trans (≼-suc (≼-refl _)) F.second)
  where nf = B.nf-collapsed 2 2

third-demand : ∀ k → L.suc (Cut.finite 3) ≼ Rt (Step.lifted 0 k)
third-demand k = ≼-trans {b = Rt (Step.child 0 k)} (row-into-branch 2 k (Step.child 0 k))
  (tree-≼ (sym (shift 0 k)) (Step.child 0 k) (Step.lifted 0 k))
```
