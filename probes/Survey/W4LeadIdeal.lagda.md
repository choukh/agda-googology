# 固定首主项的精确上确界

第四层，无条件。令 A=Ω₂+Ω₁、P=ψ₂(A)。原标准项 ψ₀(P+s) 的上确界是 ψ₀(ψ₂(A+1))。其第 n 枝只需 n 份 P，任意后缀所需份数有显式上界。[先前的严格上界](W4OriginalIteratedBound.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LeadIdeal where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_; length; replicate)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)
open import OCF.Align.EboLeanDef using (T; PT; Ωt; natT; ψ; HC; _<ᵀ_; hd<; tl<; ar<; []<; cof; cω; fsn)
open import OCF.Align.EboLeanBase
open import OCF.Align.EboLeanClosure using (cl-fsn-NF)
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Lean.YiRefTw2 using (Rt; tree-≼; hω-inv)
open import OCF.Lean.YiMENote using (fsnψ1; fsnψω)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≼-refl; ≼-suc; l≼; ≼l)
import Survey.EboPTOFinite as B
import Survey.W4OriginalIteratedBound as Old
import B26PSuffix as S

card : ℕ → PT
card j = ψ (natT j) []
A = card 2 ∷ card 1 ∷ []
A⁺ = card 2 ∷ card 1 ∷ card 0 ∷ []
P = ψ (natT 2) A
cut = S.φ (ψ (natT 2) A⁺ ∷ [])
branch : ℕ → T
branch n = S.φ (replicate n P)

card-support : ∀ {u z} j → InGP u z (card j) → z ≡ []
card-support j (gh _) = refl
card-support j (gw _ h) = B.num-support j (G-mono (B.bottom _) h)
card-support j (gc _ ())

support : ∀ {u z} → InG u z A⁺ → z ≡ []
support (gp h) = card-support 2 h
support (gtl (gp h)) = card-support 1 h
support (gtl (gtl h)) = B.num-support 1 (G-mono (B.bottom _) h)

nf-A⁺ : NF A⁺
nf-A⁺ = n∷ (nf-hd (nf-Ω (B.nf-num 2))) (inj₁ (lt→<ᴾ _ _ refl))
  (n∷ (nf-hd (nf-Ω (B.nf-num 1))) (inj₁ (lt→<ᴾ _ _ refl)) (B.nf-num 1))

nf-cut : NF cut
nf-cut = nf-ψ n[] (nf-ψ (B.nf-num 2) nf-A⁺ inner) outer
  where
  inner : GB (natT 2) A⁺ A⁺
  inner h rewrite support h = []<
  outer : GB [] (ψ (natT 2) A⁺ ∷ []) (ψ (natT 2) A⁺ ∷ [])
  outer (gp (gh _)) = hd< (ar< []<)
  outer (gp (gw _ h)) rewrite B.num-support 2 h = []<
  outer (gp (gc _ h)) rewrite support h = []<
  outer (gtl ())

opaque
  cut-h : HC cut
  cut-h = hc nf-cut (c∷ c[])

branch-eq : ∀ n → fsn cut n ≡ branch n
branch-eq n = trans (fsnψω [] _ n refl) (cong S.φ (fsnψ1 (natT 2) A⁺ n refl))

branch-nf : ∀ n → NF (branch n)
branch-nf n = subst NF (branch-eq n) (cl-fsn-NF nf-cut refl n)

opaque
  branch-h : ∀ n → HC (branch n)
  branch-h n = subst HC (branch-eq n) (hω-inv cut-h refl n)

exact : Rt cut-h ≈ᵛ L.lim (λ n → Rt (branch-h n))
exact = S.limit cut-h refl (λ n → Rt (branch-h n)) (λ n → S.same (branch-eq n) (hω-inv cut-h refl n) (branch-h n))

-- 严格下降在第一个不同的主项处结束；相等时消去一份。
word-bound : ∀ p {t} → NF t → HdLe p t → t <ᵀ replicate (suc (length t)) p
word-bound p n[] _ = []<
word-bound p (n∷ _ _ _) (inj₁ h) = hd< h
word-bound p (n∷ _ le nt) (inj₂ refl) = tl< (word-bound p nt le)

paid-by-copies : ∀ s (nf : NF (S.φ (P ∷ s))) (h : HC (S.φ (P ∷ s))) →
  L.suc (Rt h) ≼ Rt (branch-h (suc (suc (length s))))
paid-by-copies s nf h = mono<ⁿ nf (branch-nf (suc (suc (length s)))) (c∷ c[]) h (branch-h (suc (suc (length s))))
  (hd< (ar< (tl< (word-bound P (nf-tl word) (nf-le word)))))
  where word = nfp-a (nf-hd nf)

below-cut : ∀ s (nf : NF (S.φ (P ∷ s))) (h : HC (S.φ (P ∷ s))) → L.suc (Rt h) ≼ Rt cut-h
below-cut s nf h = ≼-trans {b = L.lim (λ n → Rt (branch-h n))} (≼l {f = λ n → Rt (branch-h n)} (suc (suc (length s))) (paid-by-copies s nf h)) (proj₂ exact)

least : ∀ {y : L.Ordᶜ L.zero} →
  (∀ s (nf : NF (S.φ (P ∷ s))) (h : HC (S.φ (P ∷ s))) → Rt h ≼ y) → Rt cut-h ≼ y
least {y} upper = ≼-trans {b = L.lim (λ n → Rt (branch-h n))} (proj₁ exact) (l≼ by-index)
  where
  by-index : ∀ n → Rt (branch-h n) ≼ y
  by-index zero = ≼-trans {b = L.suc (Rt (branch-h 0))} (≼-suc (≼-refl _)) (≼-trans {b = Rt (branch-h 1)}
    (mono<ⁿ (branch-nf 0) (branch-nf 1) (c∷ c[]) (branch-h 0) (branch-h 1) (hd< (ar< []<)))
    (upper [] (branch-nf 1) (branch-h 1)))
  by-index (suc n) = upper (replicate n P) (branch-nf (suc n)) (branch-h (suc n))

cut<first : L.suc (Rt cut-h) ≼ Rt Old.next-h
cut<first = mono<ⁿ nf-cut Old.next-nf (c∷ c[]) cut-h Old.next-h (lt→< _ _ refl)
```

任意一个标准后缀 s 都严格低于第 length(s)+2 枝。反向取上确界时，第 n+1 枝本身就是以 P 开头的标准项。这两个方向确定了包含所有标准后缀的最小上界；它严格低于两份 Ω₂ 参照的第 1 枝。
