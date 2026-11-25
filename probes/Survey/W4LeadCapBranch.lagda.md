# 两份 Ω₂ 的第一个正询问的完整原基本列

第四层。原 EBO 项 a₂[1] 是从 1 迭代同一个有名算子的严格可数上确界。其任一严格初段都落到某次有限迭代之前。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LeadCapBranch where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import OCF.Align.EboLeanDef using (T; ψ; natT; Ωt; γT; fsn; _<ᵀ_; hd<; ar<; tl<; []<; HC)
open import OCF.Align.EboLeanBase using (NF; lt→<; c∷; c[])
open import OCF.Align.EboLeanClosure using (cl-fsn-NF)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≼l; ≼-refl)
open import WVOne using (T₀)
import OCF.Align.Level as L
import B26PSuffix as Low
import Survey.W4OriginalIteratedBound as Old
import Survey.EboPTOFinite as P

pair = natT 2
top = ψ pair []
one = natT 1
inner = λ x → ψ pair (top ∷ x) ∷ []
name = λ y → Low.φ (inner (ψ one y ∷ []))
step = λ x → name (inner x)
sequence : ℕ → T
sequence zero = one
sequence (suc n) = step (sequence n)
arg = inner (ψ one (inner (Ωt one)) ∷ [])

loop : ∀ n → γT arg [] n ≡ sequence n
loop zero = refl
loop (suc n) = cong step (loop n)
branch : ∀ n → fsn Old.next-branch n ≡ sequence (suc n)
branch n = loop (suc n)

normal : ∀ n → NF (sequence n)
normal zero = P.nf-num 1
normal (suc n) = subst NF (branch n) (cl-fsn-NF Old.next-nf refl n)
cert : ∀ n → HC (sequence n)
cert zero = OCF.Align.EboLeanDef.h1 refl (OCF.Align.EboLeanDef.h0 refl)
cert (suc n) = subst HC (branch n) (hω-inv Old.next-h refl n)
strict : ∀ {x y} → x <ᵀ y → step x <ᵀ step y
strict e = hd< (ar< (hd< (ar< (tl< (hd< (ar< (hd< (ar< (tl< e)))))))))
rises : ∀ n → sequence n <ᵀ sequence (suc n)
rises zero = lt→< _ _ refl
rises (suc n) = strict (rises n)
v = λ n → Rt (cert n)
climb : ∀ n → L.suc (v n) ≼ v (suc n)
climb n = mono<ⁿ (normal n) (normal (suc n)) (c∷ c[]) (cert n) (cert (suc n)) (rises n)

exact : Rt Old.next-h ≈ᵛ L.lim (λ n → v (suc n))
exact = Low.limit Old.next-h refl (λ n → v (suc n)) (λ n → Low.same (branch n) (hω-inv Old.next-h refl n) (cert (suc n)))

cover : ∀ (x : T₀) → L.suc x ≼ Rt Old.next-h → Σ ℕ (λ n → L.suc x ≼ v (suc n))
cover x h with ≼-trans {b = Rt Old.next-h} h (proj₁ exact)
... | ≼l n p = n , p
```
