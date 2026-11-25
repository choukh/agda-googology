# 规范调用的比较表请求域
验收文件，不读记号；`Ask` 沿原折叠与实际回灌链跟踪请求，并继续越过已有的比较行。
来源：YiMTHit.Hit 的全部原分支；末行按 YiTBRow.ψ 补三支与退路内的请求。
`FullOn` 仅否定本域中的空格；尚未证明塔第 2、3 项的 FullTw，也不把空格解释为值损失。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFOTrace where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; kp)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiNRHit using (cW₁; HN)
open import OCF.Lean.YiMTHit using (Site)

dW₁ : {A B : Set} → Maybe (A ⊎ B) → (A → Set) → (B → Set) → Set → Set
dW₁ (just (inj₁ a)) F G H = F a
dW₁ (just (inj₂ b)) F G H = G b
dW₁ nothing F G H = H

Ask : Site → (ℓ : L) → Ok ℓ → Rb ℓ → Base ℓ → ((i : L) → i ≤ ℓ → Set) → (j : L) → j ≤ ℓ → Tr⁺ j → Set → Tr ℓ → Set
Ask P ℓ o r B HB j w β Hβ zero      = Hβ
Ask P ℓ o r B HB j w β Hβ (suc x)   = Ask P ℓ o r B HB j w β Hβ x
Ask P ℓ o r B HB j w β Hβ (lim f a) = Σ ℕ λ n → Ask P ℓ o r B HB j w β Hβ (f n)
Ask P ℓ o r B HB j w β Hβ (Ω p g)   = HN (kp ℓ o p w) (λ z → Ask P ℓ o r B HB j w β Hβ (g z))
  (λ z → fromBr ℓ p (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
  (λ z → Ask P ℓ o r B HB (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (HB (at ℓ p) (posW ℓ p)) (g z))
Ask P (nd s h) o r B HB _ self β Hβ (up x c y e) = Ask P (nd s h) o r B HB _ self β Hβ x
Ask P (nd s h) o r B HB j (inu ws) β Hβ (up x c y e) =
  Ask P (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x)
      (λ i u → Ask P (nd s h) o r B HB i (inc c u) (B i (inc c u)) (HB i (inc c u)) x)
      j (ws c) (ψ (nd s h) o r B j (inu ws) β x) (Ask P (nd s h) o r B HB j (inu ws) β Hβ x) y
Ask P (nd (sΩ k) h) o r B HB j (ink v) β Hβ (up x c y e) =
  Ask P (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x)
      (λ i u → Ask P (nd (sΩ k) h) o r B HB i (inc c u) (B i (inc c u)) (HB i (inc c u)) x)
      j (v ∙ proj₂ (proj₁ o) c) (ψ (nd (sΩ k) h) o r B j (ink v) β x) (Ask P (nd (sΩ k) h) o r B HB j (ink v) β Hβ x) y
Ask P (nd sS h) o r B HB j (inc c′ v) β Hβ (up x c y e) =
  Ask P (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x)
      (λ i u → Ask P (nd sS h) o r B HB i (inc c u) (B i (inc c u)) (HB i (inc c u)) x)
      j v (ψ (nd sS h) o r B j (inc c′ v) β x) (Ask P (nd sS h) o r B HB j (inc c′ v) β Hβ x) y
Ask P (nd sL g) o r B HB j (inc n v) β Hβ (up x m y e) = cW₁ (way g (proj₁ o) m n)
  (λ u → Ask P (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x)
           (λ i u′ → Ask P (nd sL g) o r B HB i (inc n u′) (B i (inc n u′)) (HB i (inc n u′)) x) j v
           (ψ (nd sL g) o r B j (inc n v) β x) (Ask P (nd sL g) o r B HB j (inc n v) β Hβ x)
           (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
  (λ u → Ask P (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x)
           (λ i u′ → Ask P (nd sL g) o r B HB i (inc m u′) (B i (inc m u′)) (HB i (inc m u′)) x) j (v ∙ u)
           (ψ (nd sL g) o r B j (inc n v) β x) (Ask P (nd sL g) o r B HB j (inc n v) β Hβ x) y)
Ask P (nd (sΩ k) h) o r B HB j (inc c′ v) β Hβ (up x c y e) =
  P k h j c′ c (proj₁ r c c′) ⊎ dW₁ (proj₁ r c c′)
    (λ u → Ask P (h c) (proj₂ o c) (proj₂ r c)
      (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x)
      (λ i u′ → Ask P (nd (sΩ k) h) o r B HB i (inc c u′) (B i (inc c u′)) (HB i (inc c u′)) x)
      j (v ∙ u) (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x)
      (Ask P (nd (sΩ k) h) o r B HB j (inc c′ v) β Hβ x) y)
    (λ u → Ask P (h c′) (proj₂ o c′) (proj₂ r c′)
      (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c′ u′) (B i (inc c′ u′)) x)
      (λ i u′ → Ask P (nd (sΩ k) h) o r B HB i (inc c′ u′) (B i (inc c′ u′)) (HB i (inc c′ u′)) x)
      j v (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x)
      (Ask P (nd (sΩ k) h) o r B HB j (inc c′ v) β Hβ x)
      (proj₁ (emb (h c′) (proj₂ o c′) u (y , e))))
    (Ask P (nd (sΩ k) h) o r B HB j (inc c′ v) β Hβ x ⊎
      Ask P (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) (λ _ _ → ⊥)
      zero (z≤ (h c)) (Ωt zero) ⊥ y)


Missing : Site
Missing k h j c′ c m = m ≡ nothing

AskTw : Site → (n : ℕ) → Rb (tw n) → Set
AskTw P n r = Ask P (tw n) (Ok-tw n) r (B₀ (tw n)) (λ _ _ → ⊥)
  zero (z≤ (tw n)) (Ωt zero) ⊥ (proj₁ (Ωt (tw n)))
Domain : Set₁
Domain = Site → Set
FullOn : Domain → Set
FullOn D = D Missing → ⊥
FullTw : (n : ℕ) → Rb (tw n) → Set
FullTw n r = FullOn (λ P → AskTw P n r)
full-zero : FullTw 0 (rbᶻ zero)
full-zero ()
```
