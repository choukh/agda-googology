# Ω 树块的换基覆写试验
候选，不替换主线；普通行与单调证明搬自 YiRBSib，地板以上一行改成目标层加偏移。
该行的换基部分固定重建 Ω 树，原孩子树只进入低层尾项；类型保证合法，`mono` 保持第一位置。
未证明带码域的实际链闭包；此扩展不是完整 V149，字面限制见 YiBSReadNeg，闭项见 YiBSClean。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBSFold where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; kp; node⁺; nodeLe)
open import OCF.Lean.YiRBSib using (rb; rb-ind; rb-ind₂)
open import OCF.Lean.YiBSBase
mutual
  ψ : (ℓ : L) → Ok ℓ → Rb ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j
  ψ ℓ o r B j w β zero      = β
  ψ ℓ o r B j w β (suc x)   = next⁺ (ψ ℓ o r B j w β x)
  ψ ℓ o r B j w β (lim f a) = lim⁺ (λ n → ψ ℓ o r B j w β (f n)) (λ n → mono ℓ o r B j w β (a n))
  ψ ℓ o r B j w β (Ω p g)   = node⁺ (kp ℓ o p w) (λ z → ψ ℓ o r B j w β (g z))
    (λ z → fromBr ℓ p (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
  ψ (nd s h) o r B _ self β (up x c y e) = Up (h c) (down stop c) (ψ (nd s h) o r B _ self β x) y
  ψ (nd s h) o r B j (inu ws) β (up x c y e) =
    ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) y
  ψ (nd (sΩ k) h) o r B j (ink v) β (up x c y e) =
    ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
      (ψ (nd (sΩ k) h) o r B j (ink v) β x) y
  ψ (nd sS h) o r B j (inc c′ v) β (up x c y e) =
    ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) y
  ψ (nd sL g) o r B j (inc n v) β (up x m y e) = cW (way g (proj₁ o) m n)
    (λ u → ψ (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
             (ψ (nd sL g) o r B j (inc n v) β x) (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
    (λ u → ψ (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
             (ψ (nd sL g) o r B j (inc n v) β x) y)
  ψ (nd (sΩ k) h) o r B j (inc c′ v) β (up x c y e) = rb (proj₁ r)
    (λ S → cW (route S j c′ v)
      (λ u → ψ (h c) (proj₂ o c) (proj₂ r c)
        (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (back S c u)
        (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) y)
      (λ u → seen S j (downOk (h c′) (proj₂ o c′) j v) u
        (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) c
        ⊞ ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))
    (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x ⊞ ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)


  mono : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) {x y : Tr ℓ}
       → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ ℓ o r B j w β x) ◃ proj₁ (ψ ℓ o r B j w β y)
  mono ℓ o r B j w β ◃s           = ◃l zero
  mono ℓ o r B j w β (◃l n)       = ◃l n
  mono ℓ o r B j w β (◃w {p = p}) = nodeLe (kp ℓ o p w) _ _
  mono (nd s h) o r B _ self β (◃u x c y e) = Upm (h c) (down stop c) (ψ (nd s h) o r B _ self β x) e
  mono (nd s h) o r B j (inu ws) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) e
  mono (nd (sΩ k) h) o r B j (ink v) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
      (ψ (nd (sΩ k) h) o r B j (ink v) β x) e
  mono (nd sS h) o r B j (inc c′ v) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) e
  mono (nd sL g) o r B j (inc n v) β (◃u x m y e) =
    cW-ind (λ Z → j ⊢ proj₁ (ψ (nd sL g) o r B j (inc n v) β x) ◃ proj₁ Z) (way g (proj₁ o) m n)
      (λ u → mono (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ (nd sL g) o r B j (inc n v) β x) (proj₂ (emb (g n) (proj₂ o n) u (y , e))))
      (λ u → mono (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ (nd sL g) o r B j (inc n v) β x) e)
  mono (nd (sΩ k) h) o r B j (inc c′ v) β (◃u x c y e) =
    rb-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) ◃ proj₁ Z) (proj₁ r)
      (λ S → cW-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) ◃ proj₁ Z) (route S j c′ v)
        (λ u → mono (h c) (proj₂ o c) (proj₂ r c)
          (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (back S c u)
          (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) e)
        (λ u → ◃t (seen-step S j (downOk (h c′) (proj₂ o c′) j v) u
          (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) c)
          (+-mono _ (ι-mono j (proj₂ (ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))))))
      (+-mono _ (ι-mono j (proj₂ (ψ (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))))

  mono (nd s h) o r B _ self β (◃c x c d) = Upm (h c) (down stop c) (ψ (nd s h) o r B _ self β x) d
  mono (nd s h) o r B j (inu ws) β (◃c x c d) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o r B j (inu ws) β x) d
  mono (nd (sΩ k) h) o r B j (ink v) β (◃c x c d) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
      (ψ (nd (sΩ k) h) o r B j (ink v) β x) d
  mono (nd sS h) o r B j (inc c′ v) β (◃c x c d) =
    mono (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o r B j (inc c′ v) β x) d
  mono (nd sL g) o r B j (inc n v) β (◃c x m d) =
    cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (way g (proj₁ o) m n)
      (λ u → mono (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ (nd sL g) o r B j (inc n v) β x) (emb-mono (g n) (proj₂ o n) u d))
      (λ u → mono (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ (nd sL g) o r B j (inc n v) β x) d)
  mono (nd (sΩ k) h) o r B j (inc c′ v) β (◃c x c d) =
    rb-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (proj₁ r)
      (λ S → cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (route S j c′ v)
        (λ u → mono (h c) (proj₂ o c) (proj₂ r c)
          (λ i u′ → ψ (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (back S c u)
          (ψ (nd (sΩ k) h) o r B j (inc c′ v) β x) d)
        (λ u → +-mono _ (ι-mono j (mono (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) d))))
      (+-mono _ (ι-mono j (mono (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) d)))

  mono ℓ o r B j w β (◃t d d′) = ◃t (mono ℓ o r B j w β d) (mono ℓ o r B j w β d′)
ψ₀ : (ℓ : L) → Ok ℓ → Rb ℓ → Tr ℓ → Tr⁺ zero
ψ₀ ℓ o r = ψ ℓ o r (B₀ ℓ) zero (z≤ ℓ) (Ωt zero)
closed : (n : ℕ) → Tr⁺ zero
closed n = ψ₀ (tw n) (Ok-tw n) (rb-tw n) (proj₁ (Ωt (tw n)))
```
