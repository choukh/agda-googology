# 按表参数化: MWPre

参数化（工程），数学内容与 `YiVTMWPre` 的保持及下降证明相同；验收文件。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMMWPre where

open import OCF.Lean.YiPMTable using (Table)

module F (tb : Table) where
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Unit using (⊤; tt)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Sum using (inj₁; inj₂)
  open import Data.Product using (Σ; _×_; _,_)
  open import Data.List using ([]; _∷_; _++_; replicate)
  open import Data.List.Properties using (++-assoc)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

  open import OCF.Lean.YiLegBlock
  open import OCF.Lean.YiLegOps
  open import OCF.Lean.YiLegPath using (_≤_; self; ins)
  import OCF.Lean.YiPMFold
  open OCF.Lean.YiPMFold.F tb
  import OCF.Align.EboLeanDef as E
  open E using (HC; h0; h1; hω; cof; c0; c1; cω; cΩ; pred; fsn; fsT; γT; ψ; 𝟏; natT)
  open import OCF.Align.Correspond using (cof-ne)
  import OCF.Align.Level as O
  open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ⊑→≼)
  open import OCF.Lean.YiMEBase
  open import OCF.Lean.YiMENote
  import OCF.Lean.YiPMMEAnchor
  open OCF.Lean.YiPMMEAnchor.F tb

  inv-suc : (x : Tr zero) {a : T₀} → O.suc a ≼ read x → Σ (Tr zero) λ x′ → (suc x′ ⊴ x) × (a ≼ read x′)
  inv-suc zero          ()
  inv-suc (suc x)       (s≼s p) = x , ⊴r , p
  inv-suc (lim f a)     (≼l n p) with inv-suc (f n) p
  ... | x′ , le , q = x′ , ⊴◃ (⊴-◃ le (◃l n)) , q
  inv-suc (Ω () _)
  inv-suc (up _ () _ _)

  sem→M⁰ : ∀ {t} (h : HC t) (x : Tr zero) → Rt h ≼ read x → M⁰ t x
  sem→M⁰ {t = []}     (h0 e)    x q = mz
  sem→M⁰ {t = y ∷ ys} (h0 e)    x q = ⊥-elim (cof-ne y ys e)
  sem→M⁰              (h1 e hp) x q with inv-suc x q
  ... | x′ , le , q′ = G⁰.m⊴ (m1 e (sem→M⁰ hp x′ q′)) le
  sem→M⁰              (hω e hs) x q = mL e (λ n → sem→M⁰ (hs n) x (≼-trans (≼l n (≼-refl (Rt (hs n)))) q))

  M⁰-≼ : ∀ {t x} → M⁰ t x → (y : Tr zero) → read x ≼ read y → M⁰ t y
  M⁰-≼ mz                  y q = mz
  M⁰-≼ (m1 e r)            y q with inv-suc y q
  ... | y′ , le , q′ = G⁰.m⊴ (m1 e (M⁰-≼ r y′ q′)) le
  M⁰-≼ (mL e h)            y q = mL e (λ n → M⁰-≼ (h n) y q)
  M⁰-≼ (mΩ {p = ()} _ _ _) y q
  M⁰-≼ (mU {c = ()} _ _)   y q
  M⁰-≼ (mw {x = x} m d)    y q = M⁰-≼ m y (≼-trans (⊑→≼ (read x) (◃⊑ d)) q)

  cof++Ω : ∀ t s {ν} → cof s ≡ cΩ ν → cof (t ++ s) ≡ cΩ ν
  cof++Ω t []       ()
  cof++Ω t (y ∷ ys) e = trans (cof++ t y ys) e

  fsT++′ : ∀ t y ys η → fsT (t ++ y ∷ ys) η ≡ t ++ fsT (y ∷ ys) η
  fsT++′ []          y ys η = refl
  fsT++′ (x ∷ [])    y ys η = refl
  fsT++′ (x ∷ z ∷ t) y ys η = cong (x ∷_) (fsT++′ (z ∷ t) y ys η)

  fsT++ : ∀ t s η {ν} → cof s ≡ cΩ ν → fsT (t ++ s) η ≡ t ++ fsT s η
  fsT++ t []       η ()
  fsT++ t (y ∷ ys) η e = fsT++′ t y ys η

  module Pre (B₂ : Base two) (hβ : M¹ Ω₁ᵗ (bs B₂ one (ins self))) (t : E.T)
    (hp0 : M⁰ (ψ₀ᵗ t) (bs B₂ zero (ins (ins self))))
    (hp⊥ : M⁰ (ψ₀ᵗ t) (b⊥ B₂)) where

    open At B₂ hβ (pos⁰ (bs B₂ zero (ins (ins self))) (ns B₂ zero (ins (ins self)))) (pos⁰ (b⊥ B₂) (n⊥ B₂)) public
      using (Bᵃ; β₀; nβ₀; F; nzF; H; nzH; W; nzW; PF; vch; γ; z; sγ)

    mutual
      QHp : ∀ {a x} → M¹ a x → M⁰ (ψ₀ᵗ (t ++ a)) (H x)
      QHp (mz {x = x}) =
        ++[] (λ s → M⁰ (ψ₀ᵗ s) (H x)) t (G⁰.m-zl H (monos one tt tt Bᵃ zero (ins self) β₀ nβ₀) hp0 x)
      QHp (m1 {t = a} {x = x} e r) =
        G⁰.m-next (nzH x) (cofψ1 u₀ (t ++ a) (cof++1 t a e))
          (λ n → trans (fsnψ1 u₀ (t ++ a) n (cof++1 t a e)) (cong (λ s → replicate n (ψ u₀ s)) (pred++ t a e)))
          (QHp r)
      QHp (mL {t = a} {x = x} e h) =
        mL (cofψω u₀ (t ++ a) (cof++ω t a e))
          (λ n → subst (λ s → M⁰ s (H x))
            (sym (trans (fsnψω u₀ (t ++ a) n (cof++ω t a e)) (cong ψ₀ᵗ (fsn++ t a n e))))
            (QHp (h n)))
      QHp (mΩ {t = a} {p = inj₁ tt} {g = g} e refl h) =
        mL (cofψΩ u₀ (t ++ a) (cof++Ω t a e))
          (λ n → subst (λ s → M⁰ s (H (Ω (inj₁ tt) g)))
            (sym (trans (fsnψΩ u₀ (t ++ a) n (cof++Ω t a e)) (cong ψ₀ᵗ (fsT++ t a (γT (t ++ a) [] n) e))))
            (G⁰.m-cum (λ m → H (g (vch g m))) (λ m → nzH (g (vch g m))) (suc n)
              (QHp (h (γT (t ++ a) [] n) (vch g (suc n)) (chainp e h n)))))
      QHp (mΩ {p = inj₂ ()} _ _ _)
      QHp (mU {t = a} {s = s} {x = x} {y = y} m ch) =
        subst (λ r → M⁰ (ψ₀ᵗ r) (ψs zero tt tt (dS zero tt tt Bᵃ x) zero self (H x) (nzH x) y)) (++-assoc t a s)
          (Qu (dS zero tt tt Bᵃ x) (H x) (nzH x) (QHp m) ch)
      QHp (mw m d) = mw (QHp m) (monos one tt tt Bᵃ zero (ins self) β₀ nβ₀ d)

      chainp : ∀ {a} {g : Tr zero → Tr one} → cof a ≡ cΩ [] → (∀ η c → M⁰ η c → M¹ (fsT a η) (g c))
             → ∀ n → M⁰ (γT (t ++ a) [] n) (vch g (suc n))
      chainp {g = g} e h zero    = pos⁰ (H (g zero)) (nzH (g zero))
      chainp {a = a} {g = g} e h (suc n) =
        subst (λ s → M⁰ s (vch g (suc (suc n)))) (sym (cong ψ₀ᵗ (fsT++ t a (γT (t ++ a) [] n) e)))
          (QHp (h _ _ (chainp e h n)))

    VWp : ∀ {a x} → M¹ a x → M⁰ (ψ₀ᵗ (t ++ a)) (W x)
    VWp (mz {x = x}) =
      ++[] (λ s → M⁰ (ψ₀ᵗ s) (W x)) t (G⁰.m-zl W (mono⊥ one tt tt Bᵃ) hp⊥ x)
    VWp (m1 {t = a} {x = x} e r) =
      G⁰.m-next (nzW x) (cofψ1 u₀ (t ++ a) (cof++1 t a e))
        (λ n → trans (fsnψ1 u₀ (t ++ a) n (cof++1 t a e)) (cong (λ s → replicate n (ψ u₀ s)) (pred++ t a e)))
        (VWp r)
    VWp (mL {t = a} {x = x} e h) =
      mL (cofψω u₀ (t ++ a) (cof++ω t a e))
        (λ n → subst (λ s → M⁰ s (W x))
          (sym (trans (fsnψω u₀ (t ++ a) n (cof++ω t a e)) (cong ψ₀ᵗ (fsn++ t a n e))))
          (VWp (h n)))
    VWp (mΩ {t = a} {p = inj₁ tt} {g = g} e refl h) =
      mL (cofψΩ u₀ (t ++ a) (cof++Ω t a e))
        (λ n → subst (λ s → M⁰ s (W (Ω (inj₁ tt) g)))
          (sym (trans (fsnψΩ u₀ (t ++ a) n (cof++Ω t a e)) (cong ψ₀ᵗ (fsT++ t a (γT (t ++ a) [] n) e))))
          (G⁰.m-cum (λ m → W (g (vch g m))) (λ m → nzW (g (vch g m))) (suc n)
            (VWp (h (γT (t ++ a) [] n) (vch g (suc n)) (chainp e h n)))))
    VWp (mΩ {p = inj₂ ()} _ _ _)
    VWp (mU {t = a} {s = s} {x = x} {y = y} m ch) =
      subst (λ r → M⁰ (ψ₀ᵗ r) (ψ⊥ zero tt tt (dS zero tt tt Bᵃ x) y)) (++-assoc t a s)
        (Vu (dS zero tt tt Bᵃ x) (VWp m) ch)
    VWp (mw m d) = mw (VWp m) (mono⊥ one tt tt Bᵃ d)

    rowp : ∀ n → M⁰ (ψ₀ᵗ (t ++ ψ₁ᵗ (γ n))) (ψ⊥ two tt tt B₂ (Ωt two))
    rowp n =
      G⁰.m-cum (λ k → next (W (z k)) (nzW (z k))) (λ k → nz⊥ two tt tt B₂ (up zero tt (suc (z k)) (z◃s (z k))))
        (suc (suc n)) (mw (VWp (sγ (suc n))) (◃l zero))
```
