# 按表参数化: PHBase

参数化（工程），数学内容与 `YiVTPHBase` 的保持及下降证明相同；验收文件。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMPHBase where

open import OCF.Lean.YiPMTable using (Table)

module F (tb : Table) where
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Unit using (⊤; tt)
  open import Data.Sum using (inj₁; inj₂)
  open import Data.Product using (_,_)
  open import Data.List using ([]; _∷_; _++_; replicate)
  open import Data.List.Properties using (++-assoc)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

  open import OCF.Lean.YiLegBlock
  open import OCF.Lean.YiLegOps
  open import OCF.Lean.YiLegPath using (_≤_; self; ins)
  import OCF.Lean.YiPMFold
  open OCF.Lean.YiPMFold.F tb
  import OCF.Align.EboLeanDef as E
  open E using (cof; c1; cω; cΩ; pred; fsn; fsT; ψ; natT)
  open import OCF.Lean.YiMEBase
  open import OCF.Lean.YiMENote
  import OCF.Lean.YiPMMEAnchor
  open OCF.Lean.YiPMMEAnchor.F tb using (one; two; M¹; Low¹; Nu¹; u₀; u₁; ψ₀ᵗ; ψ₁ᵗ; Ω₁ᵗ; Ω₂ᵗ; ++[])
  import OCF.Lean.YiPMMWPre
  open OCF.Lean.YiPMMWPre.F tb using (cof++Ω; fsT++)

  three : L
  three = suc two

  u₂ : E.T
  u₂ = natT 2

  ψ₂ᵗ : E.T → E.T
  ψ₂ᵗ a = ψ u₂ a ∷ []

  Low² : (p : Pos two) → E.T → Br two p → Set
  Low² (inj₁ _)        = M¹
  Low² (inj₂ (inj₁ _)) = M⁰
  Low² (inj₂ (inj₂ ()))

  Nu² : Pos two → E.T → Set
  Nu² (inj₁ _) ν = ν ≡ u₁
  Nu² (inj₂ _) ν = ν ≡ []

  M² : E.T → Tr two → Set
  M² = Mᴰ (Sig two) Low² (λ _ → M¹) Nu²

  module G² = Gen {Sig two} {Low²} {λ _ → M¹} {Nu²}

  Mβ₂ : M² Ω₂ᵗ (Ωt two)
  Mβ₂ = mΩ refl refl (λ η c l → mU mz (mw l ◃s))

  Pu⁰ : ∀ {t} (d : Dn two zero) (b : Tr two) (nb : two ⊢ zero ◃ b) → M² (ψ₂ᵗ t) b
      → ∀ {s y} → M⁰ s y → M² (ψ₂ᵗ (t ++ s)) (Up zero d b nb y)
  Pu⁰ {t} d b nb mb (mz {x = y}) =
    ++[] (λ z → M² (ψ₂ᵗ z) (Up zero d b nb y)) t (G².m-zl (Up zero d b nb) (Up-mono zero d b nb) mb y)
  Pu⁰ {t} d b nb mb (m1 {t = s} {x = y} e r) =
    G².m-next (Up-nz zero d b nb y) (cofψ1 u₂ (t ++ s) (cof++1 t s e))
      (λ n → trans (fsnψ1 u₂ (t ++ s) n (cof++1 t s e)) (cong (λ z → replicate n (ψ u₂ z)) (pred++ t s e)))
      (Pu⁰ d b nb mb r)
  Pu⁰ {t} d b nb mb (mL {t = s} {x = y} e h) =
    mL (cofψω u₂ (t ++ s) (cof++ω t s e))
      (λ n → subst (λ z → M² z (Up zero d b nb y))
        (sym (trans (fsnψω u₂ (t ++ s) n (cof++ω t s e)) (cong ψ₂ᵗ (fsn++ t s n e))))
        (Pu⁰ d b nb mb (h n)))
  Pu⁰ d b nb mb (mΩ {p = ()} _ _ _)
  Pu⁰ d b nb mb (mU {c = ()} _ _)
  Pu⁰ d b nb mb (mw m r) = mw (Pu⁰ d b nb mb m) (Up-mono zero d b nb r)

  Pu¹ : ∀ {t} (b : Tr two) (nb : two ⊢ zero ◃ b) → M² (ψ₂ᵗ t) b
      → ∀ {s y} → M¹ s y → M² (ψ₂ᵗ (t ++ s)) (Up one (down stop tt) b nb y)
  Pu¹ {t} b nb mb (mz {x = y}) =
    ++[] (λ z → M² (ψ₂ᵗ z) (Up one (down stop tt) b nb y)) t
      (G².m-zl (Up one (down stop tt) b nb) (Up-mono one (down stop tt) b nb) mb y)
  Pu¹ {t} b nb mb (m1 {t = s} {x = y} e r) =
    G².m-next (Up-nz one (down stop tt) b nb y) (cofψ1 u₂ (t ++ s) (cof++1 t s e))
      (λ n → trans (fsnψ1 u₂ (t ++ s) n (cof++1 t s e)) (cong (λ z → replicate n (ψ u₂ z)) (pred++ t s e)))
      (Pu¹ b nb mb r)
  Pu¹ {t} b nb mb (mL {t = s} {x = y} e h) =
    mL (cofψω u₂ (t ++ s) (cof++ω t s e))
      (λ n → subst (λ z → M² z (Up one (down stop tt) b nb y))
        (sym (trans (fsnψω u₂ (t ++ s) n (cof++ω t s e)) (cong ψ₂ᵗ (fsn++ t s n e))))
        (Pu¹ b nb mb (h n)))
  Pu¹ {t} b nb mb (mΩ {t = s} {p = inj₁ tt} {g = g} e refl h) =
    mΩ (cofψΩ u₂ (t ++ s) (cof++Ω t s e)) refl
      (λ η c l → subst (λ z → M² z (Up one (down stop tt) b nb (g c)))
        (sym (trans (fsTψΩ u₂ (t ++ s) η (cof++Ω t s e)) (cong ψ₂ᵗ (fsT++ t s η e))))
        (Pu¹ b nb mb (h η c l)))
  Pu¹ b nb mb (mΩ {p = inj₂ ()} _ _ _)
  Pu¹ {t} b nb mb (mU {t = s₀} {s = s₁} {x = y₀} {y = y₁} m ch) =
    subst (λ z → M² (ψ₂ᵗ z) (Up zero (down (down stop tt) tt) (Up one (down stop tt) b nb y₀) (Up-nz one (down stop tt) b nb y₀) y₁))
      (++-assoc t s₀ s₁)
      (Pu⁰ (down (down stop tt) tt) (Up one (down stop tt) b nb y₀) (Up-nz one (down stop tt) b nb y₀) (Pu¹ b nb mb m) ch)
  Pu¹ b nb mb (mw m r) = mw (Pu¹ b nb mb m) (Up-mono one (down stop tt) b nb r)

  module P2 (B₃ : Base three) (hβ₂ : M² Ω₂ᵗ (bs B₃ two (ins self))) where

    Bᵃ : Base two
    Bᵃ = dS two tt tt B₃ zero

    β₂ : Tr two
    β₂ = bs B₃ two (ins self)

    nβ₂ : two ⊢ zero ◃ β₂
    nβ₂ = ns B₃ two (ins self)

    F² : Tr two → Tr two
    F² x = ψs two tt tt Bᵃ two self β₂ nβ₂ x

    nzF² : (x : Tr two) → two ⊢ zero ◃ F² x
    nzF² x = nzs two tt tt Bᵃ two self β₂ nβ₂ x

    monoF² : {x y : Tr two} → two ⊢ x ◃ y → two ⊢ F² x ◃ F² y
    monoF² = monos two tt tt Bᵃ two self β₂ nβ₂

    P² : ∀ {a x} → M² a x → M² (ψ₂ᵗ a) (F² x)
    P² (mz {x = x}) = G².m-zl F² monoF² hβ₂ x
    P² (m1 {t = a} {x = x} e r) =
      G².m-next (nzF² x) (cofψ1 u₂ a e) (λ n → fsnψ1 u₂ a n e) (P² r)
    P² (mL {t = a} {x = x} e h) =
      mL (cofψω u₂ a e) (λ n → subst (λ z → M² z (F² x)) (sym (fsnψω u₂ a n e)) (P² (h n)))
    P² (mΩ {t = a} {p = inj₁ tt} {g = g} e refl h) =
      mΩ (cofψΩ u₂ a e) refl
        (λ η c l → subst (λ z → M² z (F² (g c))) (sym (fsTψΩ u₂ a η e)) (P² (h η c l)))
    P² (mΩ {t = a} {p = inj₂ (inj₁ tt)} {g = g} e refl h) =
      mΩ (cofψΩ u₂ a e) refl
        (λ η c l → subst (λ z → M² z (F² (g c))) (sym (fsTψΩ u₂ a η e)) (P² (h η c l)))
    P² (mΩ {p = inj₂ (inj₂ ())} _ _ _)
    P² (mU {x = x} m ch) = Pu¹ (F² x) (nzF² x) (P² m) ch
    P² (mw m d) = mw (P² m) (monoF² d)

    z : ℕ → Tr two
    z = iter (λ c → next (F² c) (nzF² c)) zero

    γ³ : ℕ → E.T
    γ³ = E.γT (E.Ωs u₂) u₂

    sγ³ : ∀ n → M² (γ³ n) (z (suc n))
    sγ³ zero    = mw hβ₂ (◃l zero)
    sγ³ (suc n) = mw (P² (sγ³ n)) (◃l zero)
```
