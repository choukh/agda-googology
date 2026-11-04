# 高度上的标签 (二): $\psi_0(\Omega_{\psi_1(1)+\Omega\cdot m+\theta})$ 的标准形

> **判决: HOLDS (编译过, 无条件).** 结论写在 [LadderLab](LadderLab.lagda.md). `NF-ψ m`: `NF₁ θ`, `Ctbl θ`, $\theta<\psi_0(\Omega_{\psi_1(1)+\Omega\cdot(m+1)})$ $\Rightarrow$ `NF₁` $\psi_0(\Omega_{\psi_1(1)+\Omega\cdot m+\theta})$. 纯记号. 与 [ScafLadderNF](ScafLadderNF.lagda.md) 的 `NF-Ωᵐ` 同形, 上界同样不可少. 比 $\Omega$ 版多一件事: 叶子 $\Omega_{\psi_1(1)+\ldots}$ 的下标里有可见参数 $1$ (`vs`, `vh`), 由 $1<\Omega_{\ldots}$ 给. 下标比较的新情形只有 `sψ`; 其余下标的首项都小于 $\psi_1(1)$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabNFTop where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_<_ to _<ⁿ_; _≤_ to _≤ⁿ_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

import OCF.Align.EBO as E
open E using (T; PT; natT; Ωt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Standard using (Ctbl; c[]; c∷; []≤)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NFᴾ₁; n[]; n∷; nψ; Sb; sC; sΩ; sΩ²; sψ; ψ¹; bnd[]; Vis₁; vh; vd; vs; vt; Bnd₁; Ωᵐ; Ω₁; NFψ¹)
open import OCF.Align.Closure using (lt→<; lt→<ᴾ; <ᵀ-trans; eq→≡; eq→≡ᴾ)
open import OCF.Align.Bachmann using (gt→<; <ᵀ-irrefl; Hd≤)
open import OCF.Align.LadderLabZUniform3Base using (ψ₀ᵗ)
open import OCF.Align.LadderLabNFOmega using (_≤₁_; ≤₁-tr; tailLt; noLt; visTail; inv-ψ; Hb; Hb-self)
```

## §1 剥层

```agda
ctbl<ψ : ∀ {u} (X : T) → Ctbl u → u <ᵗ (ψ¹ ∷ X)
ctbl<ψ X c[] = E.[]<
ctbl<ψ X (c∷ c) = E.hd< (E.lv< E.[]<)

inv-tlψ : ∀ {a b} → (ψ¹ ∷ a) <ᵗ (ψ¹ ∷ b) → a <ᵗ b
inv-tlψ (E.hd< (E.lv< q)) = ⊥-elim (<ᵀ-irrefl q)
inv-tlψ (E.hd< (E.ar< q)) = ⊥-elim (<ᵀ-irrefl q)
inv-tlψ (E.tl< r) = r

visTailψ : ∀ p {y d es} → Vis₁ [] d (ψ¹ ∷ Ωᵐ p (ψᵗ y d ∷ es))
visTailψ zero = vt (vh ([]≤ _))
visTailψ (suc p) = vt (visTail p)

badTψ : ∀ p {e x ys c} → Ctbl e → Bnd₁ [] (ψᵗ (ψ¹ ∷ Ωᵐ p e) x ∷ ys) → (ψᵗ [] (ψᵗ (ψ¹ ∷ Ωᵐ p e) x ∷ ys) ∷ []) ≤₁ c → c ≤₁ e → ⊥
badTψ p c[] b l (inj₁ ())
badTψ p c[] b (inj₁ ()) (inj₂ refl)
badTψ p c[] b (inj₂ ()) (inj₂ refl)
badTψ p (c∷ ct) b l ce′ = <ᵀ-irrefl (≤₁-tr (≤₁-tr (E.hd< (E.ar< (b (vs ([]≤ _) (visTailψ p))))) l) ce′)

-- 目标的上界 B = ψ₁(1)+Ω·(m+1)
module _ (m : ℕ) {c : T} (pm : c <ᵗ ψ₀ᵗ (Ωt (ψ¹ ∷ Ω₁ ∷ Ωᵐ m []))) where
  Tg : T
  Tg = Ωt (ψ¹ ∷ Ωᵐ m c)

  arg< : ∀ {a} → (ψᵗ [] a ∷ []) ≤₁ c → a <ᵗ Ωt (ψ¹ ∷ Ω₁ ∷ Ωᵐ m [])
  arg< l with ≤₁-tr′ l
    where
    ≤₁-tr′ : ∀ {x} → x ≤₁ c → x <ᵗ ψ₀ᵗ (Ωt (ψ¹ ∷ Ω₁ ∷ Ωᵐ m []))
    ≤₁-tr′ (inj₁ q) = <ᵀ-trans q pm
    ≤₁-tr′ (inj₂ refl) = pm
  ... | E.hd< (E.lv< ())
  ... | E.hd< (E.ar< q) = q
  ... | E.tl< ()

  key : ∀ {a} → NF₁ a → Bnd₁ [] a → (ψᵗ [] a ∷ []) ≤₁ c → a <ᵗ Tg
  key n[] b l = E.[]<
  key (n∷ {x = ψᵗ u x} (nψ nu (sC cu) na bx) nys hd) b l = E.hd< (E.lv< (ctbl<ψ (Ωᵐ m c) cu))
  key (n∷ {x = ψᵗ (_ ∷ e) x} (nψ nu (sΩ ce) na bx) nys hd) b l = E.hd< (E.lv< (E.hd< (E.ar< E.[]<)))
  key (n∷ {x = ψᵗ (_ ∷ _ ∷ _) x} (nψ nu (sΩ² k ce) na bx) nys hd) b l = E.hd< (E.lv< (E.hd< (E.ar< E.[]<)))
  key (n∷ {x = ψᵗ (_ ∷ _) x} {xs = ys} (nψ nu (sψ p ce) na bx) nys hd) b l = sub p ce b l
    where
    sub : ∀ p {e x ys} → Ctbl e → Bnd₁ [] (ψᵗ (ψ¹ ∷ Ωᵐ p e) x ∷ ys) → (ψᵗ [] (ψᵗ (ψ¹ ∷ Ωᵐ p e) x ∷ ys) ∷ []) ≤₁ c → (ψᵗ (ψ¹ ∷ Ωᵐ p e) x ∷ ys) <ᵗ Tg
    sub p {e} {x} {ys} ce b l = E.hd< (E.lv< (E.tl< (tailLt p m ce ¬eq ¬ov)))
      where
      ¬ov : m <ⁿ p → ⊥
      ¬ov lp = noLt p (suc m) lp (inv-tlψ (inv-ψ (arg< l)))
      ¬eq : p ≡ m → c ≤₁ e → ⊥
      ¬eq eqp ce′ = badTψ p ce b l ce′

  Hbc : T → Set
  Hbc = Hb₀
    where
    Hb₀ : T → Set
    Hb₀ []       = ⊤
    Hb₀ (x ∷ xs) = (x ∷ []) ≤₁ c

  Hb-tail : ∀ {x xs} → (x ∷ []) ≤₁ c → Hd≤ xs x → Hbc xs
  Hb-tail {xs = []} l h = tt
  Hb-tail {x} {y ∷ ys} l (inj₁ e) = inj₁ (≤₁-tr (E.hd< (lt→<ᴾ y x e)) l)
  Hb-tail {x} {y ∷ ys} l (inj₂ e) rewrite eq→≡ᴾ y x e = l

  visC : ∀ {t ζ} → NF₁ t → Ctbl t → Hbc t → Vis₁ [] ζ t → ζ <ᵗ Tg
  visC (n∷ (nψ _ _ na bx) nxs h) (c∷ ct) hb (vh _) = key na bx hb
  visC (n∷ (nψ _ _ na bx) nxs h) (c∷ ct) hb (vd _ v) = <ᵀ-trans (bx v) (key na bx hb)
  visC (n∷ (nψ _ _ na bx) nxs h) (c∷ ct) hb (vs _ ())
  visC (n∷ (nψ _ _ na bx) nxs h) (c∷ ct) hb (vt v) = visC nxs ct (Hb-tail hb h) v

  bndΩ : ∀ k {ζ} → NF₁ c → Ctbl c → Hbc c → Vis₁ [] ζ (Ωᵐ k c) → ζ <ᵗ Tg
  bndΩ zero nθ cθ hb v = visC nθ cθ hb v
  bndΩ (suc k) nθ cθ hb (vh _) = E.[]<
  bndΩ (suc k) nθ cθ hb (vd _ ())
  bndΩ (suc k) nθ cθ hb (vs _ (vh _)) = E.[]<
  bndΩ (suc k) nθ cθ hb (vs _ (vd _ ()))
  bndΩ (suc k) nθ cθ hb (vs _ (vs _ ()))
  bndΩ (suc k) nθ cθ hb (vs _ (vt ()))
  bndΩ (suc k) nθ cθ hb (vt v) = bndΩ k nθ cθ hb v

  -- ψ¹ 的下标与参数都是 1
  bndψ : ∀ {ζ} → NF₁ c → Ctbl c → Hbc c → Vis₁ [] ζ (ψ¹ ∷ Ωᵐ m c) → ζ <ᵗ Tg
  bndψ nθ cθ hb (vh _) = E.hd< (E.lv< E.[]<)
  bndψ nθ cθ hb (vd _ (vh _)) = E.[]<
  bndψ nθ cθ hb (vd _ (vd _ ()))
  bndψ nθ cθ hb (vd _ (vs _ ()))
  bndψ nθ cθ hb (vd _ (vt ()))
  bndψ nθ cθ hb (vs _ (vh _)) = E.[]<
  bndψ nθ cθ hb (vs _ (vd _ ()))
  bndψ nθ cθ hb (vs _ (vs _ ()))
  bndψ nθ cθ hb (vs _ (vt ()))
  bndψ nθ cθ hb (vt v) = bndΩ m nθ cθ hb v

Hb-selfψ : ∀ {m} t (pm : t <ᵗ ψ₀ᵗ (Ωt (ψ¹ ∷ Ω₁ ∷ Ωᵐ m []))) → Hbc m pm t
Hb-selfψ [] pm = tt
Hb-selfψ (x ∷ []) pm = inj₂ refl
Hb-selfψ (x ∷ y ∷ ys) pm = inj₁ (E.tl< E.[]<)

NF-ψ : ∀ m {θ} → NF₁ θ → Ctbl θ → θ <ᵗ ψ₀ᵗ (Ωt (ψ¹ ∷ Ω₁ ∷ Ωᵐ m [])) → NF₁ (ψ₀ᵗ (Ωt (ψ¹ ∷ Ωᵐ m θ)))
NF-ψ m {θ} nθ cθ pm =
  n∷ (nψ n[] (sC c[]) (n∷ (nψ (NFψ¹ m nθ cθ) (sψ m cθ) n[] bnd[]) n[] tt)
     (λ { (vh _) → E.[]< ; (vd _ ()) ; (vs _ v) → bndψ m pm nθ cθ (Hb-selfψ θ pm) v ; (vt ()) })) n[] tt
```
