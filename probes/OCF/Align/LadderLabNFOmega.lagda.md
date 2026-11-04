> **机械改写, 验收用.** 由 `ScafLadderNF` 经 `Survey/scripts/ladderlab/mk_class.py` 生成: 对高度结构 `HtS` 抽象, 记号前缀换成 `PxS` 的 `P`; 见 [LadderLab](LadderLab.lagda.md). 下面的文字来自原文件.

# 阶梯 (十四): $\psi_0(\Omega_{\Omega\cdot(m+1)+\theta})$ 的标准形

> 结论写在 [ScafLadder](ScafLadder.lagda.md). `NF-Ωᵐ m`: `NF₁ θ`, `Ctbl θ`, $\theta<\psi_0(\Omega_{\Omega\cdot(m+2)})$ $\Rightarrow$ `NF₁` $\psi_0(\Omega_{\Omega\cdot(m+1)+\theta})$. 这是纯记号. 上界不可少: `Sb` 现在含一切 $\Omega\cdot n+c$. 与 [Uniform5Label](Uniform5Label.lagda.md) §1 同形, 加上对 $m$ 的剥层.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabNFOmega where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_<_ to _<ⁿ_; _≤_ to _≤ⁿ_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

import OCF.Align.EBO as E
open E using (T; PT; natT; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Standard using (Ctbl; c[]; c∷; []≤)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NFᴾ₁; n[]; n∷; nψ; Sb; sC; sΩ; sΩ²; sψ; ψ¹; bnd[]; Vis₁; vh; vd; vs; vt; Bnd₁; Ωᵐ; Ω₁; NFΩᵐ; SbΩᵐ; hdΩᵐ; nfΩ₁)
open import OCF.Align.Closure using (lt→<; lt→<ᴾ; <ᵀ-trans; eq→≡; eq→≡ᴾ)
open import OCF.Align.Bachmann using (gt→<; <ᵀ-irrefl; Hd≤)
open import OCF.Align.LadderLabZSystemOmega using (cmp-CΩ)
open import OCF.Align.LadderLabZUniform3Base using (ψ₀ᵗ)
```

## §1 剥层

```agda
_≤₁_ : T → T → Set
a ≤₁ c = (a <ᵗ c) ⊎ (a ≡ c)

≤₁-tr : ∀ {a b c} → a <ᵗ b → b ≤₁ c → a <ᵗ c
≤₁-tr p (inj₁ q) = <ᵀ-trans p q
≤₁-tr p (inj₂ refl) = p

tailLt : ∀ p m {e c} → Ctbl e → (p ≡ m → c ≤₁ e → ⊥) → (m <ⁿ p → ⊥) → Ωᵐ p e <ᵗ Ωᵐ m c
tailLt zero zero {e} {c} ce ¬eq ¬ov with cmpᵀ e c in ec
... | lt = lt→< e c ec
... | eq = ⊥-elim (¬eq refl (inj₂ (sym (eq→≡ e c ec))))
... | gt = ⊥-elim (¬eq refl (inj₁ (gt→< e c ec)))
tailLt zero (suc m) {e} {c} ce ¬eq ¬ov = lt→< e (Ω₁ ∷ Ωᵐ m c) (cmp-CΩ ce (Ωᵐ m c))
tailLt (suc p) zero ce ¬eq ¬ov = ⊥-elim (¬ov (s≤s z≤n))
tailLt (suc p) (suc m) ce ¬eq ¬ov = E.tl< (tailLt p m ce (λ e → ¬eq (cong suc e)) (λ l → ¬ov (s≤s l)))

noLt : ∀ k q {e} → q ≤ⁿ k → Ωᵐ k e <ᵗ Ωᵐ q [] → ⊥
noLt k zero le ()
noLt (suc k) (suc q) (s≤s le) (E.hd< p) = <ᵀ-irrefl {Ω₁ ∷ []} (E.hd< p)
noLt (suc k) (suc q) (s≤s le) (E.tl< r) = noLt k q le r

visTail : ∀ p {y d es} → Vis₁ [] d (Ω₁ ∷ Ωᵐ p (ψᵗ y d ∷ es))
visTail zero = vt (vh ([]≤ _))
visTail (suc p) = vt (visTail p)

badT : ∀ p {e x ys c} → Ctbl e → Bnd₁ [] (ψᵗ (Ω₁ ∷ Ωᵐ p e) x ∷ ys) → (ψᵗ [] (ψᵗ (Ω₁ ∷ Ωᵐ p e) x ∷ ys) ∷ []) ≤₁ c → c ≤₁ e → ⊥
badT p c[] b l (inj₁ ())
badT p c[] b (inj₁ ()) (inj₂ refl)
badT p c[] b (inj₂ ()) (inj₂ refl)
badT p (c∷ ct) b l ce′ = <ᵀ-irrefl (≤₁-tr (≤₁-tr (E.hd< (E.ar< (b (vs ([]≤ _) (visTail p))))) l) ce′)

no-ψ¹ : ∀ {e z} → (ψ¹ ∷ e) <ᵗ (Ω₁ ∷ z) → ⊥
no-ψ¹ (E.hd< (E.lv< q)) = <ᵀ-irrefl q
no-ψ¹ (E.hd< (E.ar< ()))

inv-ψ : ∀ {u x ys U} → (ψᵗ u x ∷ ys) <ᵗ (ψᵗ U [] ∷ []) → u <ᵗ U
inv-ψ (E.hd< (E.lv< q)) = q
inv-ψ (E.hd< (E.ar< ()))
inv-ψ (E.tl< ())

-- 目标的上界 B = Ω·(m+2)
module _ (m : ℕ) {c : T} (pm : c <ᵗ ψ₀ᵗ (Ωt (Ω₁ ∷ Ω₁ ∷ Ωᵐ m []))) where
  Tg : T
  Tg = Ωt (Ω₁ ∷ Ωᵐ m c)

  arg< : ∀ {a} → (ψᵗ [] a ∷ []) ≤₁ c → a <ᵗ Ωt (Ω₁ ∷ Ω₁ ∷ Ωᵐ m [])
  arg< l with ≤₁-tr′ l
    where
    ≤₁-tr′ : ∀ {x} → x ≤₁ c → x <ᵗ ψ₀ᵗ (Ωt (Ω₁ ∷ Ω₁ ∷ Ωᵐ m []))
    ≤₁-tr′ (inj₁ q) = <ᵀ-trans q pm
    ≤₁-tr′ (inj₂ refl) = pm
  ... | E.hd< (E.lv< ())
  ... | E.hd< (E.ar< q) = q
  ... | E.tl< ()

  key : ∀ {a} → NF₁ a → Bnd₁ [] a → (ψᵗ [] a ∷ []) ≤₁ c → a <ᵗ Tg
  key n[] b l = E.[]<
  key (n∷ {x = ψᵗ (_ ∷ _) x} (nψ nu (sψ k ce) na bx) nys hd) b l = ⊥-elim (no-ψ¹ (inv-ψ (arg< l)))
  key (n∷ {x = ψᵗ u x} (nψ nu (sC cu) na bx) nys hd) b l = E.hd< (E.lv< (lt→< u (Ω₁ ∷ Ωᵐ m c) (cmp-CΩ cu (Ωᵐ m c))))
  key (n∷ {x = ψᵗ (_ ∷ e) x} {xs = ys} (nψ nu (sΩ ce) na bx) nys hd) b l = sub 0 ce b l
    where
    sub : ∀ p {e x ys} → Ctbl e → Bnd₁ [] (ψᵗ (Ω₁ ∷ Ωᵐ p e) x ∷ ys) → (ψᵗ [] (ψᵗ (Ω₁ ∷ Ωᵐ p e) x ∷ ys) ∷ []) ≤₁ c → (ψᵗ (Ω₁ ∷ Ωᵐ p e) x ∷ ys) <ᵗ Tg
    sub p {e} {x} {ys} ce b l = E.hd< (E.lv< (E.tl< (tailLt p m ce ¬eq ¬ov)))
      where
      ¬ov : m <ⁿ p → ⊥
      ¬ov lp = noLt (suc p) (suc (suc m)) (s≤s lp) (inv-ψ (arg< l))
      ¬eq : p ≡ m → c ≤₁ e → ⊥
      ¬eq eqp ce′ = badT p ce b l ce′
  key (n∷ {x = ψᵗ (_ ∷ _ ∷ _) x} {xs = ys} (nψ nu (sΩ² k ce) na bx) nys hd) b l = sub′ (suc k) ce b l
    where
    sub′ : ∀ p {e x ys} → Ctbl e → Bnd₁ [] (ψᵗ (Ω₁ ∷ Ωᵐ p e) x ∷ ys) → (ψᵗ [] (ψᵗ (Ω₁ ∷ Ωᵐ p e) x ∷ ys) ∷ []) ≤₁ c → (ψᵗ (Ω₁ ∷ Ωᵐ p e) x ∷ ys) <ᵗ Tg
    sub′ p {e} {x} {ys} ce b l = E.hd< (E.lv< (E.tl< (tailLt p m ce ¬eq ¬ov)))
      where
      ¬ov : m <ⁿ p → ⊥
      ¬ov lp = noLt (suc p) (suc (suc m)) (s≤s lp) (inv-ψ (arg< l))
      ¬eq : p ≡ m → c ≤₁ e → ⊥
      ¬eq eqp ce′ = badT p ce b l ce′

  Hb : T → Set
  Hb []       = ⊤
  Hb (x ∷ xs) = (x ∷ []) ≤₁ c

  Hb-tail : ∀ {x xs} → (x ∷ []) ≤₁ c → Hd≤ xs x → Hb xs
  Hb-tail {xs = []} l h = tt
  Hb-tail {x} {y ∷ ys} l (inj₁ e) = inj₁ (≤₁-tr (E.hd< (lt→<ᴾ y x e)) l)
  Hb-tail {x} {y ∷ ys} l (inj₂ e) rewrite eq→≡ᴾ y x e = l

  visC : ∀ {t ζ} → NF₁ t → Ctbl t → Hb t → Vis₁ [] ζ t → ζ <ᵗ Tg
  visC (n∷ (nψ _ _ na bx) nxs h) (c∷ ct) hb (vh _) = key na bx hb
  visC (n∷ (nψ _ _ na bx) nxs h) (c∷ ct) hb (vd _ v) = <ᵀ-trans (bx v) (key na bx hb)
  visC (n∷ (nψ _ _ na bx) nxs h) (c∷ ct) hb (vs _ ())
  visC (n∷ (nψ _ _ na bx) nxs h) (c∷ ct) hb (vt v) = visC nxs ct (Hb-tail hb h) v

  bndΩ : ∀ k {ζ} → NF₁ c → Ctbl c → Hb c → Vis₁ [] ζ (Ωᵐ k c) → ζ <ᵗ Tg
  bndΩ zero nθ cθ hb v = visC nθ cθ hb v
  bndΩ (suc k) nθ cθ hb (vh _) = E.[]<
  bndΩ (suc k) nθ cθ hb (vd _ ())
  bndΩ (suc k) nθ cθ hb (vs _ (vh _)) = E.[]<
  bndΩ (suc k) nθ cθ hb (vs _ (vd _ ()))
  bndΩ (suc k) nθ cθ hb (vs _ (vs _ ()))
  bndΩ (suc k) nθ cθ hb (vs _ (vt ()))
  bndΩ (suc k) nθ cθ hb (vt v) = bndΩ k nθ cθ hb v

Hb-self : ∀ {m} t (pm : t <ᵗ ψ₀ᵗ (Ωt (Ω₁ ∷ Ω₁ ∷ Ωᵐ m []))) → Hb m pm t
Hb-self [] pm = tt
Hb-self (x ∷ []) pm = inj₂ refl
Hb-self (x ∷ y ∷ ys) pm = inj₁ (E.tl< E.[]<)

NF-Ωᵐ : ∀ m {θ} → NF₁ θ → Ctbl θ → θ <ᵗ ψ₀ᵗ (Ωt (Ω₁ ∷ Ω₁ ∷ Ωᵐ m [])) → NF₁ (ψ₀ᵗ (Ωt (Ω₁ ∷ Ωᵐ m θ)))
NF-Ωᵐ m {θ} nθ cθ pm =
  n∷ (nψ n[] (sC c[]) (n∷ (nψ (NFΩᵐ (suc m) nθ cθ) (SbΩᵐ m cθ) n[] bnd[]) n[] tt)
     (λ { (vh _) → E.[]< ; (vd _ ()) ; (vs _ v) → bndΩ m pm (suc m) nθ cθ (Hb-self θ pm) v ; (vt ()) })) n[] tt

-- θ 的上界在 θ 小的时候平凡
1<ψ₀ : ∀ {b x xs} → b ≡ x ∷ xs → natT 1 <ᵗ ψ₀ᵗ b
1<ψ₀ refl = E.hd< (E.ar< E.[]<)
```
