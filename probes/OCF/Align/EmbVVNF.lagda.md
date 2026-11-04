# 值验收 (标准形): $\psi_0(\Omega_{\psi_1(1)\cdot(k+2)+\Omega\cdot m+\theta})$

> 入口 [EmbVV](EmbVV.lagda.md). 读记号. `NF-ψ⁺ k m`: `NF₁ θ`, `Ctbl θ`, $\theta<\psi_0(\Omega_{\psi_1(1)\cdot(k+2)+\Omega\cdot(m+1)})$ $\Rightarrow$ `NF₁` $\psi_0(\Omega_{\psi_1(1)\cdot(k+2)+\Omega\cdot m+\theta})$. 与 [OrdLabNFTop](OrdLabNFTop.lagda.md) 的 `NF-ψ` 同形, 多一层前缀的比较 (`coreS`). 这里的 `NF₁` 是 [EmbVVLZStandardOmega](EmbVVLZStandardOmega.lagda.md) 的, `Sb` 多一族 `sψ⁺`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVNF where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_<_ to _<ⁿ_; _≤_ to _≤ⁿ_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
import OCF.Align.EBO as E
open E using (T; PT; natT; Ωt; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Standard using (Ctbl; c[]; c∷; []≤)
open import OCF.Align.EmbVVLZStandardOmega using (NF₁; NFᴾ₁; n[]; n∷; nψ; Sb; sC; sΩ; sΩ²; sψ; sψ⁺; ψ¹; pk; bnd[]; Vis₁; vh; vd; vs; vt; Bnd₁; Ωᵐ; Ω₁; NFψ⁺)
open import OCF.Align.OrdLabZClosure using (lt→<; lt→<ᴾ; <ᵀ-trans; eq→≡; eq→≡ᴾ)
open import OCF.Align.OrdLabZBachmann using (gt→<; <ᵀ-irrefl; Hd≤)
open import OCF.Align.LadderLabZSystemOmega using (cmp-CΩ)
open import OCF.Align.EmbVVOZUniform3Base using (ψ₀ᵗ)
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

visTail : ∀ p {y d es} → Vis₁ [] d (Ωᵐ p (ψᵗ y d ∷ es))
visTail zero = vh ([]≤ _)
visTail (suc p) = vt (visTail p)

visTailK : ∀ K p {y d es} → Vis₁ [] d (ψ¹ ∷ pk K (ψ¹ ∷ Ωᵐ p (ψᵗ y d ∷ es)))
visTailK zero p = vt (vt (visTail p))
visTailK (suc K) p = vt (visTailK K p)

no-ψ¹ : ∀ {e z} → (ψ¹ ∷ e) <ᵗ (Ω₁ ∷ z) → ⊥
no-ψ¹ (E.hd< (E.lv< q)) = <ᵀ-irrefl q
no-ψ¹ (E.hd< (E.ar< ()))

inv-ψ : ∀ {u x ys U} → (ψᵗ u x ∷ ys) <ᵗ (ψᵗ U [] ∷ []) → u <ᵗ U
inv-ψ (E.hd< (E.lv< q)) = q
inv-ψ (E.hd< (E.ar< ()))
inv-ψ (E.tl< ())

ctbl<ψ : ∀ {u} (X : T) → Ctbl u → u <ᵗ (ψ¹ ∷ X)
ctbl<ψ X c[] = E.[]<
ctbl<ψ X (c∷ c) = E.hd< (E.lv< E.[]<)

inv-tlψ : ∀ {a b} → (ψ¹ ∷ a) <ᵗ (ψ¹ ∷ b) → a <ᵗ b
inv-tlψ (E.hd< (E.lv< q)) = ⊥-elim (<ᵀ-irrefl q)
inv-tlψ (E.hd< (E.ar< q)) = ⊥-elim (<ᵀ-irrefl q)
inv-tlψ (E.tl< r) = r

-- 前缀比首项 Ω 的尾巴高
Ωᵐ<ψ : ∀ p {e} (X : T) → Ctbl e → Ωᵐ p e <ᵗ (ψ¹ ∷ X)
Ωᵐ<ψ zero X ce = ctbl<ψ X ce
Ωᵐ<ψ (suc p) X ce = E.hd< (E.ar< E.[]<)

Ωᵐ<pk : ∀ L p {e} (X : T) → Ctbl e → Ωᵐ p e <ᵗ pk L (ψ¹ ∷ X)
Ωᵐ<pk zero p X ce = Ωᵐ<ψ p X ce
Ωᵐ<pk (suc L) p X ce = Ωᵐ<ψ p (pk L (ψ¹ ∷ X)) ce

no-ψ¹pk : ∀ K {t z} → pk K (ψ¹ ∷ t) <ᵗ (Ω₁ ∷ z) → ⊥
no-ψ¹pk zero q = no-ψ¹ q
no-ψ¹pk (suc K) q = no-ψ¹ q
```

## §2 目标

`W X` $=\psi_1(1)\cdot(k+2)+X$.

```agda
module _ (k m : ℕ) {c : T} (pm : c <ᵗ ψ₀ᵗ (Ωt (ψ¹ ∷ pk k (ψ¹ ∷ Ω₁ ∷ Ωᵐ m [])))) where
  W : T → T
  W X = ψ¹ ∷ pk k (ψ¹ ∷ X)

  Tg : T
  Tg = Ωt (W (Ωᵐ m c))

  arg< : ∀ {a} → (ψᵗ [] a ∷ []) ≤₁ c → a <ᵗ Ωt (W (Ω₁ ∷ Ωᵐ m []))
  arg< l with ≤₁-tr′ l
    where
    ≤₁-tr′ : ∀ {x} → x ≤₁ c → x <ᵗ ψ₀ᵗ (Ωt (W (Ω₁ ∷ Ωᵐ m [])))
    ≤₁-tr′ (inj₁ q) = <ᵀ-trans q pm
    ≤₁-tr′ (inj₂ refl) = pm
  ... | E.hd< (E.lv< ())
  ... | E.hd< (E.ar< q) = q
  ... | E.tl< ()

  coreS : ∀ K L p {e} → Ctbl e → pk K (ψ¹ ∷ Ωᵐ p e) <ᵗ pk L (ψ¹ ∷ Ω₁ ∷ Ωᵐ m []) → (K ≡ L → p ≡ m → c ≤₁ e → ⊥) → pk K (ψ¹ ∷ Ωᵐ p e) <ᵗ pk L (ψ¹ ∷ Ωᵐ m c)
  coreS zero zero p ce q bad = E.tl< (tailLt p m ce (bad refl) (λ lp → noLt p (suc m) lp (inv-tlψ q)))
  coreS (suc K) zero p ce q bad = ⊥-elim (no-ψ¹pk K (inv-tlψ q))
  coreS zero (suc L) p ce q bad = E.tl< (Ωᵐ<pk L p (Ωᵐ m c) ce)
  coreS (suc K) (suc L) p ce q bad = E.tl< (coreS K L p ce (inv-tlψ q) (λ e → bad (cong suc e)))

  gk : ∀ {u x ys} → Sb u → Bnd₁ [] (ψᵗ u x ∷ ys) → (ψᵗ [] (ψᵗ u x ∷ ys) ∷ []) ≤₁ c → (ψᵗ u x ∷ ys) <ᵗ Tg
  gk (sC cu) b l = E.hd< (E.lv< (ctbl<ψ _ cu))
  gk (sΩ ce) b l = E.hd< (E.lv< (E.hd< (E.ar< E.[]<)))
  gk (sΩ² n ce) b l = E.hd< (E.lv< (E.hd< (E.ar< E.[]<)))
  gk (sψ p ce) b l = E.hd< (E.lv< (E.tl< (Ωᵐ<pk k p (Ωᵐ m c) ce)))
  gk {x = x} {ys = ys} (sψ⁺ k′ p {c = e} ce) b l = E.hd< (E.lv< (E.tl< (coreS k′ k p ce (inv-tlψ (inv-ψ (arg< l))) bad)))
    where
    bad : k′ ≡ k → p ≡ m → c ≤₁ e → ⊥
    bad _ _ = gb ce b l
      where
      gb : ∀ {e} → Ctbl e → Bnd₁ [] (ψᵗ (ψ¹ ∷ pk k′ (ψ¹ ∷ Ωᵐ p e)) x ∷ ys) → (ψᵗ [] (ψᵗ (ψ¹ ∷ pk k′ (ψ¹ ∷ Ωᵐ p e)) x ∷ ys) ∷ []) ≤₁ c → c ≤₁ e → ⊥
      gb c[] b l (inj₁ ())
      gb c[] b (inj₁ ()) (inj₂ refl)
      gb c[] b (inj₂ ()) (inj₂ refl)
      gb (c∷ ct) b l ce′ = <ᵀ-irrefl (≤₁-tr (≤₁-tr (E.hd< (E.ar< (b (vs ([]≤ _) (visTailK k′ p))))) l) ce′)

  key : ∀ {a} → NF₁ a → Bnd₁ [] a → (ψᵗ [] a ∷ []) ≤₁ c → a <ᵗ Tg
  key n[] b l = E.[]<
  key (n∷ (nψ nu su na bx) nys hd) b l = gk su b l

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

  bndΩ : ∀ j {ζ} → NF₁ c → Ctbl c → Hb c → Vis₁ [] ζ (Ωᵐ j c) → ζ <ᵗ Tg
  bndΩ zero nθ cθ hb v = visC nθ cθ hb v
  bndΩ (suc j) nθ cθ hb (vh _) = E.[]<
  bndΩ (suc j) nθ cθ hb (vd _ ())
  bndΩ (suc j) nθ cθ hb (vs _ (vh _)) = E.[]<
  bndΩ (suc j) nθ cθ hb (vs _ (vd _ ()))
  bndΩ (suc j) nθ cθ hb (vs _ (vs _ ()))
  bndΩ (suc j) nθ cθ hb (vs _ (vt ()))
  bndΩ (suc j) nθ cθ hb (vt v) = bndΩ j nθ cθ hb v

  -- ψ¹ 的下标与参数都是 1
  hψ¹ : ∀ {ζ r} → (Vis₁ [] ζ r → ζ <ᵗ Tg) → Vis₁ [] ζ (ψ¹ ∷ r) → ζ <ᵗ Tg
  hψ¹ k₁ (vh _) = E.hd< (E.lv< E.[]<)
  hψ¹ k₁ (vd _ (vh _)) = E.[]<
  hψ¹ k₁ (vd _ (vd _ ()))
  hψ¹ k₁ (vd _ (vs _ ()))
  hψ¹ k₁ (vd _ (vt ()))
  hψ¹ k₁ (vs _ (vh _)) = E.[]<
  hψ¹ k₁ (vs _ (vd _ ()))
  hψ¹ k₁ (vs _ (vs _ ()))
  hψ¹ k₁ (vs _ (vt ()))
  hψ¹ k₁ (vt v) = k₁ v

  bndW : ∀ K {ζ} → NF₁ c → Ctbl c → Hb c → Vis₁ [] ζ (ψ¹ ∷ pk K (ψ¹ ∷ Ωᵐ m c)) → ζ <ᵗ Tg
  bndW zero nθ cθ hb v = hψ¹ (hψ¹ (bndΩ m nθ cθ hb)) v
  bndW (suc K) nθ cθ hb v = hψ¹ (bndW K nθ cθ hb) v

Hb-self : ∀ {k m} t (pm : t <ᵗ ψ₀ᵗ (Ωt (ψ¹ ∷ pk k (ψ¹ ∷ Ω₁ ∷ Ωᵐ m [])))) → Hb k m pm t
Hb-self [] pm = tt
Hb-self (x ∷ []) pm = inj₂ refl
Hb-self (x ∷ y ∷ ys) pm = inj₁ (E.tl< E.[]<)

NF-ψ⁺ : ∀ k m {θ} → NF₁ θ → Ctbl θ → θ <ᵗ ψ₀ᵗ (Ωt (ψ¹ ∷ pk k (ψ¹ ∷ Ω₁ ∷ Ωᵐ m []))) → NF₁ (ψ₀ᵗ (Ωt (ψ¹ ∷ pk k (ψ¹ ∷ Ωᵐ m θ))))
NF-ψ⁺ k m {θ} nθ cθ pm =
  n∷ (nψ n[] (sC c[]) (n∷ (nψ (NFψ⁺ k m nθ cθ) (sψ⁺ k m cθ) n[] bnd[]) n[] tt)
     (λ { (vh _) → E.[]< ; (vd _ ()) ; (vs _ v) → bndW k m pm k nθ cθ (Hb-self θ pm) v ; (vt ()) })) n[] tt
```
