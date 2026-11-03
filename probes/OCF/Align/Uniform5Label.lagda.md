# 统一形 (五): $\psi_0(\Omega_{\Omega+\eta})$ 与 $\psi_0(\Omega_{\Omega\cdot2})$ 的标签

> 接 [Uniform5Eval](Uniform5Eval.lagda.md). 结论先说:
>
> 1. **`TΩ-label`: 对一切带标签的可数树 $Y$ (标签 $\theta\in$ `NF₁`), $\psi_0(\Omega_{\Omega+\theta})$ 的标签无条件成立.** 这包含 Uniform4 的 $\theta=c\in\mathbb N$ 与 $\omega$, 也包含 $\theta=\psi_0(\Omega_{\Omega+\theta'})$.
> 2. **`NF-Ω`: `NF₁ θ`, `Ctbl θ` $\Rightarrow$ `NF₁ ψ₀(Ω_{Ω+θ})`.** 这不是平凡的: `vs` 让 $\theta$ 的参数对 $\Omega_{\Omega+\theta}$ 可见. 证明 (§1) 只用 `Bnd₁` 与 `Sb`: 若 $a$ 的首项下标 $u\ge\Omega+\theta$, 则 $u=\Omega+e$, $e=\psi_0(d)+\cdots\ge\theta\ge\psi_0(a)$, 而 $d$ 对 $a$ 可见, 所以 $d<a$, 矛盾.
> 3. **`TΩ·2-label` ([Uniform5Top](Uniform5Top.lagda.md)): $\psi_0(\Omega_{\Omega\cdot2})$ 的标签无条件成立**, 基本列是 EBO 的 ($\gamma_0=1$, $\gamma_{n+1}=\psi_0(\Omega_{\Omega+\gamma_n})$). 这个项本身不在 `NF₁` (`¬NF-Ω·2`), 但它的基本列全在: 顶层一步 ([Uniform5Clo](Uniform5Clo.lagda.md)) 把 `clo0` 的 "`NF₁` 顶层 ⟹ 基本列的 `NF₁` 与单调" 换成直接的证明 (`nfγ`, `mono`). **这只对顶层节点有效**, 见 [Uniform5NF](Uniform5NF.lagda.md) 的裁决.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform5Label where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.StandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Align.Decouple using (Idx; lvI; Lab0[])
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.Stage2Label using (one⁰)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.OmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW; cofW)
open import OCF.Align.Closure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Align.StandardOmega using ()
open import OCF.Align.GoodLBase
open import OCF.Align.UniformS
open import OCF.Align.Uniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.Uniform3Rel
open import OCF.Align.Uniform3SqABase
open import OCF.Align.Uniform3Hon
open import OCF.Align.Uniform3Depth2Class
open import OCF.Align.Uniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Align.Uniform3Depth2Fold using (Zc₀; Zc₀-of; InpO)
open import OCF.Align.Uniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr; ∅ᴿ-goodʰ)
open import OCF.Align.Uniform5Head
open import OCF.Align.Uniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.Uniform4Two
open import OCF.Align.Uniform5Class
open import OCF.Align.Uniform5Close
open import OCF.Align.Uniform5Tail
open import OCF.Align.Uniform5Tr
open import OCF.Align.Uniform5Psi
open import OCF.Align.Uniform5Rel
open import OCF.Align.Uniform5RelPsi
open import OCF.Align.Uniform3SqA using (LW0→LW)
open import OCF.Align.Uniform5Eval
open GRᴬ
open import OCF.Align.Standard using (Ctbl; c[]; c∷; []≤)
open import OCF.Align.StandardOmega using (NFᴾ₁; n[]; n∷; nψ; Sb; sC; sΩ; bnd[]; Vis₁; vh; vd; vs; vt; Bnd₁)
open import OCF.Align.Closure using (lt→<; lt→<ᴾ; <→lt; <ᵀ-trans; cmpᵀ-refl; eq→≡; eq→≡ᴾ) renaming (Pen to CPen)
open import OCF.Align.Bachmann using (gt→<; <ᵀ-irrefl; Hd≤)
open import OCF.Align.SystemOmega using (cmp-CΩ)
open import OCF.Align.Uniform4Label using (nfΩp; nf𝟏)
open import OCF.Align.Uniform4TwoWalk using (tΩ·2; ¬NF-Ω·2)
open import OCF.Align.Stage2 using () renaming (≺→⊑ to ≺→⊑²)
open import OCF.Align.Stage2Label using (Lab-oc)
open import OCF.Align.OmegaExpBase using (1<γ)
```

## §1 `NF₁` 对 $\theta\mapsto\psi_0(\Omega_{\Omega+\theta})$ 封闭

```agda
Ωs₊ : T → T
Ωs₊ c = Ωt (μ c)

_≤₁_ : T → T → Set
a ≤₁ c = (a <ᵗ c) ⊎ (a ≡ c)

≤₁-tr : ∀ {a b c} → a <ᵗ b → b ≤₁ c → a <ᵗ c
≤₁-tr p (inj₁ q) = <ᵀ-trans p q
≤₁-tr p (inj₂ refl) = p

bad : ∀ {x ys e c} → Ctbl e → Bnd₁ [] (ψᵗ (Ωp ∷ e) x ∷ ys) → (ψᵗ [] (ψᵗ (Ωp ∷ e) x ∷ ys) ∷ []) ≤₁ c → c ≤₁ e → ⊥
bad c[] b l (inj₁ ())
bad c[] b (inj₁ ()) (inj₂ refl)
bad c[] b (inj₂ ()) (inj₂ refl)
bad (c∷ ct) b l m = <ᵀ-irrefl (≤₁-tr (≤₁-tr (E.hd< (E.ar< (b (vs ([]≤ _) (vt (vh ([]≤ _))))))) l) m)

key : ∀ {a c} → NF₁ a → Bnd₁ [] a → (ψᵗ [] a ∷ []) ≤₁ c → a <ᵗ Ωs₊ c
key n[] b l = E.[]<
key {c = c} (n∷ {x = ψᵗ u x} (nψ nu (sC cu) na bx) nys hd) b l = E.hd< (E.lv< (lt→< u (μ c) (cmp-CΩ cu c)))
key {c = c} (n∷ {x = ψᵗ (_ ∷ e) x} {xs = ys} (nψ nu (sΩ ce) na bx) nys hd) b l with cmpᵀ e c in ec
... | lt = E.hd< (E.lv< (E.tl< (lt→< e c ec)))
... | eq = ⊥-elim (bad ce b l (inj₂ (sym (eq→≡ e c ec))))
... | gt = ⊥-elim (bad ce b l (inj₁ (gt→< e c ec)))

Hb : T → T → Set
Hb []       c = ⊤
Hb (x ∷ xs) c = (x ∷ []) ≤₁ c

Hb-tail : ∀ {x xs c} → (x ∷ []) ≤₁ c → Hd≤ xs x → Hb xs c
Hb-tail {xs = []} l h = tt
Hb-tail {x} {y ∷ ys} l (inj₁ e) = inj₁ (≤₁-tr (E.hd< (lt→<ᴾ y x e)) l)
Hb-tail {x} {y ∷ ys} l (inj₂ e) rewrite eq→≡ᴾ y x e = l

Hb-self : ∀ t → Hb t t
Hb-self [] = tt
Hb-self (x ∷ []) = inj₂ refl
Hb-self (x ∷ y ∷ ys) = inj₁ (E.tl< E.[]<)

visC : ∀ {c t ζ} → NF₁ t → Ctbl t → Hb t c → Vis₁ [] ζ t → ζ <ᵗ Ωs₊ c
visC (n∷ (nψ _ _ na bx) nxs h) (c∷ ct) hb (vh _) = key na bx hb
visC (n∷ (nψ _ _ na bx) nxs h) (c∷ ct) hb (vd _ v) = <ᵀ-trans (bx v) (key na bx hb)
visC (n∷ (nψ _ _ na bx) nxs h) (c∷ ct) hb (vs _ ())
visC (n∷ (nψ _ _ na bx) nxs h) (c∷ ct) hb (vt v) = visC nxs ct (Hb-tail hb h) v

bndΩ : ∀ {θ} → NF₁ θ → Ctbl θ → Bnd₁ [] (Ωs₊ θ)
bndΩ nθ cθ (vh _) = E.[]<
bndΩ nθ cθ (vd _ ())
bndΩ nθ cθ (vs _ (vh _)) = E.[]<
bndΩ nθ cθ (vs _ (vd _ ()))
bndΩ nθ cθ (vs _ (vs _ (vh _))) = E.[]<
bndΩ nθ cθ (vs _ (vs _ (vd _ ())))
bndΩ nθ cθ (vs _ (vs _ (vs _ ())))
bndΩ nθ cθ (vs _ (vs _ (vt ())))
bndΩ {θ} nθ cθ (vs _ (vt v)) = visC nθ cθ (Hb-self θ) v
bndΩ nθ cθ (vt ())

hdΩ : ∀ {θ} → Ctbl θ → Hd≤ θ Ωp
hdΩ c[] = tt
hdΩ (c∷ ct) = inj₁ refl

NF-Ω : ∀ {θ} → NF₁ θ → Ctbl θ → NF₁ (ψ₀ᵗ (Ωs₊ θ))
NF-Ω nθ cθ = n∷ (nψ n[] (sC c[]) (n∷ (nψ (n∷ nfΩp nθ (hdΩ cθ)) (sΩ cθ) n[] bnd[]) n[] tt) (bndΩ nθ cθ)) n[] tt
```

## §2 $\psi_0(\Omega_{\Omega+\theta})$

```agda
TΩ-label : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {α} → α ≅ᴵ toLevel Y hY → ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Lab₀ (ψ̄ (Ω̇ α) ev z) (ψ₀ᵗ (Ωs₊ θ))
TΩ-label Y hY lY nθ e = label (LdΩ̇ Y hY lY nθ e hon) (RΩ̇ (≅ᴵ-refl _)) (NF-Ω nθ (Lab→Ctbl lY nθ))
```

