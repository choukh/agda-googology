# 统一形 (五): 标准形的边界与裁决的证据

> 接 [Uniform5Top](Uniform5Top.lagda.md), [Uniform5Wall](Uniform5Wall.lagda.md). 结论先说:
>
> 1. **`NF₁` 的可数部分都在 $\psi_0(\Omega_{\Omega\cdot2})$ 之下 (`nf-below`).** 所以 `TΩ-label` 的 "一切带标签的 $\eta$" 正好是 $\psi_0(\Omega_{\Omega\cdot2})$ 以下的全部可数下标; `Idx` 不含 $\psi_0(\Omega_{\Omega\cdot2})$ 本身 (`no-Idx`). 这不是损失: $\theta=\psi_0(\Omega_{\Omega\cdot2})$ 时 $\psi_0(\Omega_{\Omega+\theta})$ 在任何标准形里都不合法, 因为 $\Omega_{\Omega\cdot2}$ 经 `vs` 对它可见而不小于它.
> 2. **与 Uniform4 一致 (`agree-Ω+1`).** 同一个标签, 两棵树 $\cong$.
> 3. **没有 `NF` 的语法序不能作分层 (`¬Acc-T`).** $\Omega>\psi_0(\Omega)>\psi_0(\psi_0(\Omega))>\cdots$ 是 `_<ᵀ_` 的无穷降链. 这是 `Syn` 路线的边界: 层号语法一旦含 $\psi_1(\cdot)$, 按 $<$ 递归定义 `Q σ` 就必须把标准形与 `Acc` 带进树的定义.
>
> **裁决 (证据在 [Uniform5Assess](Uniform5Assess.lagda.md)).**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform5NF where

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
open import OCF.Align.Stage2 using (Ωᵗ; Lab-uniq)
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
open import OCF.Align.Uniform5Label
open import OCF.Align.Uniform5Top
import OCF.Align.Uniform4Label as U4
```

## §1 `NF₁` 的边界

```agda
Ω·2<Ω·2 : ∀ {u} → Sb u → u <ᵗ (Ωp ∷ Ωp ∷ [])
Ω·2<Ω·2 {u} (sC cu) = lt→< u _ (cmp-CΩ cu (Ωp ∷ []))
Ω·2<Ω·2 (sΩ {c} cc) = E.tl< (lt→< c _ (cmp-CΩ cc []))

nf-below : ∀ {θ} → NF₁ θ → Ctbl θ → θ <ᵗ tΩ·2
nf-below n[] c[] = E.[]<
nf-below (n∷ (nψ _ _ n[] _) _ _) (c∷ _) = E.hd< (E.ar< E.[]<)
nf-below (n∷ (nψ _ _ (n∷ (nψ _ su _ _) _ _) _) _ _) (c∷ _) = E.hd< (E.ar< (E.hd< (E.lv< (Ω·2<Ω·2 su))))

no-Idx : Idx tΩ·2 → ⊥
no-Idx (_ , _ , _ , n) = ¬NF-Ω·2 n
```

## §2 与 Uniform4 对照

$\psi_0(\Omega_{\Omega+1})$: Uniform4 的层号是 ℕ, 这里是 `Ordᴵ`. 两棵树字面不同, 计值后 $\cong$.

```agda
agree-Ω+1 : ∀ {ℓ ℓ′} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) (ev′ : Ev ℓ′ Fl) (z′ : zero <ᴵ ℓ′) →
            forceᴸ _ (proj₁ (TΩ-label one⁰ (hs hz) lab1 nf1 (s≅ z≅) ev z)) ≅ forceᴸ _ (proj₁ (U4.TΩ-label 1 ev′ z′))
agree-Ω+1 ev z ev′ z′ = Lab-uniq (proj₂ (TΩ-label one⁰ (hs hz) lab1 nf1 (s≅ z≅) ev z)) (proj₂ (U4.TΩ-label 1 ev′ z′))
```

## §3 语法序不良基

```agda
data Acc⁺ (a : T) : Set where
  acc : (∀ {b} → b <ᵗ a → Acc⁺ b) → Acc⁺ a

dch : ℕ → T
dch zero    = Ωᵗ
dch (suc n) = ψ₀ᵗ (dch n)

dch↓ : ∀ n → dch (suc n) <ᵗ dch n
dch↓ zero    = E.hd< (E.lv< E.[]<)
dch↓ (suc n) = E.hd< (E.ar< (dch↓ n))

no-acc : ∀ n → Acc⁺ (dch n) → ⊥
no-acc n (acc h) = no-acc (suc n) (h (dch↓ n))

¬Acc-T : Acc⁺ Ωᵗ → ⊥
¬Acc-T = no-acc 0
```
