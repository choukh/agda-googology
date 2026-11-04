# 主线直接标: 验收

> **验收文件, 不在证书的闭包内.** 记号与标签在这里出现. 结论写在 [OrdLab](OrdLab.lagda.md). 与 [LadderLabAccept](LadderLabAccept.lagda.md) 同形, 差别只有一处: 这里的 `I∞`, `I₂` 是**主线**的 `OCF.Align.LadderInfMain`, 不是克隆 `LadderLabZInfWMain`. 标签类 (`OrdLabClass`, `OrdLabRel`, `OrdLabPsi`, `OrdLabEval`, `OrdLabTop`) 贴在主线的 `LadderInfTree` 与主线的 `GᴺTᵠ` 上, 证书没有副本.
>
> §3 经 `agree₂`, `agree²`, `agree∞`, `agree-NF`, `anchor-ω` 搬到 `LadderOrd` 与 `LadderNF`, `LadderMono` 的树上. 这些全是主线的定理.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.List using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Force using (forceᴺ)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; Lab-≅)
import OCF.Align.EBO as E
open E using (T; natT; Ωt) renaming (_<ᵀ_ to _<ᵗ_)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; n[]; Ω₁; Ωᵐ; ψ¹)
open import OCF.Align.OrdLabZGoodLBase using (Lab→Ctbl; lab1; nf1)
open import OCF.Align.OrdLabZStage2Label using (one⁰)
open import OCF.Align.OrdLabZUniform3Base using (ψ₀ᵗ)
open import OCF.Align.OrdLabNFOmega using (NF-Ωᵐ)
open import OCF.Align.OrdLabNFTop using (NF-ψ)
open import OCF.Align.LadderInfTop using (HS∞; fin; ∞)
open import OCF.Align.LadderInfTop2 using (HS₂; top) renaming (fin to fin₂)
open import OCF.Align.OrdLabInst using (Px∞; Px₂)
import OCF.Align.OrdLabTop
import OCF.Align.LadderInfMain
import OCF.Align.LadderOrdMain
import OCF.Align.LadderNFMain as NM
import OCF.Align.LadderMonoMain as MM
open import OCF.Align.LadderOrdPos using (HB; end; low; blk)
open import OCF.Align.LadderOrdCode using (ωᶜ; ω²ᶜ)
open import OCF.Align.LadderOrdInst using (M₂; e₂; e²; e∞)
open import OCF.Align.LadderOrdAgree using (agree₂; agree²; agree∞; agree-NF; anchor-ω)
module L∞ = OCF.Align.OrdLabTop HS∞ Px∞
module L₂ = OCF.Align.OrdLabTop HS₂ Px₂
module I∞ = OCF.Align.LadderInfMain HS∞
module I₂ = OCF.Align.LadderInfMain HS₂
module G₂ = OCF.Align.LadderOrdMain (HB M₂)
module G² = OCF.Align.LadderOrdMain (HB ω²ᶜ)
module Gω = OCF.Align.LadderOrdMain (HB ωᶜ)
```

## §1 主线的 `HS∞`

```agda
B∞ : T
B∞ = ψ₀ᵗ (Ωt (ψ¹ ∷ Ω₁ ∷ []))

label-∞ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ B∞ → ∀ {α} → α ≅ᴵ toLevel Y hY →
          ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I∞.GᴺTᵠ ∞ α ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ θ)))
label-∞ Y hY lY nθ pm e ev p = L∞.label-cert ∞ Y hY lY nθ (NF-ψ 0 nθ (Lab→Ctbl lY nθ) pm) e ev p

1<B∞ : natT 1 <ᵗ B∞
1<B∞ = E.hd< (E.ar< E.[]<)

label-∞1 : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I∞.GᴺTᵠ ∞ (suc zero) ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ natT 1)))
label-∞1 = label-∞ one⁰ (hs hz) lab1 nf1 1<B∞ (s≅ z≅)

label-∞0 : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I∞.GᴺTᵠ ∞ zero ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ [])))
label-∞0 = label-∞ Ord₊.zero hz (l0 refl z≅) n[] E.[]< z≅

label-fin : ∀ m {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ ψ₀ᵗ (Ωt (Ω₁ ∷ Ω₁ ∷ Ωᵐ m [])) → ∀ {α} → α ≅ᴵ toLevel Y hY →
            ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I∞.GᴺTᵠ (fin m) α ev p)) (ψ₀ᵗ (Ωt (Ω₁ ∷ Ωᵐ m θ)))
label-fin m Y hY lY nθ pm e ev p = L∞.label-cert (fin m) Y hY lY nθ (NF-Ωᵐ m nθ (Lab→Ctbl lY nθ) pm) e ev p
```

## §2 主线的 `HS₂`

```agda
label-top : ∀ n {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ ψ₀ᵗ (Ωt (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) → ∀ {α} → α ≅ᴵ toLevel Y hY →
            ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I₂.GᴺTᵠ (top n) α ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ Ωᵐ n θ)))
label-top n Y hY lY nθ pm e ev p = L₂.label-cert (top n) Y hY lY nθ (NF-ψ n nθ (Lab→Ctbl lY nθ) pm) e ev p

label-fin₂ : ∀ m {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ ψ₀ᵗ (Ωt (Ω₁ ∷ Ω₁ ∷ Ωᵐ m [])) → ∀ {α} → α ≅ᴵ toLevel Y hY →
             ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I₂.GᴺTᵠ (fin₂ m) α ev p)) (ψ₀ᵗ (Ωt (Ω₁ ∷ Ωᵐ m θ)))
label-fin₂ m Y hY lY nθ pm e ev p = L₂.label-cert (fin₂ m) Y hY lY nθ (NF-Ωᵐ m nθ (Lab→Ctbl lY nθ) pm) e ev p

label-ψ₁+Ω·n : ∀ n {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I₂.GᴺTᵠ (top n) zero ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ Ωᵐ n [])))
label-ψ₁+Ω·n n = label-top n Ord₊.zero hz (l0 refl z≅) n[] E.[]< z≅

label-ψ₁+Ω : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I₂.GᴺTᵠ (top 1) zero ev p)) B∞
label-ψ₁+Ω = label-ψ₁+Ω·n 1

label-ψ₁+Ω+1 : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (I₂.GᴺTᵠ (top 1) (suc zero) ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ Ω₁ ∷ natT 1)))
label-ψ₁+Ω+1 = label-top 1 one⁰ (hs hz) lab1 nf1 (E.hd< (E.ar< E.[]<)) (s≅ z≅)
```

## §3 搬到 `LadderOrd`, `LadderNF`, `LadderMono`

`e₂ (top n)` 是码 `M₂ = ω·ᶜ 1` 里值 $\omega+n$ 的位置, `e² (top n)` 是码 `ω²ᶜ` 里同样值的位置. 所以这些是高度为序数码位置的树上的标签, 没有克隆: `agree₂`, `agree²`, `agree∞` 都是主线的定理.

```agda
ord-top₂ : ∀ n {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ ψ₀ᵗ (Ωt (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) → ∀ {α} → α ≅ᴵ toLevel Y hY →
           ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (G₂.GᴺTᵠ (e₂ (top n)) α ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ Ωᵐ n θ)))
ord-top₂ n Y hY lY nθ pm {α} e ev p = Lab-≅ (≅-sym (agree₂ (top n) α ev p)) (label-top n Y hY lY nθ pm e ev p)

ord-top² : ∀ n {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ ψ₀ᵗ (Ωt (ψ¹ ∷ Ω₁ ∷ Ωᵐ n [])) → ∀ {α} → α ≅ᴵ toLevel Y hY →
           ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (G².GᴺTᵠ (e² (top n)) α ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ Ωᵐ n θ)))
ord-top² n Y hY lY nθ pm {α} e ev p = Lab-≅ (≅-sym (agree² (top n) α ev p)) (label-top n Y hY lY nθ pm e ev p)

ord-fin₂ : ∀ m {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ ψ₀ᵗ (Ωt (Ω₁ ∷ Ω₁ ∷ Ωᵐ m [])) → ∀ {α} → α ≅ᴵ toLevel Y hY →
           ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (G₂.GᴺTᵠ (e₂ (fin₂ m)) α ev p)) (ψ₀ᵗ (Ωt (Ω₁ ∷ Ωᵐ m θ)))
ord-fin₂ m Y hY lY nθ pm {α} e ev p = Lab-≅ (≅-sym (agree₂ (fin₂ m) α ev p)) (label-fin₂ m Y hY lY nθ pm e ev p)

-- 码 ωᶜ 的顶: 值 ω, 第 α 行
ord-∞ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ B∞ → ∀ {α} → α ≅ᴵ toLevel Y hY →
        ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (Gω.GᴺTᵠ end α ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ θ)))
ord-∞ Y hY lY nθ pm {α} e ev p = Lab-≅ (≅-sym (agree∞ ∞ α ev p)) (label-∞ Y hY lY nθ pm e ev p)

ord-fin∞ : ∀ m {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ ψ₀ᵗ (Ωt (Ω₁ ∷ Ω₁ ∷ Ωᵐ m [])) → ∀ {α} → α ≅ᴵ toLevel Y hY →
           ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (Gω.GᴺTᵠ (e∞ (fin m)) α ev p)) (ψ₀ᵗ (Ωt (Ω₁ ∷ Ωᵐ m θ)))
ord-fin∞ m Y hY lY nθ pm {α} e ev p = Lab-≅ (≅-sym (agree∞ (fin m) α ev p)) (label-fin m Y hY lY nθ pm e ev p)

-- 主线 LadderNF 的树
nf-main : ∀ m {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ ψ₀ᵗ (Ωt (Ω₁ ∷ Ω₁ ∷ Ωᵐ m [])) → ∀ {α} → α ≅ᴵ toLevel Y hY →
          ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (NM.GᴺTᵠ m α ev p)) (ψ₀ᵗ (Ωt (Ω₁ ∷ Ωᵐ m θ)))
nf-main m Y hY lY nθ pm {α} e ev p = Lab-≅ (agree-NF m α ev p) (ord-fin∞ m Y hY lY nθ pm e ev p)

-- 主线 LadderMono 的树 Tω
mono-main : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (MM.GᴺTω ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ [])))
mono-main ev p = Lab-≅ (anchor-ω ev p) (ord-∞ Ord₊.zero hz (l0 refl z≅) n[] E.[]< z≅ ev p)
```
