> **机械克隆, 验收用.** 由 `LadderNFMain` 经脚本复制, 只改导入, 把证书搬到标签阶梯的世界. 见 [LadderNFAccept](LadderNFAccept.lagda.md).

# 阶梯去记号 (二十五): 闭包定理

> 结论写在 [LadderNF](LadderNF.lagda.md). **`GᴺTᵠ m α`: `Goodᴺ (toZ (Tᵠ m α ev z))`, 对一切 $m$, $\alpha$.** 证书的导入闭包不含记号 (`probes/Survey/scripts/importclosure.py`). `GᴺTω-if`: $T_\omega$ 只差跨高度的单调.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderNFWMain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Align.Level
open import OCF.Align.LadderNFWPrefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ)
open import OCF.Align.LadderNFWEq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; toZ-≅)
open import OCF.Align.LadderNFWFloor using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; inb; Dem; _∼ᶠ_; ∼ᶠ-refl; flo; cvFlo; toFlo)
open import OCF.Align.LadderNFWForce using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Align.LadderNFWFT using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderNFWTree
open import OCF.Align.LadderNFWRel
open import OCF.Align.LadderNFWCx
open import OCF.Align.LadderNFWRules
open import OCF.Align.LadderNFWRules2
open import OCF.Align.LadderNFWRules3
open import OCF.Align.LadderNFWStrict
open import OCF.Align.LadderNFWStrict2
open import OCF.Align.LadderNFWClass
open import OCF.Align.LadderNFWClassF using (inp-map)
open import OCF.Align.LadderNFWGood
open import OCF.Align.LadderNFWVis
open import OCF.Align.LadderNFWIota
open import OCF.Align.LadderNFWAdd
open import OCF.Align.LadderNFWTr
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.LadderNFWForce using (forceᴺ-≅; Goodᴺ-tr)
open import OCF.Align.LadderNFWEq using (s-invˢ; l-invˢ; i-respˢ; u-reflˢ; tf; ŝ≅; ĉ≅; upˡ; upʳ)
open import OCF.Align.LadderNFWClassF

open import OCF.Align.LadderNFWTail
open import OCF.Align.LadderNFWRead
open import OCF.Align.LadderNFWAux using (one⁰)
open import OCF.Align.LadderNFWEq using (≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; Ωˢ-≅; Ωˢ-refl)
open import OCF.Align.LadderNFWFloor using (⊔∼; fk∼)
open import OCF.Align.LadderNFWClassF using (NZ-of)

open import OCF.Align.LadderNFWForce using (gl)
open import OCF.Align.LadderNFWEval using (module EvalM)

open import OCF.Align.LadderNFWOmega
open EvalM Ω̇G public using (T̄)
```

## §1 一切 $m$, $\alpha$

```agda
Gᴺof : ∀ {m c φ χ ℓ w} {ok : Ok w} {e : Eh zero m w χ} {x : Q m c φ χ} → Gq g₀ m c 𝓥 x → (ev : Ev ℓ φ) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ᵠ ok e x ev z))
Gᴺof {ok = ok} {e = e} g ev z = Good→N refl (T̄ {ok = ok} {e = e} {ev = ev} {p = z} {𝓖 = 𝓥} {𝓖′ = isId} (λ { refl → tt }) (λ c → c) refl g)

GᴺTᵠ : ∀ m α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Tᵠ m α ev z))
GᴺTᵠ m α = Gᴺof (Ω̇G g₀ m α)
```

## §2 实例

$\psi_0(\Omega_{\Omega\cdot(m+1)+\alpha})$ 这个读法是验收的结论 ([LadderNFAccept](LadderNFAccept.lagda.md)). 这里只说证书存在.

```agda
ev₀ : Ev (suc zero) Fl
ev₀ = tt , (λ q → q)

-- ψ₀(Ω_Ω): 根层
GᴺTΩ : Goodᴺ (toZ (Tᵠ 0 zero ev₀ zero))
GᴺTΩ = GᴺTᵠ 0 zero ev₀ zero

-- 决定性锚点 ψ₀(Ω_{Ω·2})
GᴺTΩ·2 : Goodᴺ (toZ (Tᵠ 1 zero ev₀ zero))
GᴺTΩ·2 = GᴺTᵠ 1 zero ev₀ zero

-- ψ₀(Ω_{Ω·2+1})
GᴺTΩ·2+1 : Goodᴺ (toZ (Tᵠ 1 (suc zero) ev₀ zero))
GᴺTΩ·2+1 = GᴺTᵠ 1 (suc zero) ev₀ zero

-- ψ₀(Ω_{Ω·3})
GᴺTΩ·3 : Goodᴺ (toZ (Tᵠ 2 zero ev₀ zero))
GᴺTΩ·3 = GᴺTᵠ 2 zero ev₀ zero

-- ψ₀(Ω_{Ω·(m+1)+α}), 一切 m, α
GᴺT : ∀ m α → Goodᴺ (toZ (Tᵠ m α ev₀ zero))
GᴺT m α = GᴺTᵠ m α ev₀ zero
```

## §3 $\psi_0(\Omega_{\Omega\cdot\omega})$ 的逐项证书

```agda
GᴺTωn : ∀ n {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Tωn n ev z))
GᴺTωn zero ev z = Gᴺof {m = 0} {c = zero} {χ = κ Fl} (gs 𝓥 (λ c → c) g0 (λ _ f _ → cxoᵀ f) (λ x o _ → x) (λ _ _ → (λ { (inr ink) → inj₂ z≅ }) , (λ i ())) (λ c → Hq-zero _)) ev z
GᴺTωn (suc n) = GᴺTᵠ n zero

-- 条件: 跨高度的单调是唯一缺的东西
GᴺTω-if : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → (∀ n → forceᴺ _ (GᴺTωn n ev z) ⊑ forceᴺ _ (GᴺTωn (suc n) ev z)) → Goodᴺ (toZ (Tω ev z))
GᴺTω-if ev z st = gl (λ n → GᴺTωn n ev z) st
```
