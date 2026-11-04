# 主线直接标: 链行的展开 (对一切 `HtB`)

> **判决: HOLDS (编译过, 对结构参数, 不读记号).** 结论写在 [OrdLab](OrdLab.lagda.md). 对 `HtB` 的高度 $m$, 若 `view m` 是 `chain F qs`, 则第 0 行的计值 $\cong$ `lim h`, 其中 `h 0` 就是树 $\omega$ (`ωZ` 的计值, 与 $F$ 和 $m$ 都无关), `h (suc i)` $\cong$ 高度 `F i` 的第 0 行的计值. 这是字面定义 (`rowL`) 的定理形式, 用 `D-self` 把 `ι↓` 去掉.
>
> 这条不读记号, 导入闭包在主线内.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.OrdLabChain (𝕊 : HtB) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ; Ord₊ˢ; Ωˢ; _+ˢ_)
open import OCF.Free.Eq using (_≈ᴿ_; _≅ˢ_; ≅ˢ-sym; toZ-≅)
open import OCF.Free.Floor using (Ev; Run; fz; wk; sucRun; ∅ᴿ)
open import OCF.Free.Force using (Goodᴺ; gl; forceᴺ; forceᴺ-≅)
open import OCF.Free.Tree using (Fl)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdMain 𝕊 using (GᴺTᵠ)
open import OCF.Align.LadderOrdDn 𝕊 using (D→≈ᵠ)
open import OCF.Align.LadderOrdDnSelf 𝕊 using (D-self)
```

## §1 `Goodᴺ` 在极限上的反演

```agda
goodLim : ∀ {x} {f : ℕ → Z} → x ≡ Z.lim f → (G : Goodᴺ x) → Σ (∀ n → Goodᴺ (f n)) λ Gs → (forceᴺ x G ≅ lim (λ n → forceᴺ (f n) (Gs n))) × (∀ n → forceᴺ (f n) (Gs n) ⊑⁰ forceᴺ (f (suc n)) (Gs (suc n)))
goodLim refl (gl G st) = G , ≅-refl⁰ _ , st
```

## §2 第 0 项

`ωZ`: 链行第 0 项 `𝟏L` 的计值, 字面就是 $\omega$ 的展开. 不依赖高度与环境.

```agda
ωZ : Z
ωZ = toZ (Ord₊ˢ.lim (iter (Ωˢ zero +ˢ_) Ord₊ˢ.zero))
```

## §3 后面的项

```agda
e₀ : ∀ {m} → Eh h₀ m w₀ (κ Fl)
e₀ {m} i h r = ok₀ i

e-stp : ∀ {n m} → Eh h₀ m w₀ (cap (κ Fl) n fz)
e-stp {n} j h r = κ-cap n (λ _ → tt) j (ok₀ j)

stepR : ∀ {n m} (q : n <ᴸ m) → Tᵠ n zero ≈ᴿ ψ̄ᵠ ok₀ e₀ (stepL q (ΩI m q))
stepR {n} {m} q = subst (λ X → Tᵠ n zero ≈ᴿ ψ̄ᵠ ok₀ e₀ (stepL q X)) (sym (ΩI≡ q)) (D→≈ᵠ (D-self q) ok₀ e₀ ok₀ e-stp)
```

## §4 展开

```agda
Ω̇-chain : ∀ {m F qf} → view m ≡ chain F qf → Ω̇ m zero ≡ ql (rowL F qf (λ i → ΩI m (qf i)))
Ω̇-chain {m} e = cong (rowV m (ΩI m)) e

record ChainRow (X : Ordᶜ zero) (Y : ℕ → Ordᶜ zero) : Set where
  constructor mkCR
  field
    h     : ℕ → Ordᶜ zero
    eq    : X ≅ lim h
    G₀    : Goodᴺ ωZ
    first : h 0 ≡ forceᴺ ωZ G₀
    rest  : ∀ i → h (suc i) ≅ Y i
    step  : ∀ n → h n ⊑⁰ h (suc n)

chain-row : ∀ {m F qf} → view m ≡ chain F qf → ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) →
            ChainRow (forceᴺ _ (GᴺTᵠ m zero ev z)) (λ i → forceᴺ _ (GᴺTᵠ (F i) zero ev z))
chain-row {m} {F} {qf} c ev z = mkCR (λ n → forceᴺ _ (proj₁ J n)) (proj₁ (proj₂ J)) (proj₁ J 0) refl stp (proj₂ (proj₂ J))
  where
  f : ℕ → Z
  f n = toZ (ψ̄ᵠ ok₀ e₀ (rowL F qf (λ i → ΩI m (qf i)) n) ev z)
  x≡ : toZ (Tᵠ m zero ev z) ≡ Z.lim f
  x≡ = cong (λ w → toZ (ψ̄ᵠ ok₀ e₀ w ev z)) (Ω̇-chain c)
  J = goodLim x≡ (GᴺTᵠ m zero ev z)
  stp : ∀ i → forceᴺ (f (suc i)) (proj₁ J (suc i)) ≅ forceᴺ _ (GᴺTᵠ (F i) zero ev z)
  stp i = forceᴺ-≅ (toZ-≅ (≅ˢ-sym (stepR (qf i) ev z ev z (≅ᴵ-refl _)))) _ _
```
