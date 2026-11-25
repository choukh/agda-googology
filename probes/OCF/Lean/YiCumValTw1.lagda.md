# 累加的读回: 塔第 1 项闭项的值 (回归)

> 验收文件. 编译定理, 无前提: `bho-tw1ᶜ : ψ⁰(Ω₂) ≼ read (ctwᶜ 1)`, 累加的塔第 1 项闭项不低于 ψ₀(Ω₂) (只有下界), 即 `YiLimVal.bho-tw1` 的对应物.
> 证法与旧塔不同: 链点 1 读成的层号的孩子 1 是层号 3 (`YiCumCheck.pt1-child`), 那里的底由路径搬入 (不经回退行); 层号 3 的 Ω 树经 `ins` 行下到层号 2, 再用层号 2 上的 `YiLimVal.At.lower2`.
> 不否定什么. 不涉及上界, 不涉及 ω+1 分量 (ψ₀(Ω_{ω+1})).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCumValTw1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock renaming (L to LF)
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃s; ◃l; ◃w; ◃t; Ωt-nz)
open import OCF.Lean.YiFreshValRead using (read; limcum≽; next≼)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiUpBlock
open import OCF.Lean.YiUpCheck using (one; two; d₁)
open import OCF.Lean.YiUpVal using (_⊢_⊴_; ⊴r; ⊴◃; ⊴-◃; ⊴-trans; ⊴→≼; Up-⊵; S; S-w; s-⊴; Sβ₀; 𝟏; I2)
open import OCF.Lean.YiLimBlock
open import OCF.Lean.YiLimFold
open import OCF.Lean.YiLimLegal using (mono⊥; dS; dL)
open import OCF.Lean.YiLimVal using (module At; s0-⊵; ⊥1-⊵)
open import OCF.Lean.YiCumBlock
open import OCF.Lean.YiCumLegal using (ctwᶜ)
open import OCF.Lean.YiCumCheck using (three; hᶜ; εhᶜ; ρhᶜ; Gᶜ; ptᶜ; pt1; g₁ᶜ)

import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼l; ≼-trans)
```

## 链点 1, 孩子 1 (层号 3) 的底

`Bc3`: 前缀 `up zero 0 (Ωt 1)` 给孩子 1 的底. `B′`: 层号 3 的 Ω 树下到层号 2 时 (`ins` 行) 的底. 两个分量都是沿路径 `ins (ins self)` 搬进孩子 1 后再折的: 第 1 层分量是一个结点, 第一分支是 `next (Ωt 1)` (`β₁-form`).

```agda
Bc3 : Base three
Bc3 = dL g₁ᶜ (εhᶜ pt1) (ρhᶜ pt1) (B₀ (LF.lim g₁ᶜ)) 1 (up zero 0 (Ωt one))

B′ : Base two
B′ = dS two tt tt Bc3 zero

β₁ : Tr one
β₁ = bs B′ one (ins self)

β₁-form : β₁ ≡ Ω (inj₁ tt) (λ z → next (Up zero d₁ (Ωt one) z))
β₁-form = refl

β₂ : Tr two
β₂ = bs Bc3 two (ins self)

β₂-form : β₂ ≡ Up one (down stop tt) (Ωt two) (Ωt one)
β₂-form = refl
```

`At.lower2 B′` 的四条前提.

```agda
Ωt1◃β₁ : one ⊢ Ωt one ◃ β₁
Ωt1◃β₁ = ◃t {y = next (Ωt one)} (◃l zero) ◃w

hβ : S (L.Ω (L.suc L.zero)) β₁
hβ = S-w Sβ₀ Ωt1◃β₁

zβ : one ⊢ zero ◃ β₁
zβ = ◃t (Ωt-nz one) Ωt1◃β₁

H1-⊵ : (B : Base one) (b : Tr zero) (t : Tr one) → zero ⊢ b ⊴ ψs one tt tt B zero (ins self) b t
H1-⊵ B b zero       = ⊴r
H1-⊵ B b (suc t)    = ⊴◃ (⊴-◃ (H1-⊵ B b t) (◃l zero))
H1-⊵ B b (lim f)    = ⊴◃ (⊴-◃ (H1-⊵ B b (f zero)) (◃l zero))
H1-⊵ B b (Ω (inj₁ tt) g) = ⊴◃ (⊴-◃ (H1-⊵ B b (g zero)) (◃l zero))
H1-⊵ B b (Ω (inj₂ ()) g)
H1-⊵ B b (up t _ c) = ⊴-trans (H1-⊵ B b t) (s0-⊵ (dS zero tt tt B t) (ψs one tt tt B zero (ins self) b t) c)

h0 : zero ⊢ suc zero ⊴ bs B′ zero (ins (ins self))
h0 = H1-⊵ _ (suc zero) (Ωt one)

h⊥ : 𝟏 ≼ read (b⊥ B′)
h⊥ = ⊴→≼ (⊥1-⊵ (dL g₁ᶜ (εhᶜ pt1) (ρhᶜ pt1) (B₀ (LF.lim g₁ᶜ)) 0 zero) (Ωt one))
```

## 层号 3 下到层号 2

`form3` 与 `At.form` 同形: 层号 3 的 Ω 树的折叠是层号 2 上链的部分和. 链的第 1 项是 `next β₂`, 高于 `Ωt 2` (`Up-⊵`).

```agda
F₂ : Tr two → Tr two
F₂ c = ψs two tt tt B′ two self β₂ c

zc : ℕ → Tr two
zc = iter (λ c → next (F₂ c)) zero

form3 : ψ⊥ three tt tt Bc3 (Ωt three) ≡ lim (cum (λ k → next (ψ⊥ two tt tt B′ (zc k))))
form3 = refl

Ωt2◃z1 : two ⊢ Ωt two ◃ zc 1
Ωt2◃z1 = ⊴-◃ (Up-⊵ one (down stop tt) (Ωt two) (Ωt one)) (◃l zero)

low3 : L.ψ⁰ (L.Ω I2) ≼ read (ψ⊥ three tt tt Bc3 (Ωt three))
low3 = limcum≽ (λ k → next (ψ⊥ two tt tt B′ (zc k))) 1
  (next≼ (ψ⊥ two tt tt B′ (zc 1))
    (≼-trans (At.lower2 B′ hβ zβ h0 h⊥) (⊴→≼ (⊴◃ (mono⊥ two tt tt B′ Ωt2◃z1)))))
```

## 塔第 1 项

```agda
low-pt1 : L.ψ⁰ (L.Ω I2) ≼ read (Gᶜ (ptᶜ 1))
low-pt1 = ≼l 1 low3

bho-tw1ᶜ : L.ψ⁰ (L.Ω I2) ≼ read (ctwᶜ 1)
bho-tw1ᶜ = limcum≽ (λ k → Gᶜ (ptᶜ k)) 1 low-pt1
```
