# 链从 0 起 (二): 闭项

> 不含记号. 入口 [ChainZ](ChainZ.lagda.md). 与 [HtTowerFClosed](HtTowerFClosed.lagda.md) 同一个包装 (`At`), 折叠换成 [ChainZFold](ChainZFold.lagda.md). 高度 (`Ω₂ᴴ`, `mul`, `Ω₂ω`, `Ω₂²`), `ω⋅`, `ord` 全部从 `HtTowerFClosed` 导入. 合法性仍由形状给出 (`Lg-sum` 一次调用), 与折叠里链怎么走无关; 这一点本身是 `DiagKTop.Lg-blind` 那一类事实, 所以 "仍合法" 不说明链从 0 起的折叠好不好, 只说明它是一个合格的候选.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ChainZClosed where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Align.CumReadCF using (A; azero; Lg; z⊲)
import OCF.Free.Level as FL
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree
open import OCF.Align.HtTowerFClosed using (ω⋅; one; W₁; top⁺; Ω₂ᴴ; lΩ₂; mul; Lg-mul; Ω₂ω; Lg-Ω₂ω; Ω₂²; Lg-Ω₂²; ord)
open import OCF.Align.HtTowerFRead using (D₁; rd; Lg-rd)
import OCF.Align.ChainZFold as Fold

-- 种子: 只看状态里第 1 层的输出 z₁, 不看界
Seed : Set
Seed = Σ (∀ {W} → LgW₂ W → D₁ W → H₀) (λ sd → ∀ {W} (lW : LgW₂ W) t → LgB (sd lW t))

bot₀ : Seed                       -- 审查 D2 的原文: x₀ = bot
bot₀ = (λ _ _ → hz) , (λ _ _ → tt)

out₀ : Seed                       -- 种子取输出: x₀ = rd(hz, z₁)
out₀ = (λ lW t → rd lW hz t) , (λ lW t → Lg-rd lW hz t tt)

module At (σ : Seed) (Λ : Ht) (lΛ : LgB Λ) (o : ∀ {w} → hs hz ⊲[ w ] Λ) where
  open Fold ω⋅ Λ lΛ o (proj₁ σ) (proj₂ σ)
  open import OCF.Align.HtTowerFFold ω⋅ Λ lΛ o using (Ig; St; st; zeroD; Stp; Df; yc; τ₀)

  Act : ∀ {ly W} → Ig ly W
  Act p lW′ _ Y = Stp Y

  Y₀ : ∀ {W} → St W
  Y₀ = st zeroD n0 n0

  ΔΩ : Df W₁
  ΔΩ = Run accᴸ (Ωd Λ {azero , hz}) (z⊲ one , hself) (tt , tt) hself Act n0 Y₀

  ΨΩ : D₀ W₁
  ΨΩ = n1 ⨾ yc ΔΩ (τ₀ (tt , tt))

  Tψ : A
  Tψ = sum azero ΨΩ

  Lg-Tψ : Lg Tψ
  Lg-Tψ = Lg-sum azero ΨΩ tt

module Inst (σ : Seed) where
  TΛ : ∀ Λ → LgB Λ → (∀ {w} → hs hz ⊲[ w ] Λ) → A
  TΛ Λ lΛ o = At.Tψ σ Λ lΛ o

  Lg-TΛ : ∀ Λ (lΛ : LgB Λ) (o : ∀ {w} → hs hz ⊲[ w ] Λ) → Lg (TΛ Λ lΛ o)
  Lg-TΛ Λ lΛ o = At.Lg-Tψ σ Λ lΛ o

  T⁺ : ∀ h → LgB h → A
  T⁺ h lh = TΛ (top⁺ h) (Lg-⊞ (hs hz) h tt lh) (⊞-fst (hs hz) h)

  Lg-T⁺ : ∀ h (lh : LgB h) → Lg (T⁺ h lh)
  Lg-T⁺ h lh = Lg-TΛ (top⁺ h) (Lg-⊞ (hs hz) h tt lh) (⊞-fst (hs hz) h)

open Inst using (T⁺; Lg-T⁺)
```

**闭项.** 与 `HtTowerFClosed` 同样的高度. 都用到新种类 `κH`, 所以都经过改过的 `RunM`. `Z-…` 用种子 `bot₀`, `Zs-…` 用种子 `out₀`.

```agda
Z-Ω₂ Z-Ω₂+1 Z-Ω₂·2 Z-Ω₂ω Z-Ω₂² : A
Z-Ω₂ = T⁺ bot₀ Ω₂ᴴ lΩ₂
Z-Ω₂+1 = T⁺ bot₀ (hs Ω₂ᴴ) lΩ₂
Z-Ω₂·2 = T⁺ bot₀ (mul 2) (Lg-mul 2)
Z-Ω₂ω = T⁺ bot₀ Ω₂ω Lg-Ω₂ω
Z-Ω₂² = T⁺ bot₀ Ω₂² Lg-Ω₂²

Zs-Ω₂ Zs-Ω₂+1 Zs-Ω₂·2 Zs-Ω₂ω Zs-Ω₂² : A
Zs-Ω₂ = T⁺ out₀ Ω₂ᴴ lΩ₂
Zs-Ω₂+1 = T⁺ out₀ (hs Ω₂ᴴ) lΩ₂
Zs-Ω₂·2 = T⁺ out₀ (mul 2) (Lg-mul 2)
Zs-Ω₂ω = T⁺ out₀ Ω₂ω Lg-Ω₂ω
Zs-Ω₂² = T⁺ out₀ Ω₂² Lg-Ω₂²

Lg-Z-Ω₂² : Lg Z-Ω₂²
Lg-Z-Ω₂² = Lg-T⁺ bot₀ Ω₂² Lg-Ω₂²

Lg-Zs-Ω₂² : Lg Zs-Ω₂²
Lg-Zs-Ω₂² = Lg-T⁺ out₀ Ω₂² Lg-Ω₂²

fgh : ℕ → ℕ
fgh = FL.FGH (ord Zs-Ω₂²)
```
