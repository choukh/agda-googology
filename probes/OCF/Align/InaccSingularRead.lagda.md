# 奇异下标的定时检验: 分支下标要读什么 (验收)

> **验收节.** 结论在 [InaccSingular](InaccSingular.lagda.md). 全部是 `cmpᵀ` 上的计算, 不提树. 三组例子说明: 目标 `limᴼ k g` 的分支 `x` 要从 `j` 读的, 依次是 `j` 的下标、`j` 相对目标的尾项、`j` 被 ψ 折叠掉的参数. 没有一个是 `j` 的整棵树 (`toT`), 也没有一个是自然数 (`nat-fails`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccSingularRead where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import OCF.Align.EBO as E
open E using (T; cmpᵀ; fsT; fsn; γT; cof; cΩ; cω; Ωt; sucT; 𝟏; lt; eq; gt) renaming (ψ to ψᵗ; natT to natᵗ)

Ωn : ℕ → T
Ωn n = Ωt (natᵗ n)

ω Ω₁ OO OO·2 : T
ω    = ψᵗ [] (𝟏 ∷ []) ∷ []
Ω₁   = Ωn 1
OO   = Ωt Ω₁
OO·2 = ψᵗ Ω₁ [] ∷ ψᵗ Ω₁ [] ∷ []
```

## §1 读下标: `Ω_ω` 对 `Ω_Ω`

`j = Ω_ω` 不可数, 所以 `toT₀ j` 没有意义; 要读的是下标 ω, `x = ω+1`. 这是 `D♯` 不做的第一个情形.

```agda
sub-lt : cmpᵀ (Ωt ω) OO ≡ lt
sub-lt = refl

sub-nat : ∀ n → cmpᵀ (Ωt ω) (fsT OO (natᵗ n)) ≡ gt
sub-nat zero    = refl
sub-nat (suc n) = refl

sub-read : cmpᵀ (Ωt ω) (fsT OO (sucT ω)) ≡ lt
sub-read = refl
```

## §2 读尾项: `Ω_Ω + Ω_ω` 对 `Ω_Ω·2`

`j` 的首项下标是 Ω₁, 而分支 `x` 可数, 所以 "读首项下标" 没有意义; `x` 要由**尾项**的下标给出. 目标与 `j` 共享的前缀 `Ω_Ω` 要先被认出来并扣掉, 所以 `x` 依赖目标.

```agda
rel-j : T
rel-j = ψᵗ Ω₁ [] ∷ ψᵗ ω [] ∷ []

rel-lt : cmpᵀ rel-j OO·2 ≡ lt
rel-lt = refl

rel-nat : ∀ n → cmpᵀ rel-j (fsT OO·2 (natᵗ n)) ≡ gt
rel-nat zero    = refl
rel-nat (suc n) = refl

rel-read : cmpᵀ rel-j (fsT OO·2 (sucT ω)) ≡ lt
rel-read = refl

-- `Ω_Ω + 1` 对同一目标: 这是任务单上的第三个点
rel-small : cmpᵀ (sucT OO) (fsT OO·2 (natᵗ 1)) ≡ lt
rel-small = refl
```

## §3 读被折叠的参数: `ψ₁(Ω_Ω + Ω_s)` 对 `ψ₁(Ω_Ω·2)`

目标 `T = ψ₁(Ω_Ω·2)`, `T[x] = ψ₁(Ω_Ω + Ω_x)`. `j = T[2]`, 共尾度 ω (`hid-cof`): `Ω₂` 的共尾度下标 1, `1+1 > 1`, 规则 6 折叠. 它的基本列是 `ψ₁(Ω_Ω + γ n)`, `γ 0 = Ω₁`, `γ (n+1) = ψ₁(Ω_Ω + γ n)` (`hid-fs`). **`Ω₂` 不出现在任何一项里, 但 `x` 必须至少是 3 (`hid-need`).** 所以读数要反演 ψ 的 `rise` 分支; 这个分支只在轨道 `γ n` 上用参数函数 (`InaccSingularSharp.rise-forgets`).

```agda
T₁ : T
T₁ = ψᵗ (natᵗ 1) OO·2 ∷ []

hid : T
hid = fsT T₁ (natᵗ 2)

hid-form : hid ≡ ψᵗ (natᵗ 1) (ψᵗ Ω₁ [] ∷ Ωn 2) ∷ []
hid-form = refl

hid-cof : cof hid ≡ cω
hid-cof = refl

hid-fs0 : fsn hid 0 ≡ ψᵗ (natᵗ 1) (ψᵗ Ω₁ [] ∷ Ωn 1) ∷ []
hid-fs0 = refl

hid-fs1 : fsn hid 1 ≡ ψᵗ (natᵗ 1) (ψᵗ Ω₁ [] ∷ fsn hid 0) ∷ []
hid-fs1 = refl

hid-lt : cmpᵀ hid T₁ ≡ lt
hid-lt = refl

hid-need : cmpᵀ hid (fsT T₁ (natᵗ 2)) ≡ eq   -- `x = 2` 还不够, 这是相等
hid-need = refl

hid-3 : cmpᵀ hid (fsT T₁ (natᵗ 3)) ≡ lt
hid-3 = refl

-- 同样的形状, 下标 ω: 没有自然数够大
hid′ : T
hid′ = fsT T₁ ω

hid′-nat : ∀ n → cmpᵀ hid′ (fsT T₁ (natᵗ n)) ≡ gt
hid′-nat zero    = refl
hid′-nat (suc n) = refl

hid′-lt : cmpᵀ hid′ T₁ ≡ lt
hid′-lt = refl
```
