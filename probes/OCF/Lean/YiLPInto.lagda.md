# 合法块: 塔各项不超过终点 (Into)

> 验收文件 (经 [YiLPRead](YiLPRead.lagda.md) 读进参照框架). 编译定理, 无前提: `EBOᶜ` 第 n 支的底是由前缀折出的底, 它按 `_⊴_` 不低于 `B₀ (tw n)` (`B₀⊴dL`, 对一切前缀); `Into 0` (`into-0`).
> 条件定理: 塔第 n 项的 Ω 树对 (`Ev-tw n`, `Rt-tw n`) 基底单调时 `Into n` (`into-bm`); 所以 `BaseMonoΩt` 推出一切 `Into n` (`into-all-bm`); 坐标单调 `CoordMono (tw n)` 推出 `Into (n+1)` (`into-coord`).
> 有限测试: `Into 1` 用到的两条回灌链从第 1 项起坐标不同, 右边第 1 项是左边第 1 项的 `next` (`chain-B₀`, `chain-B₁`), 所以那里比较的是两个不同孩子层上的折叠. 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLPInto where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLPVal hiding (emb; emb-mono)
open import OCF.Lean.YiLPMono
open import OCF.Lean.YiLPRead using (readᴸ; ≼→read)
open import OCF.Align.Value using () renaming (_≼_ to _≼ᴸ_)
```

## 陈述

`Intoᵛ n`: 值的陈述; `Into n`: 与 `YiRefTw2.Into` 同形, 读进参照框架后比较.

```agda
Intoᵛ : ℕ → Set
Intoᵛ n = val zero (twᶜ n) ≼ val zero EBOᶜ

Into : ℕ → Set
Into n = readᴸ (twᶜ n) ≼ᴸ readᴸ EBOᶜ

ᵛ→ᴿ : (n : ℕ) → Intoᵛ n → Into n
ᵛ→ᴿ n d = ≼→read d
```

## 折叠不低于底的分量

```agda
base≼⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (x : Tr ℓ) → val zero (b⊥ B) ≼ val zero (ψ⊥ ℓ ε ρ B x)
base≼⊥ ℓ ε ρ B x with zl x
... | inj₁ refl = ≼-refl _
... | inj₂ d    = ◁→≼ (val-mono zero (mono⊥ ℓ ε ρ B d))

start≼s : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr ℓ)
        → val j β ≼ val j (ψs ℓ ε ρ B j w β nβ x)
start≼s ℓ ε ρ B j w β nβ x with zl x
... | inj₁ refl = ≼-refl _
... | inj₂ d    = ◁→≼ (val-mono j (monos ℓ ε ρ B j w β nβ d))
```

## `EBOᶜ` 的各支与它们的底

`pre n`: `EBOᶜ` 的第 n 支之前的前缀. 第 n 支是塔第 n 项的 Ω 树以 `dL … n (pre n)` 为底折到第 0 层.

```agda
pre : ℕ → Tr Λ
pre zero    = zero
pre (suc n) = cumΩ tw n

B₀⊴dL : (n : ℕ) (x : Tr Λ) → B₀ (tw n) ⊴ dL tw Ev-Λ Rt-Λ (B₀ Λ) n x
B₀⊴dL n x = base≼⊥ Λ Ev-Λ Rt-Λ (B₀ Λ) x
          , λ j w → start≼s Λ Ev-Λ Rt-Λ (B₀ Λ) j (inl n w) (Ωt j) (Ωt-nz j) x

branch : (n : ℕ) → val zero (ψ⊥ (tw n) (Ev-tw n) (Rt-tw n) (dL tw Ev-Λ Rt-Λ (B₀ Λ) n (pre n)) (Ωt (tw n)))
                 ≼ val zero EBOᶜ
branch zero    = ≼l zero (≼-refl _)
branch (suc n) = ≼l (suc n) (≼-refl _)
```

## Into

```agda
into-bm : (n : ℕ) → BM⊥ᵉ (tw n) (Ev-tw n) (Rt-tw n) (Ωt (tw n)) → Intoᵛ n
into-bm n bm = ≼-trans (bm (B₀ (tw n)) (dL tw Ev-Λ Rt-Λ (B₀ Λ) n (pre n)) (B₀⊴dL n (pre n))) (branch n)

into-0 : Into 0
into-0 = ᵛ→ᴿ 0 (into-bm 0 (bm-zero⊥ (Ωt zero) tt tt))

into-all-bm : BaseMonoΩt → (n : ℕ) → Into n
into-all-bm bm n = ᵛ→ᴿ n (into-bm n (bm (tw n) (Ev-tw n) (Rt-tw n)))

into-coord : (n : ℕ) → CoordMono (tw n) (Ev-tw n) (Rt-tw n) → Into (suc n)
into-coord n cm = ᵛ→ᴿ (suc n) (into-bm (suc n) (bm-Nx (tw n) (Ev-tw n) (Rt-tw n) cm))

into-all-coord : ((n : ℕ) → CoordMono (tw n) (Ev-tw n) (Rt-tw n)) → (n : ℕ) → Into n
into-all-coord cm zero    = into-0
into-all-coord cm (suc n) = into-coord n (cm n)
```

## `Into 1` 的两条回灌链 (有限测试)

塔第 1 项, 左边的底 `B₀ (tw 1)`, 右边的底 `B₁` (EBOᶜ 第 1 支). 链的一步是 `CoordMono` 里的那一步; 第 0 项两边都是 `zero`.

```agda
st₁ : Base (tw 1) → Tr zero → Tr zero
st₁ B c = ψs (tw 1) (Ev-tw 1) (Rt-tw 1) B zero (ink self) (bs B zero (ink self)) (ns B zero (ink self)) (Gc zero c)

B₁ : Base (tw 1)
B₁ = dL tw Ev-Λ Rt-Λ (B₀ Λ) 1 (pre 1)

chain-B₀ : st₁ (B₀ (tw 1)) zero ≡ next (suc zero) ◃s
chain-B₀ = refl

chain-B₁ : st₁ B₁ zero ≡ next (st₁ (B₀ (tw 1)) zero) (ns B₁ zero (ink self))
chain-B₁ = refl
```
