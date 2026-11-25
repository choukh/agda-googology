# 终点 `EBOᶜ` 的各支与转移引理

> 验收文件. 编译定理, 无前提: `EBOᶜ` 的读回是各支读回的上确界 (`br≼`, `sup≼`, `EBO≅sup`); 第 n 支是层号 `tw n` 上 `Ωt (tw n)` 以 `dB n = dL tw Ev-Λ Rt-Λ (B₀ Λ) n (pre n)` 为底的折叠 (`branch-eq`, `refl`); 各支的底满足下界条件 (`ok-dB`).
> 转移引理 `transfer`: 参照 X 对第 n 支所在层号上满足 `OKB` 的一切底不高于折叠, 则 X ≼ read EBOᶜ; `transferP` 多带一个第 n 支的底满足的谓词. 不经 Into.
> 有限测试: 第 n+1 支的底的第 0 分量是第 n 支 (`b⊥-dB`); 第 2 支的链起点不是 `Ωt (tw 1)`, 分支是上折像 (`start-dB2`). 不否定什么, 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiEBShape where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead
open import OCF.Lean.YiLSFold using (OKB; ok-B₀; ok-dL)
open import OCF.Lean.YiLSTw1 using (h₁)

import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼)
```

## 各支

`pre n`: 第 n 支之前的前缀; `Fn n B`: 层号 `tw n` 上 Ω 树以 B 为底的折叠.

```agda
pre : ℕ → Tr Λ
pre zero    = zero
pre (suc n) = cumΩ tw n

dB : (n : ℕ) → Base (tw n)
dB n = dL tw Ev-Λ Rt-Λ (B₀ Λ) n (pre n)

Fn : (n : ℕ) → Base (tw n) → Tr zero
Fn n B = ψ⊥ (tw n) (Ev-tw n) (Rt-tw n) B (Ωt (tw n))

br : ℕ → Tr zero
br n = Fn n (dB n)

EBO-lim : EBOᶜ ≡ lim (λ n → ψ⊥ Λ Ev-Λ Rt-Λ (B₀ Λ) (cumΩ tw n))
                     (λ n → mono⊥ Λ Ev-Λ Rt-Λ (B₀ Λ) (◃u (cumΩ tw n) (suc n) (Ωt (tw (suc n))) (Ωt-nz (tw (suc n)))))
EBO-lim = refl

branch-eq : (n : ℕ) → ψ⊥ Λ Ev-Λ Rt-Λ (B₀ Λ) (cumΩ tw n) ≡ br n
branch-eq zero    = refl
branch-eq (suc n) = refl
```

## 上确界

```agda
br≼ : (n : ℕ) → read (br n) ≼ read EBOᶜ
br≼ zero    = ≼l zero (≼-refl _)
br≼ (suc n) = ≼l (suc n) (≼-refl _)

sup≼ : (Y : T₀) → ((n : ℕ) → read (br n) ≼ Y) → read EBOᶜ ≼ Y
sup≼ Y h = l≼ go
  where
  go : (n : ℕ) → read (ψ⊥ Λ Ev-Λ Rt-Λ (B₀ Λ) (cumΩ tw n)) ≼ Y
  go zero    = h zero
  go (suc n) = h (suc n)

EBO≅sup : read EBOᶜ L.≅ L.lim (λ n → read (br n))
EBO≅sup = L.l≅ go
  where
  go : (n : ℕ) → read (ψ⊥ Λ Ev-Λ Rt-Λ (B₀ Λ) (cumΩ tw n)) L.≅ read (br n)
  go zero    = L.≅-refl⁰ _
  go (suc n) = L.≅-refl⁰ _
```

## 各支的底与转移

```agda
ok-dB : (n : ℕ) → OKB (tw n) (dB n)
ok-dB n = ok-dL tw Ev-Λ Rt-Λ (B₀ Λ) (ok-B₀ Λ) n (pre n)

b⊥-dB : (n : ℕ) → b⊥ (dB (suc n)) ≡ br n
b⊥-dB zero    = refl
b⊥-dB (suc n) = refl

transfer : (X : T₀) (n : ℕ) → ((B : Base (tw n)) → OKB (tw n) B → X ≼ read (Fn n B)) → X ≼ read EBOᶜ
transfer X n h = ≼-trans (h (dB n) (ok-dB n)) (br≼ n)

transferP : (X : T₀) (n : ℕ) (P : Base (tw n) → Set) → P (dB n)
  → ((B : Base (tw n)) → OKB (tw n) B → P B → X ≼ read (Fn n B)) → X ≼ read EBOᶜ
transferP X n P pd h = ≼-trans (h (dB n) (ok-dB n) pd) (br≼ n)
```

## 第 2 支的链起点 (有限测试)

层号 `tw 2` 的 Ω 结点的链从分量 `bs B (tw 1) (ink self)` 起步. 标准底给 `Ωt (tw 1)` (分支是 `up zero c (Ωt (h₁ c))`); 第 2 支的底给分支为上折像的 Ω 结点, 上折的底是 `next (Ωt (tw 1))`.

```agda
start-dB2 : bs (dB 2) (tw 1) (ink self)
          ≡ Ω (inj₁ (inj₁ tt)) (λ c → Up (h₁ c) (down stop c) (next (Ωt (tw 1)) (Ωt-nz (tw 1))) _ (Ωt (h₁ c)))
start-dB2 = refl

start-B₀2 : bs (B₀ (tw 2)) (tw 1) (ink self) ≡ Ω (inj₁ (inj₁ tt)) (λ c → up zero c (Ωt (h₁ c)) (Ωt-nz (h₁ c)))
start-B₀2 = refl
```
