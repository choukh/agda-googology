# 统一值模拟: 有限层号与塔第 1 项的 ψ₀(Ω_ω) 下界

> 验收文件. 编译定理, 无前提: `lower-nat` (`lower-fin` 写在 `fin n` 与 `natᴵ n` 上, 一切 n); `LOWER′-1` (`YiUpValTw1.LOWER′` 在 m = 1 的全部: 链点 `pt′ 1` 的层号是 ℕ 极限, 各分量是有限层号, 底经 `ok-dL` 不降); `ω-tw1 : ψ⁰(Ω (κ′ 1)) ≼ read Tw1′`, 即参照在层号 ω 上的 ψ₀(Ω_ω) 不高于塔第 1 项的闭项.
> ℕ 极限层号只用到 `ψ⊥` 的嵌入行与 "底不降"; 不同号的两行只出现在底里. m = 2 起见 `YiUpLimRows`.
> 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUpSimTw1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock renaming (L to LF)
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt)
open import OCF.Lean.YiFreshLegal using (seq)
open import OCF.Lean.YiFreshValRead using (T₀; read; limcum≽)
open import OCF.Lean.YiPhiBlock hiding (psh; pshBr)
open import OCF.Lean.YiPhiCheck using (fin; Ev-fin)
open import OCF.Lean.YiUpFold
open import OCF.Lean.YiUpLegal using (dL)
open import OCF.Lean.YiUpValTw1 using (g₁; lv-pt1; pt′; G′; εh; Tw1′; κ′; LOWER′)
open import OCF.Lean.YiUpSimRel using (Corr; cz; cs)
open import OCF.Lean.YiUpSimFold using (FinL; fz; fs; OKB; ok-B₀; ok-dL; lower-fin)

import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼l; l≼)
```

## 有限层号

```agda
finL : (n : ℕ) → FinL (fin n)
finL zero    = fz
finL (suc n) = fs (finL n)

corr-nat : (n : ℕ) → Corr (L.natᴵ n) (fin n)
corr-nat zero    = cz
corr-nat (suc n) = cs (corr-nat n)

lower-nat : (n : ℕ) (B : Base (fin n)) → OKB (fin n) B
  → L.ψ⁰ (L.Ω (L.natᴵ n)) ≼ read (ψ⊥ (fin n) (Ev-fin n) B (Ωt (fin n)))
lower-nat n B ok = lower-fin (finL n) (Ev-fin n) B ok (corr-nat n)
```

## ℕ 极限层号的分量

`Ωt (lim g)` 的第 n 项是前 n 项上嵌入第 n 个孩子的 Ω 树; 折到第 0 层交给孩子层, 底是前缀的折叠, 仍满足 `OKB`.

```agda
lowerLim : (g : ℕ → LF) (ε : Ev (lim g)) (B : Base (lim g)) → OKB (lim g) B
  → ∀ n {i} → FinL (g n) → Corr i (g n)
  → L.ψ⁰ (L.Ω i) ≼ read (ψ⊥ (lim g) ε B (seq (Ωt (lim g)) n))
lowerLim g ε B ok zero    fn c = lower-fin fn (ε zero) (dL g ε B zero zero) (ok-dL g ε B ok zero zero) c
lowerLim g ε B ok (suc n) fn c =
  lower-fin fn (ε (suc n)) (dL g ε B (suc n) (seq (Ωt (lim g)) n))
    (ok-dL g ε B ok (suc n) (seq (Ωt (lim g)) n)) c
```

## 链点 `pt′ 1` (层号 ω)

```agda
IsNum : Tr zero → Set
IsNum zero    = ⊤
IsNum (suc x) = IsNum x
IsNum _       = ⊥

num-1+ : (x : Tr zero) → IsNum x → IsNum (suc zero + x)
num-1+ zero    h = tt
num-1+ (suc x) h = num-1+ x h

nm : ℕ → Tr zero
nm = iter (suc zero +_) (suc zero)

numN : ∀ n → IsNum (nm n)
numN zero    = tt
numN (suc n) = num-1+ (nm n) (numN n)

fin-↑ : (x : Tr zero) → IsNum x → FinL (zero ⊕ ↑ zero x)
fin-↑ zero    h = fz
fin-↑ (suc x) h = fs (fin-↑ x h)

corr-↑ : (x : Tr zero) → IsNum x → (h : L.HS (read x)) → Corr (L.toLevel (read x) h) (zero ⊕ ↑ zero x)
corr-↑ zero    n h = cz
corr-↑ (suc x) n h = cs (corr-↑ x n (L.hs⁻ h))

pt1-form : pt′ 1 ≡ lim nm
pt1-form = refl

LOWER′-1 : L.ψ⁰ (L.Ω (κ′ 1)) ≼ read (G′ (pt′ 1))
LOWER′-1 = l≼ (λ n → ≼l n (lowerLim g₁ (εh (pt′ 1)) (B₀ (lim g₁)) (ok-B₀ (lim g₁)) n
  (fin-↑ (nm n) (numN n)) (corr-↑ (nm n) (numN n) _)))

ω-tw1 : L.ψ⁰ (L.Ω (κ′ 1)) ≼ read Tw1′
ω-tw1 = limcum≽ (λ k → G′ (pt′ k)) 1 LOWER′-1
```
