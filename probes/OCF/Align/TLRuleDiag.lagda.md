# 折叠是和的作用 (六): 对角线也是和

> 不含记号. 入口 [TLRule](TLRule.lagda.md). `cell` 那条对角线的相邻项各在自己的世界里算, 所以 `Top` 没有 `Lg`. 这里把它写成一路走下去: 上一个世界 $u$ 的状态延到下一个世界 $v$, 输入接着走 $\Omega_v-\Omega_u$. 新的层是 `sum v (差)`, **$v\lhd$ 新层是字面的, 不用证**. 所以 `TopΣ` 带 `Lg`, 可以直接当下一站的层 (`next`).
>
> 状态延长: 目标不高于 $u$ 时用旧状态; 高于 $u$ 时输入里的节点都低于目标, 没有链, 重新走一遍 $\Omega_u$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLRuleDiag where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg; _⊲_; ⊲-tr; lg⊲; z⊲; cmpF)
import OCF.Align.CumReadCF as C
import OCF.Align.TLRuleSum as N
open N using (D; n0; n1; _⨾_; nl; ni; sum; sum-fst; Lg-sum; accL; ω⋅; Ωd; Dif; Ψ; Lg-Ψ; module Fold)
```

## §1 定义

```agda
record Cell : Set where
  constructor mk
  field
    u  : A
    lu : Lg u
    v  : A
    lv : Lg v
    p  : u ⊲ v
    Y  : Fold.St u lu ω⋅
open Cell public

module Ext (c : Cell) where
  open Fold (v c) (lv c) ω⋅

  A₀ : D (v c) → St → St
  A₀ _ Y′ = Step Y′

  -- 状态延到世界 v
  ext : St
  ext {t} τ with cmpF (p c) τ (lv c)
  ... | inj₁ q = Y c q
  ... | inj₂ q = Act C.self (Ωd (u c) (p c) (lu c)) (λ _ → n0) τ

  Δ : St
  Δ = Run (accL (v c)) C.self A₀ n0 (Dif (v c) (p c) C.self (lv c)) ext

  Y′ : St
  Y′ = ext ⊕ Δ

  d₀ : D azero
  d₀ = Δ (z⊲ (v c))

start : Cell
start = mk one tt (Ψ one tt) (Lg-Ψ one tt) (sum-fst (asuc azero) (N.Ψd one tt)) Y₀
  where
  one : A
  one = asuc azero
  open Fold one tt ω⋅
  Y₀ : St
  Y₀ = Act C.self (Ωd one C.self tt) (λ _ → n0)

step : Cell → Cell
step c = mk (v c) (lv c) (sum (v c) d₀) (Lg-sum (v c) d₀ (lv c)) (sum-fst (v c) d₀) Y′
  where open Ext c

cellΣ : ℕ → Cell
cellΣ zero = start
cellΣ (suc n) = step (cellΣ n)

v⊲ : ∀ n → v (cellΣ n) ⊲ v (cellΣ (suc n))
v⊲ n = p (cellΣ (suc n))

TopΣ : A
TopΣ = alim (λ n → v (cellΣ n))

Lg-TopΣ : Lg TopΣ
Lg-TopΣ = v⊲ , (λ n → lv (cellΣ n))

fghΣ : ℕ → ℕ
fghΣ = N.FGH′ TopΣ

-- 下一站: 层就是 TopΣ, 没有证明
next : A
next = Ψ TopΣ Lg-TopΣ

Lg-next : Lg next
Lg-next = Lg-Ψ TopΣ Lg-TopΣ
```
