# 终局 (七): 分支带证据的层号宇宙能写下来 (侦察)

> 不含记号. 结论写在 [EBOTop](EBOTop.lagda.md). **这是侦察, 不是实例.** 问题: `no-Ω₂` 说层号的分支不能对全部原始输入负责, 所以 `limᴼ` 的分支应该只在好输入上. 好输入要读折叠, 折叠要层号, 层号要好输入: 这个循环 Agda 接受吗?
>
> **回答: 接受.** 下面的块过了正性与停机检查: `limᴼ : (k : Lv) → (Σ (Ordᴸ k) (Gd k) → Lv) → Lv`, 树的 `limᵢ` 也只对好输入分支, `Gd k t = E (fold₀ t)`, `fold₀` 在同一个块里. 第一版用 `Ordᴸ (at k r)` 写链, 停机检查失败 (`Pre → Gd → fold₀ → Ordᴸ (at k r) → Pre`, `at k r` 不是结构子项; 临时文件, 记录于此); 把链写成对路径的模式匹配 (`node`) 就过了, 与 [InaccTreeBase](InaccTreeBase.lagda.md) 的 `Low` 同一个手法.
>
> **没有证明的部分, 如实.**
>
> 1. `ev` 是模块参数, **假设**证据处处有. 取 `E = ⊤` 时这个假设平凡, 取 `E = HS` 时它是假的 (`no-⊤`). 所以这里只说明块的形状可以写下来. 真实的设计里两处 `ev _` 要换成闭包定理, 它们要进这个块, 而且要过停机检查: **这一点没有试**. 用 `postulate` 把 `E` 换成真正的 `HS` 的临时文件也过了正性与停机检查 (不进仓库).
> 2. 只有 `rise`, 没有穿透: 判决没有写. 这里只回答类型上的循环, 不回答 $\psi_i$ 的比较从哪里来.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.EBOTopIR where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Align.EBOTopStage using (O₀)

-- 假设: E 与 ev 都是模块参数
module Block (E : O₀ → Set) (ev : ∀ t → E t) where
  data Tree (P : Set) (Br : P → Set) (D : Set) (Dr : D → Set) : Set where
    zero : Tree P Br D Dr
    suc  : Tree P Br D Dr → Tree P Br D Dr
    lim  : (ℕ → Tree P Br D Dr) → Tree P Br D Dr
    limᵢ : (r : P) → (Br r → Tree P Br D Dr) → Tree P Br D Dr
    up   : (d : D) → Dr d → Tree P Br D Dr

  data Lv : Set
  Pre  : Lv → Set
  Low  : (ℓ : Lv) → Pre ℓ → Set
  Dn   : Lv → Set
  DnT  : (ℓ : Lv) → Dn ℓ → Set
  Ordᴸ : Lv → Set
  Gd   : (k : Lv) → Ordᴸ k → Set
  fold₀ : ∀ {k} → Ordᴸ k → O₀
  ψ    : (i : Lv) {k : Lv} → Ordᴸ k → Ordᴸ i
  node : (i K k : Lv) (r : Pre k) → (Low k r → Ordᴸ K) → Ordᴸ i
  Ωs   : (ℓ : Lv) → Ordᴸ ℓ
  add  : ∀ {i} → Ordᴸ i → Ordᴸ i → Ordᴸ i

  data Lv where
    zero : Lv
    suc  : Lv → Lv
    lim  : (ℕ → Lv) → Lv
    limᴼ : (k : Lv) → (Σ (Ordᴸ k) (Gd k) → Lv) → Lv

  Pre zero       = ⊥
  Pre (suc k)    = ⊤ ⊎ Pre k
  Pre (lim f)    = Σ ℕ λ n → Pre (f n)
  Pre (limᴼ k g) = (⊤ ⊎ Pre k) ⊎ Σ (Σ (Ordᴸ k) (Gd k)) λ x → Pre (g x)

  Low (suc k)    (inj₁ _)            = Σ (Ordᴸ k) (Gd k)
  Low (suc k)    (inj₂ r)            = Low k r
  Low (lim f)    (n , r)             = Low (f n) r
  Low (limᴼ k g) (inj₁ (inj₁ _))     = Σ (Ordᴸ k) (Gd k)
  Low (limᴼ k g) (inj₁ (inj₂ r))     = Low k r
  Low (limᴼ k g) (inj₂ (x , r))      = Low (g x) r

  Dn zero       = ⊥
  Dn (suc k)    = ⊤
  Dn (lim f)    = ℕ
  Dn (limᴼ k g) = Σ (Ordᴸ k) (Gd k)

  DnT (suc k)    _ = Ordᴸ k
  DnT (lim f)    n = Ordᴸ (f n)
  DnT (limᴼ k g) x = Ordᴸ (g x)

  Ordᴸ ℓ = Tree (Pre ℓ) (Low ℓ) (Dn ℓ) (DnT ℓ)

  Gd k t = E (fold₀ t)

  Ωs zero       = suc zero
  Ωs (suc k)    = limᵢ (inj₁ tt) (λ x → up tt (proj₁ x))
  Ωs (lim f)    = lim (λ n → up n (Ωs (f n)))
  Ωs (limᴼ k g) = limᵢ (inj₁ (inj₁ tt)) (λ x → up x (Ωs (g x)))

  iter : {A : Set} → (A → A) → A → ℕ → A
  iter f a zero = a
  iter f a (suc n) = f (iter f a n)

  add a zero = a
  add a (suc b) = suc (add a b)
  add a (lim f) = lim (λ n → add a (f n))
  add a (limᵢ r f) = limᵢ r (λ y → add a (f y))
  add a (up d x) = a

  ψ i zero = Ωs i
  ψ i (suc a) = lim (iter (add (ψ i a)) zero)
  ψ i (lim f) = lim (λ n → ψ i (f n))
  ψ i {k} (limᵢ r f) = node i k k r f
  ψ i {suc k}    (up d x) = ψ i {k} x
  ψ i {lim f}    (up d x) = ψ i {f d} x
  ψ i {limᴼ k g} (up d x) = ψ i {g d} x

  node i K (suc k) (inj₁ _) f = lim (λ n → ψ i (f (iter step (Ωs k , ev _) n))) where
    step : Σ (Ordᴸ k) (Gd k) → Σ (Ordᴸ k) (Gd k)
    step x = ψ k (f x) , ev _
  node i K (suc k) (inj₂ r) f = node i K k r f
  node i K (lim h) (n , r) f = node i K (h n) r f
  node i K (limᴼ k g) (inj₁ (inj₁ _)) f = lim (λ n → ψ i (f (iter step (Ωs k , ev _) n))) where
    step : Σ (Ordᴸ k) (Gd k) → Σ (Ordᴸ k) (Gd k)
    step x = ψ k (f x) , ev _
  node i K (limᴼ k g) (inj₁ (inj₂ r)) f = node i K k r f
  node i K (limᴼ k g) (inj₂ (x , r)) f = node i K (g x) r f

  fold₀ t = rd₀ (ψ zero t) where
    rd₀ : Ordᴸ zero → O₀
    rd₀ zero = O₀.zero
    rd₀ (suc a) = O₀.suc (rd₀ a)
    rd₀ (lim f) = O₀.lim (λ n → rd₀ (f n))
    rd₀ (limᵢ () f)
    rd₀ (up () x)
```
