# 上折: ℕ 极限层号的两行与链点 `pt′ 2`

> 验收文件. 编译定理 (折叠现有的行, 逐字): ℕ 极限层号上, 目标在孩子 n 里而结点或嵌入在孩子 m 里, `eqℕ m n` 为 `nothing` 时, 结点走默认 (`lim-kp`), 嵌入走回退 (`lim-up`: x 的折叠加孩子以 `B₀` 折到第 0 层的值).
> 有限测试: 塔第 1 项的链点 `pt′ 2` 沿分量 0, 1, 0, 0, 0 走到 "ℕ 极限的后继" (`sl-in-pt2`); 所以 `LOWER′` 在 m = 2 要用到形如 suc (lim g) 的层号, 那里第 `lim g` 层的树要折到孩子里的目标.
> 不否定什么: 没有上界, "这两行使 `LOWER′` 在 m = 2 不成立" 是判断, 见回报. 不改折叠.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUpLimRows where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock renaming (L to LF)
open import OCF.Lean.YiFreshFold using (_+_; ι; eqℕ)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiFold using (kp; kp⁼)
open import OCF.Lean.YiUpFold
open import OCF.Lean.YiUpValTw1 using (pt′)
```

## 两行

```agda
lim-kp : (g : ℕ → LF) (ε : Ev (lim g)) (m n : ℕ) (p : Pos⁼ (g m)) {j : LF} (w : j ≤ g n) {X : Set}
  (K : (q : Pos j) → (Br j q → Br (lim g) (m , p)) → X) (d : X)
  → eqℕ m n ≡ nothing → kp (lim g) ε (m , p) (inl n w) K d ≡ d
lim-kp g ε m n p w K d e rewrite e = refl

lim-up : (g : ℕ → LF) (ε : Ev (lim g)) (B : Base (lim g)) (m n : ℕ) (j : LF) (w : j ≤ g n) (β : Tr j)
  (x : Tr (lim g)) (y : Tr (g m))
  → eqℕ m n ≡ nothing
  → ψs (lim g) ε B j (inl n w) β (up x m y)
  ≡ ψs (lim g) ε B j (inl n w) β x + ι j (ψ⊥ (g m) (ε m) (B₀ (g m)) y)
lim-up g ε B m n j w β x y e rewrite e = refl
```

## `pt′ 2` 里的 "极限的后继"

```agda
cm : ∀ {P B C D} → ℕ → T P B C D → T P B C D
cm n (lim f) = f n
cm n x       = x

isSL : ∀ {P B C D} → T P B C D → Set
isSL (suc (lim _)) = ⊤
isSL _             = ⊥

sl-in-pt2 : isSL (cm 0 (cm 0 (cm 0 (cm 1 (cm 0 (pt′ 2))))))
sl-in-pt2 = tt
```
