# OT 上的函数：Setzer [Se98] Definitions 2.10–2.13

`+`、`·n`、正规化的 `φ`、`Ω`、`Ωⁿ`（Def 2.10）；`κ⁻`、`ã`、`a⁺`、`a^{−Fi}`、`a^{+Fi}`、`a^{−I}`（Def 2.13）。全部是 T′ 上的原始递归函数；和用 snoc 表之后，「去掉末分量」「首分量」「按末分量拆」都是结构递归。

Definition 2.11 的 `=NF` 不另定义：在 snoc 表示下它就是构造子形状——`zer ▹ phi b c` 即 `=NF φ b c`，`zer ▹ psi κ c` 即 `=NF ψ κ c`，`zer ▹ Om b` 即 `=NF Ω b`，`(a ▹ q) ▹ p` 即 `=₀NF (a ▹ q) + ⟨p⟩`（末分量拆出），前提是整项 ∈ OT。Remark 2.12 (b) 因此是模式匹配。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Inacc.Arith where

open import Mahlo.Inacc.Syntax
open import Mahlo.Inacc.Order
open import Mahlo.Inacc.Closure

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false; _∧_; not; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## 1. 加法与乘自然数（Def 2.10 (a)(b)）

`a = (a₁,…,aₙ)`，`b = (b₁,…,bₘ)`：m = 0 时 `a + b := a`；否则取最大的 j 使 `b₁ ⪯′ aⱼ`（无则 j = 0），`a + b := (a₁,…,aⱼ,b₁,…,bₘ)`。

```agda
dropLt : Tm → PTm → Tm                  -- 从右端去掉所有 ≺′ q 的分量
dropLt zer     q = zer
dropLt (a ▹ p) q = if lt ⟨ p ⟩ ⟨ q ⟩ then dropLt a q else a ▹ p

app : Tm → Tm → Tm                      -- 分量表拼接
app a zer     = a
app a (b ▹ q) = app a b ▹ q

infixl 6 _+_
_+_ : Tm → Tm → Tm
a + zer = a
a + b   = app (dropLt a (hd b)) b

infixl 7 _·_
_·_ : Tm → ℕ → Tm
a · zero  = zer
a · suc n = (a · n) + a
```

## 2. 正规化的 φ、Ω（Def 2.10 (c)(d)(e)）

```agda
φ : Tm → Tm → Tm
φ a b = if inCr a b then b
        else (if isZero b ∧ isGT a then a else ⟨ phi a b ⟩)

Ω : Tm → Tm
Ω a = if isZero a then zer else (if isFiT a then a else ⟨ Om a ⟩)

Ωⁿ : Tm → ℕ → Tm                        -- Ω⁰_a := a，Ω^{n+1}_a := Ω_{Ωⁿ_a}
Ωⁿ a zero    = a
Ωⁿ a (suc n) = Ω (Ωⁿ a n)
```

## 3. 基数的前驱与相邻基数（Def 2.13）

- `κ⁻`：`(Ω′_{s+1})⁻ := Ω_s`，`I⁻ := 0`。
- `ã`：a 以下（含）最大的基数；`a⁺`：a 以上最小的基数；`a^{−Fi}`：a 以下（含）最大的 Fi′ 元素；`a^{+Fi}`：a ≺ I 时 a 以上最小的 Fi′ 元素。
- 和：看首分量 a₀。`a =NF φ b c`：看 `max{b,c}`。`a =NF ψ_b c`，b ≠ I：`ã := b⁻`，`a⁺ := b`，`a^{±Fi} := b^{±Fi}`。`a =NF ψ_I c`：`ã := a^{−Fi} := a`，`a⁺ := Ω_{a+1}`，`a^{+Fi} := ψ_I(c+1)`。`a =NF Ω_b`：`ã := a`，`a^{−Fi} := b^{−Fi}`，`a⁺ := Ω_{b+1}`，`a^{+Fi} := b^{+Fi}`。`Ĩ := I`，`I⁺ := Ω_{I+1}`，`I^{±Fi} := I`。`0̃ := 0^{−Fi} := 0`，`0⁺ := Ω_1`，`0^{+Fi} := ψ_I 0`。

`max{b,c}` 的两支各自结构递归，所以不必先算 `max` 再递归。

```agda
κ⁻ : Reg → Tm
κ⁻ (ΩR a) = Ω (pred a)
κ⁻ IR     = zer

mutual
  tilde : Tm → Tm                       -- ã
  tilde zer         = zer
  tilde (zer ▹ p)   = tildeP p
  tilde (a ▹ q ▹ p) = tilde (a ▹ q)

  tildeP : PTm → Tm
  tildeP (phi b c)      = if lt b c then tilde c else tilde b
  tildeP (psi (ΩR b) c) = κ⁻ (ΩR b)
  tildeP (psi IR c)     = ⟨ psi IR c ⟩
  tildeP (Om b)         = ⟨ Om b ⟩
  tildeP I              = I′

mutual
  plus : Tm → Tm                        -- a⁺
  plus zer         = Ω₁
  plus (zer ▹ p)   = plusP p
  plus (a ▹ q ▹ p) = plus (a ▹ q)

  plusP : PTm → Tm
  plusP (phi b c)      = if lt b c then plus c else plus b
  plusP (psi (ΩR b) c) = ⟨ Om b ⟩
  plusP (psi IR c)     = Ω (⟨ psi IR c ⟩ + one)
  plusP (Om b)         = Ω (b + one)
  plusP I              = Ω (I′ + one)

mutual
  mFi : Tm → Tm                         -- a^{−Fi}
  mFi zer         = zer
  mFi (zer ▹ p)   = mFiP p
  mFi (a ▹ q ▹ p) = mFi (a ▹ q)

  mFiP : PTm → Tm
  mFiP (phi b c)      = if lt b c then mFi c else mFi b
  mFiP (psi (ΩR b) c) = mFi b                    -- (Ω′_b)^{−Fi} = b^{−Fi}
  mFiP (psi IR c)     = ⟨ psi IR c ⟩
  mFiP (Om b)         = mFi b
  mFiP I              = I′

mutual
  pFi : Tm → Tm                         -- a^{+Fi}
  pFi zer         = ψI0
  pFi (zer ▹ p)   = pFiP p
  pFi (a ▹ q ▹ p) = pFi (a ▹ q)

  pFiP : PTm → Tm
  pFiP (phi b c)      = if lt b c then pFi c else pFi b
  pFiP (psi (ΩR b) c) = pFi b                    -- (Ω′_b)^{+Fi} = b^{+Fi}
  pFiP (psi IR c)     = ⟨ psi IR (c + one) ⟩
  pFiP (Om b)         = pFi b
  pFiP I              = I′

mI : Tm → Tm                            -- a^{−I} := 0 若 a ≺ I，否则 I
mI a = if lt a I′ then zer else I′
```

## 4. 算例

```agda
_ : one + one ≡ (one ▹ phi zer zer)
_ = refl
_ : one + ω′ ≡ ω′                       -- 1 + ω = ω
_ = refl
_ : ω′ + one ≡ (ω′ ▹ phi zer zer)
_ = refl
_ : ω′ · 2 ≡ (ω′ ▹ phi zer one)
_ = refl
_ : φ zer one ≡ ω′                       -- φ_0 1 = ω
_ = refl
_ : φ one zer ≡ ε₀′
_ = refl
_ : φ zer ε₀′ ≡ ε₀′                      -- ε₀ ∈ Cr(0)：φ_0 ε₀ = ε₀
_ = refl
_ : φ zer Ω₁ ≡ Ω₁                        -- Ω₁ ∈ G′，0 ≺ Ω₁：φ_0 Ω₁ = Ω₁
_ = refl
_ : φ Ω₁ zer ≡ Ω₁                        -- b = 0，a ∈ G′：φ_{Ω₁} 0 = Ω₁
_ = refl
_ : Ω zer ≡ zer
_ = refl
_ : Ω I′ ≡ I′
_ = refl
_ : Ω ψI0 ≡ ψI0                          -- ψ_I 0 ∈ Fi′：Ω_{ψ_I 0} = ψ_I 0
_ = refl
_ : Ω one ≡ Ω₁
_ = refl
_ : Ωⁿ zer 2 ≡ zer
_ = refl
_ : Ωⁿ one 2 ≡ ⟨ Om Ω₁ ⟩                 -- Ω_{Ω_1}
_ = refl

_ : κ⁻ (ΩR one) ≡ zer                    -- Ω_1⁻ = Ω_0 = 0
_ = refl
_ : κ⁻ (ΩR (one ▹ phi zer zer)) ≡ Ω₁     -- Ω_2⁻ = Ω_1
_ = refl
_ : tilde ω′ ≡ zer
_ = refl
_ : tilde (Ω₁ ▹ phi zer zer) ≡ Ω₁        -- (Ω₁ + 1)~ = Ω₁
_ = refl
_ : tilde ψΩ₁0 ≡ zer                     -- (ψ_{Ω₁} 0)~ = Ω₁⁻ = 0
_ = refl
_ : tilde endpoint ≡ zer
_ = refl
_ : plus zer ≡ Ω₁
_ = refl
_ : plus ψΩ₁0 ≡ Ω₁
_ = refl
_ : plus Ω₁ ≡ ⟨ Om (one ▹ phi zer zer) ⟩ -- Ω₁⁺ = Ω_2
_ = refl
_ : plus I′ ≡ ⟨ Om I+1 ⟩
_ = refl
_ : plus ψI0 ≡ ⟨ Om (ψI0 ▹ phi zer zer) ⟩ -- (ψ_I 0)⁺ = Ω_{ψ_I 0 + 1}
_ = refl
_ : mFi Ω₁ ≡ zer
_ = refl
_ : pFi Ω₁ ≡ ψI0
_ = refl
_ : pFi ψI0 ≡ ⟨ psi IR one ⟩             -- (ψ_I 0)^{+Fi} = ψ_I 1
_ = refl
_ : mFi I+ω ≡ I′
_ = refl
_ : mI Ω₁ ≡ zer
_ = refl
_ : mI I+1 ≡ I′
_ = refl
```
