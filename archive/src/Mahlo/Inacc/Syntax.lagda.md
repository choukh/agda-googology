# OT_I 的语法：Setzer [Se98] Definition 2.2

方案 A 的第一块（[../DECISION.md](../DECISION.md)、[../ROADMAP.md](../ROADMAP.md) B1）。转写 Setzer, *Well-ordering proofs for Martin-Löf type theory* (1998) §2.1 的项系统 T′——ML₁W（一个宇宙 + W）的记号系统，端点 ψ_{Ω₁}Ω_{I+ω}。来源 `../Sources/setzer1998-wellordering.txt` 行 458–560，**文本可抽取，逐字对照**。

设计：

- 原始语法用归纳类型（Setzer 的项是自然数编码，这里用构造子代替编码）。
- **和写成 snoc 表**：`(a₀,…,aₙ) = ((zer ▹ a₀) ▹ …) ▹ aₙ`。理由：Definition 2.11 的 `a =₀NF b + c` 把**末**分量 c 拆出来（c ∈ A′），Definition 5.3 的 K^a、Lemma 4.17 (ii) 都沿这个拆法递归——snoc 表让它成为结构递归。主元项 `(a) = a` 就是 `zer ▹ a`，不另设构造子。
- Definition 2.2 的子类 Suc′、G′、Car′、R′、Fi′ 是**可判定谓词**（原文："All the sets and length can be defined primitive recursively"）；T′ 的成员条件（ψ 的下标 ∈ R′、Ω′ 的下标 ≠ 0）也是谓词，不放进类型——句法相等与枚举因此平凡。
- 互递归块里不经 `regTm`／高阶 `all` 转手，另写 `…R`／`…L` 版本，终止检查器才看得见结构递减。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Inacc.Syntax where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Bool.Base using (Bool; true; false; _∧_; not)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## 1. 项（T′1–T′6）

| 原文 | 这里 |
|---|---|
| (T′1) `0_OT` | `zer` |
| (T′2) `(a₀,…,aₙ)`，n > 0，aᵢ ∈ A′ | `a ▹ p`，a ≠ zer |
| 单主元项 `(a) := a` | `zer ▹ p`，记 `⟨ p ⟩` |
| (T′3) `φ′_a b` ∈ A′ | `phi a b` |
| (T′4) `ψ_π b` ∈ G′，π ∈ R′；π = I 时 ∈ Fi′ | `psi π b`，π : `Reg` |
| (T′5) `Ω′_a` ∈ Car′，a ≠ 0；a ∈ Suc′ 时 ∈ R′ | `Om a` |
| (T′6) `I` ∈ Fi′ ∩ R′ | `I` |

`Reg` 是 R′ 的**形状**（Ω′_a 或 I）；`Ω′_a ∈ R′` 还要 `a ∈ Suc′`，由 `isR` 检查。

```agda
data Tm : Set
data PTm : Set
data Reg : Set

infixl 5 _▹_

data Tm where
  zer : Tm                              -- 0
  _▹_ : Tm → PTm → Tm                   -- (a₀,…,aₙ₋₁) ▹ aₙ

data Reg where
  ΩR : Tm → Reg                         -- Ω′_a
  IR : Reg                              -- I

data PTm where
  phi : Tm → Tm → PTm                   -- φ′_a b
  psi : Reg → Tm → PTm                  -- ψ_π b
  Om  : Tm → PTm                        -- Ω′_a
  I   : PTm                             -- I

⟨_⟩ : PTm → Tm                          -- (a) = a
⟨ p ⟩ = zer ▹ p

regTm : Reg → Tm
regTm (ΩR a) = ⟨ Om a ⟩
regTm IR     = ⟨ I ⟩

regP : Reg → PTm
regP (ΩR a) = Om a
regP IR     = I

one : Tm                                -- 1_OT := φ′_0 0
one = ⟨ phi zer zer ⟩
```

分量表（首分量在前）与其逆，以及首、末分量：

```agda
toListAcc : Tm → List PTm → List PTm
toListAcc zer     acc = acc
toListAcc (a ▹ p) acc = toListAcc a (p ∷ acc)

toList : Tm → List PTm
toList a = toListAcc a []

fromList : List PTm → Tm
fromList = go zer
  where
    go : Tm → List PTm → Tm
    go a []       = a
    go a (p ∷ ps) = go (a ▹ p) ps

hd : Tm → PTm                           -- 首分量 a₀（0 时取 I，不会用到）
hd zer           = I
hd (zer ▹ p)     = p
hd (a ▹ q ▹ p)   = hd (a ▹ q)

lastP : Tm → PTm                        -- 末分量（0 时取 I，不会用到）
lastP zer     = I
lastP (_ ▹ p) = p

pred : Tm → Tm                          -- 去掉末分量；a ∈ Suc′ 时 pred a + 1 = a
pred zer     = zer
pred (a ▹ _) = a

NZ : Tm → Set                           -- 「不是 0」：和 (b ▹ p) 的 b 必须非零
NZ zer     = ⊥
NZ (_ ▹ _) = ⊤
```

`NZ` 的用处：良序证明里按 =NF 拆和时，递归调用要把 `b`（去掉末分量的部分）**整个**传给辅助函数——若在辅助函数里再写 `a ▹ q ▹ p` 这样的嵌套模式，Agda 的终止检查器在 `with` 之后看不出 `a ▹ q` 是 `a ▹ q ▹ p` 的子项（实测：互递归块里 `with` 之后重建的项失去结构序）。所以引理对一般的 `b ▹ p` 陈述，附 `NZ b`。

## 2. 子类（Def 2.2 的 Suc′、G′、Car′、R′、Fi′、Lim′）

(T′7)：R′ ⊆ Car′ ⊆ G′ ⊆ A′ ⊆ T′，Fi′ ⊆ Car′ ⊆ G′，Suc′ ⊆ T′。A′ 就是全部主元项 `PTm`。

```agda
isZero : Tm → Bool
isZero zer = true
isZero _   = false

isSucP : PTm → Bool                     -- Suc′ 的主元形状：φ′_0 0
isSucP (phi a b) = isZero a ∧ isZero b
isSucP _         = false

isSuc : Tm → Bool                       -- Suc′：末分量是 φ′_0 0
isSuc zer     = false
isSuc (_ ▹ p) = isSucP p

isG : PTm → Bool                        -- G′ = {ψ, Ω′, I}
isG (phi _ _) = false
isG _         = true

isFi : PTm → Bool                       -- Fi′ = {ψ_I b, I}
isFi (psi IR _) = true
isFi I          = true
isFi _          = false

isCar : PTm → Bool                      -- Car′ = {Ω′_a} ∪ Fi′
isCar (Om _) = true
isCar p      = isFi p

isR : PTm → Bool                        -- R′ = {Ω′_a : a ∈ Suc′} ∪ {I}
isR (Om a) = isSuc a
isR I      = true
isR _      = false

isLim : Tm → Bool                       -- Lim′ := T′ ∖ ({0} ∪ Suc′)
isLim t = not (isZero t) ∧ not (isSuc t)

-- 对 Tm 的版本：单主元项看其主元，和与 0 都不在这些类里
isFiT isCarT isRT isGT : Tm → Bool
isFiT (zer ▹ p) = isFi p ; isFiT _ = false
isCarT (zer ▹ p) = isCar p ; isCarT _ = false
isRT (zer ▹ p) = isR p ; isRT _ = false
isGT (zer ▹ p) = isG p ; isGT _ = false

isRR : Reg → Bool                       -- Reg 的形状是否真在 R′
isRR (ΩR a) = isSuc a
isRR IR     = true
```

## 3. T′ 的成员条件

(T′4) 要 π ∈ R′，(T′5) 要 a ≠ 0。

```agda
mutual
  inT′ : Tm → Bool
  inT′ zer     = true
  inT′ (a ▹ p) = inT′ a ∧ inT′P p

  inT′P : PTm → Bool
  inT′P (phi a b) = inT′ a ∧ inT′ b
  inT′P (psi π b) = inT′R π ∧ isRR π ∧ inT′ b
  inT′P (Om a)    = inT′ a ∧ not (isZero a)
  inT′P I         = true

  inT′R : Reg → Bool
  inT′R (ΩR a) = inT′ a ∧ not (isZero a)
  inT′R IR     = true
```

## 4. `length`（Def 2.2）与 BCW 范数

`length`：0 与 I 为 1；和为分量之和；φ′_a b 为 `len a + len b`；ψ_π b 为 `len π + len b`；Ω′_a 为 `len a + 1`。`length(0) = 1` 不能改成 0：否则 `length(φ′_0 0) = 0` 不比分量大，Remark 2.12 (c) 失效。

BCW 范数 `N`（[../Notation/ExtOT](../Notation/ExtOT.lagda.md) 的做法）：非和函数符号与非零常量的出现次数。两者线性互控（常数 2）——这里只定义，互控留到需要时证。

```agda
mutual
  len : Tm → ℕ
  len zer         = 1
  len (zer ▹ p)   = lenP p
  len (a ▹ q ▹ p) = len (a ▹ q) + lenP p

  lenP : PTm → ℕ
  lenP (phi a b) = len a + len b
  lenP (psi π b) = lenR π + len b
  lenP (Om a)    = len a + 1
  lenP I         = 1

  lenR : Reg → ℕ
  lenR (ΩR a) = len a + 1
  lenR IR     = 1

mutual
  N : Tm → ℕ
  N zer     = 0
  N (a ▹ p) = N a + NP p

  NP : PTm → ℕ
  NP (phi a b) = 1 + N a + N b
  NP (psi π b) = 1 + NR π + N b
  NP (Om a)    = 1 + N a
  NP I         = 1

  NR : Reg → ℕ
  NR (ΩR a) = 1 + N a
  NR IR     = 1
```

## 5. 句法相等

`≺′` 的 (≺′2)(≺′3)(≺′5) 要判 `a = b`。项是有限树，相等可判定。

```agda
mutual
  eqT : Tm → Tm → Bool
  eqT zer     zer     = true
  eqT (a ▹ p) (b ▹ q) = eqT a b ∧ eqP p q
  eqT _       _       = false

  eqP : PTm → PTm → Bool
  eqP (phi a b) (phi c d) = eqT a c ∧ eqT b d
  eqP (psi π b) (psi κ d) = eqR π κ ∧ eqT b d
  eqP (Om a)    (Om c)    = eqT a c
  eqP I         I         = true
  eqP _         _         = false

  eqR : Reg → Reg → Bool
  eqR (ΩR a) (ΩR c) = eqT a c
  eqR IR     IR     = true
  eqR _      _      = false
```

## 6. 大小（枚举与递归测度用）

`size ⟨ p ⟩ = 1 + sizeP p`，使「大小 ≤ n 的项只由大小 ≤ n−1 的部件搭成」。

```agda
mutual
  size : Tm → ℕ
  size zer     = 1
  size (a ▹ p) = size a + sizeP p

  sizeP : PTm → ℕ
  sizeP (phi a b) = 1 + size a + size b
  sizeP (psi π b) = 1 + sizeR π + size b
  sizeP (Om a)    = 1 + size a
  sizeP I         = 1

  sizeR : Reg → ℕ
  sizeR (ΩR a) = 1 + size a
  sizeR IR     = 1
```

## 7. 几个常用项

```agda
ω′ ε₀′ Ω₁ Ωs I′ : Tm
ω′  = ⟨ phi zer one ⟩                    -- ω = φ′_0 1
ε₀′ = ⟨ phi one zer ⟩                    -- ε₀ = φ′_1 0
Ω₁  = ⟨ Om one ⟩                         -- Ω′_1
I′  = ⟨ I ⟩
Ωs  = ⟨ Om I′ ⟩                          -- Ω′_I：(OT5) 排除（I ∈ Fi′）

-- I + 1，I + ω，Ω′_{I+ω}，端点 ψ_{Ω₁}(Ω′_{I+ω})
I+1 I+ω ΩI+ω endpoint : Tm
I+1  = I′ ▹ phi zer zer
I+ω  = I′ ▹ phi zer one
ΩI+ω = ⟨ Om I+ω ⟩
endpoint = ⟨ psi (ΩR one) ΩI+ω ⟩

_ : N endpoint ≡ 7
_ = refl

_ : len endpoint ≡ 8
_ = refl
```

`len endpoint ≡ 8` 与 §66.2 记的 λ_M 的 length 8 一致（同一形状，K 换 I）。
