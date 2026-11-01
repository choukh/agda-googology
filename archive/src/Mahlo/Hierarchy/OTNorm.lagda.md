# OT 的两种范数线性互控：§83.4 的形式化与订正

[RESEARCH.md](../RESEARCH.md) §83.4 用边数计算给出 Setzer 的 `length` 与 BCW 范数 `N` 互相受控，结论写作 `N ≤ 2·length` 与 `length ≤ 4·N`。本文件把它形式化，结果**订正两处**：后一条在 `t = 0` 处失效（`len 0 = 1` 而 `nrm 0 = 0`），且常数 `4` 偏松。机器检验过的正确形式是 `nrm t + 1 ≤ 2 · len t` 与 `len t ≤ 2 · nrm t + 1`。

只形式化项语法与两个范数，**不**涉及 `≺`（那是另一套庞大的互递归，不在本文件内），因此这里与 CONTRACT 的 E 无关。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Hierarchy.OTNorm where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-mono-≤; +-monoʳ-≤; n≤1+n; m≤m+n; +-comm)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
```

## 1. 项

按 §65.1 已核的 (T′1)–(T′6)。`P′`（加法主元）单列一个类型，于是 (T′2)+(OT2) 的“和的分量必属 `P′`”成为**类型层面**的事实——§83.3 的有限性论证正是靠它（`0` 不能作和的分量）。和至少两个分量。

```agda
data Tm : Set
data PTm : Set

data Tm where
  zer  : Tm                            -- 0_OT
  prin : PTm → Tm
  sum  : PTm → PTm → List PTm → Tm     -- (a₀,…,aₙ)，n ≥ 1

data PTm where
  M   : PTm                            -- Mahlo 常量
  phi : Tm → Tm → PTm                  -- φ′_a b
  psi : Tm → Tm → PTm                  -- ψ_π b
  Om  : Tm → PTm                       -- Ω′_a
```

## 2. 两个范数

`len` 是 Setzer 随项一起定义的 `length`（§65.1 的 length 栏）；`nrm` 是 BCW §4 配方在 `OT` 上的写法，即 `ω`-型函数符号（`φ′,ψ,Ω′`）与非零常量（`M`）的出现次数。

```agda
mutual
  len : Tm → ℕ
  len zer          = 1
  len (prin p)     = plen p
  len (sum p q ps) = plen p + plen q + plenL ps

  plen : PTm → ℕ
  plen M         = 1
  plen (phi a b) = len a + len b
  plen (psi a b) = len a + len b
  plen (Om a)    = len a + 1

  plenL : List PTm → ℕ
  plenL []       = 0
  plenL (p ∷ ps) = plen p + plenL ps

mutual
  nrm : Tm → ℕ
  nrm zer          = 0
  nrm (prin p)     = pnrm p
  nrm (sum p q ps) = pnrm p + pnrm q + pnrmL ps

  pnrm : PTm → ℕ
  pnrm M         = 1
  pnrm (phi a b) = 1 + nrm a + nrm b
  pnrm (psi a b) = 1 + nrm a + nrm b
  pnrm (Om a)    = 1 + nrm a

  pnrmL : List PTm → ℕ
  pnrmL []       = 0
  pnrmL (p ∷ ps) = pnrm p + pnrmL ps
```

## 3. 算术辅助

```agda
eqA : ∀ a b c → suc (suc (a + b + c)) ≡ suc a + suc b + c
eqA = solve 3 (λ a b c → con 1 :+ (con 1 :+ (a :+ b :+ c))
                      := (con 1 :+ a) :+ (con 1 :+ b) :+ c) refl

eqB : ∀ a b → suc (1 + a + b) ≡ suc a + suc b
eqB = solve 2 (λ a b → con 1 :+ (con 1 :+ a :+ b) := (con 1 :+ a) :+ (con 1 :+ b)) refl

eqC : ∀ a b → 2 * a + 2 * b ≡ 2 * (a + b)
eqC = solve 2 (λ a b → con 2 :* a :+ con 2 :* b := con 2 :* (a :+ b)) refl

eqD : ∀ a → suc (1 + a) ≡ suc a + 1
eqD = solve 1 (λ a → con 1 :+ (con 1 :+ a) := (con 1 :+ a) :+ con 1) refl

eqE : ∀ a → 2 * a + 2 ≡ 2 * (a + 1)
eqE = solve 1 (λ a → con 2 :* a :+ con 2 := con 2 :* (a :+ con 1)) refl

eqF : ∀ a b c → 2 * a + 2 * b + 2 * c ≡ 2 * (a + b + c)
eqF = solve 3 (λ a b c → con 2 :* a :+ con 2 :* b :+ con 2 :* c
                      := con 2 :* (a :+ b :+ c)) refl

eqG : ∀ a b → (2 * a + 1) + (2 * b + 1) ≡ 2 * (1 + a + b)
eqG = solve 2 (λ a b → (con 2 :* a :+ con 1) :+ (con 2 :* b :+ con 1)
                    := con 2 :* (con 1 :+ a :+ b)) refl

eqH : ∀ a → (2 * a + 1) + 1 ≡ 2 * (1 + a)
eqH = solve 1 (λ a → (con 2 :* a :+ con 1) :+ con 1 := con 2 :* (con 1 :+ a)) refl

eqI : ∀ a b c → (2 * a + 1) + (2 * b + 1) + (2 * c) ≡ 2 * (a + b + c) + 2
eqI = solve 3 (λ a b c → (con 2 :* a :+ con 1) :+ (con 2 :* b :+ con 1) :+ (con 2 :* c)
                      := con 2 :* (a :+ b :+ c) :+ con 2) refl
```

## 4. `nrm + 1 ≤ 2 · len`

```agda
mutual
  up : ∀ t → suc (nrm t) ≤ 2 * len t
  up zer      = s≤s z≤n
  up (prin p) = pup p
  up (sum p q ps) =
    ≤-trans (n≤1+n _)
      (≤-trans (≤-reflexive (eqA (pnrm p) (pnrm q) (pnrmL ps)))
        (≤-trans (+-mono-≤ (+-mono-≤ (pup p) (pup q)) (lup ps))
                 (≤-reflexive (eqF (plen p) (plen q) (plenL ps)))))

  pup : ∀ p → suc (pnrm p) ≤ 2 * plen p
  pup M         = ≤-refl
  pup (phi a b) =
    ≤-trans (≤-reflexive (eqB (nrm a) (nrm b)))
      (≤-trans (+-mono-≤ (up a) (up b)) (≤-reflexive (eqC (len a) (len b))))
  pup (psi a b) =
    ≤-trans (≤-reflexive (eqB (nrm a) (nrm b)))
      (≤-trans (+-mono-≤ (up a) (up b)) (≤-reflexive (eqC (len a) (len b))))
  pup (Om a) =
    ≤-trans (≤-reflexive (eqD (nrm a)))
      (≤-trans (+-mono-≤ (up a) (s≤s z≤n)) (≤-reflexive (eqE (len a))))

  lup : ∀ ps → pnrmL ps ≤ 2 * plenL ps
  lup []       = z≤n
  lup (p ∷ ps) =
    ≤-trans (+-mono-≤ (≤-trans (n≤1+n _) (pup p)) (lup ps))
            (≤-reflexive (eqC (plen p) (plenL ps)))
```

## 5. `len ≤ 2 · nrm + 1`

```agda
mutual
  down : ∀ t → len t ≤ 2 * nrm t + 1
  down zer      = ≤-refl
  down (prin p) = ≤-trans (pdown p) (m≤m+n _ 1)
  down (sum p q ps) =
    ≤-trans (+-mono-≤ (+-mono-≤ (pdown p) (pdown q)) (ldown ps))
      (≤-trans (≤-reflexive (eqF (pnrm p) (pnrm q) (pnrmL ps))) (m≤m+n _ 1))

  pdown : ∀ p → plen p ≤ 2 * pnrm p
  pdown M         = s≤s z≤n
  pdown (phi a b) =
    ≤-trans (+-mono-≤ (down a) (down b)) (≤-reflexive (eqG (nrm a) (nrm b)))
  pdown (psi a b) =
    ≤-trans (+-mono-≤ (down a) (down b)) (≤-reflexive (eqG (nrm a) (nrm b)))
  pdown (Om a) =
    ≤-trans (+-mono-≤ (down a) (≤-refl {1})) (≤-reflexive (eqH (nrm a)))

  ldown : ∀ ps → plenL ps ≤ 2 * pnrmL ps
  ldown []       = z≤n
  ldown (p ∷ ps) =
    ≤-trans (+-mono-≤ (pdown p) (ldown ps)) (≤-reflexive (eqC (pnrm p) (pnrmL ps)))
```

## 6. 结论

两条合起来：对每个 `t : Tm`，

    nrm t + 1 ≤ 2 · len t        len t ≤ 2 · nrm t + 1

所以两个范数线性互控，常数为 2。这订正了 §83.4 的 `length ≤ 4·N`（在 `t = 0` 处失效，且偏松），并把 §64 归约里“范数可比性”这一条落成机器检验过的事实。

本文件**没有**做的：`≺` 的形式化；`nrm` 满足 BCW Theorem 4 其余假设的验证（§83.5 在纸面上核过）；以及全部输入端内容。

## 7. §83.3 的有限性论证：OT 特有的那部分

§83.3 论证 `N` 是 BCW 意义的范数（`card{β ≺ α : Nβ ≤ n} < ω`）。其中与 `OT` 有关的是两条：**每个直接子项的 `len` 严格更小**，以及**和的分量个数受 `len` 控制**。把这两条证掉，剩下的"有限签名上 `len` 受界的语法树只有有限多棵"是通用事实，与 `OT` 无关，不在本文件内。

先证两个范数的下界。`plen ≥ 1` 用到 `P′` 的项不可能是 `0`——同一处类型层面的约束（§1）。

```agda
mutual
  len≥1 : ∀ t → 1 ≤ len t
  len≥1 zer          = ≤-refl
  len≥1 (prin p)     = plen≥1 p
  len≥1 (sum p q ps) = ≤-trans (plen≥1 p) (≤-trans (m≤m+n _ _) (m≤m+n _ _))

  plen≥1 : ∀ p → 1 ≤ plen p
  plen≥1 M         = ≤-refl
  plen≥1 (phi a b) = ≤-trans (len≥1 a) (m≤m+n _ _)
  plen≥1 (psi a b) = ≤-trans (len≥1 a) (m≤m+n _ _)
  plen≥1 (Om a)    = ≤-trans (len≥1 a) (m≤m+n _ _)
```

直接子项的 `len` 严格更小。这正是 §65.2 命题 U 归纳所依赖的那一步，也是 Definition 3.3 按 `length` 作递归得以良基的理由。

```agda
sub-phiˡ : ∀ a b → len a < plen (phi a b)
sub-phiˡ a b = ≤-trans (≤-reflexive (+-comm 1 (len a))) (+-monoʳ-≤ (len a) (len≥1 b))

sub-phiʳ : ∀ a b → len b < plen (phi a b)
sub-phiʳ a b = ≤-trans (≤-trans (≤-reflexive (+-comm 1 (len b)))
                                (+-monoʳ-≤ (len b) (len≥1 a)))
                       (≤-reflexive (+-comm (len b) (len a)))

sub-psiˡ : ∀ a b → len a < plen (psi a b)
sub-psiˡ = sub-phiˡ

sub-psiʳ : ∀ a b → len b < plen (psi a b)
sub-psiʳ = sub-phiʳ

sub-Om : ∀ a → len a < plen (Om a)
sub-Om a = ≤-trans (≤-reflexive (+-comm 1 (len a))) ≤-refl
```

和的分量个数受 `len` 控制：每个分量的 `plen ≥ 1`，故分量数不超过整项的 `len`。

```agda
plenL≥length : ∀ ps → length ps ≤ plenL ps
plenL≥length []       = ≤-refl
plenL≥length (p ∷ ps) = ≤-trans (≤-reflexive (+-comm 1 (length ps)))
                                (≤-trans (+-monoʳ-≤ (length ps) (plen≥1 p))
                                         (≤-trans (≤-reflexive (+-comm (length ps) (plen p)))
                                                  (+-monoʳ-≤ (plen p) (plenL≥length ps))))

sum-arity : ∀ p q ps → length (p ∷ q ∷ ps) ≤ len (sum p q ps)
sum-arity p q ps =
  +-mono-≤ (+-mono-≤ (plen≥1 p) (plen≥1 q)) (plenL≥length ps)
```

至此 §83.3 的 `OT` 特有部分是机器检验过的：子项的 `len` 严格下降，分量数受 `len` 控制。由此"`len ≤ n` 的项只有有限多"是有限签名上的通用归纳，本文件不涉及。
