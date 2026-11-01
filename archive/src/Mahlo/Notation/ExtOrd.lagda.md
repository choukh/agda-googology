# `OTˣ` 上的序 `≺`

[RESEARCH.md](../RESEARCH.md) §120。本文件给出提取分支项系统 `OTˣ` 上的比较关系，**全函数、可判定、无 postulate／无洞／无终止绕过**。

**关键简化（§120.1）**：比较规则只用到 `sc_κ`，而 `sc_κ` 非空仅当 `κ = M`；此时判据 `ψ_λ d ≺ M` 由 Lemma 1.3a **恒真**，于是 `SC_M` 是**纯结构**函数。§119.4 卡住的那个"`SC/G` 与 `≺` 互递归"根本不出现——那是我把well-formedness 用的 `C̃_κ(b)` 和比较用的 `sc_κ` 混为一谈。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Notation.ExtOrd where

open import Mahlo.Notation.ExtOT

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool.Base
  using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Bool.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Bool.ListAction using (any; all)
open import Relation.Nullary.Decidable.Core using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## 1. `SC_M`：纯结构

Buchholz 页 2 的 `SC(γ)` 四条，相对 `κ = M` 展开。`ψ_λ d ≺ M` 恒真（Lemma 1.3a：`ψ_λ d < λ ≤ M`），故 ψ-项一律取单点集，不需要任何比较。

```agda
mutual
  scM : Tm → List PTm
  scM zer          = []
  scM (prin p)     = scMP p
  scM (sum p q ps) = scMP p ++ scMP q ++ scML ps

  scMP : PTm → List PTm
  scMP K         = []
  scMP (phi a b) = scM a ++ scM b
  scMP (Omg a)   = scM a
  scMP (psiK a)  = psiK a ∷ []
  scMP (psi s a) = psi s a ∷ []

  scML : List PTm → List PTm
  scML []       = []
  scML (p ∷ ps) = scMP p ++ scML ps
```

`sc_κ(b)`：仅 `κ = M` 时非空。`isFix` 判 `I′`（`Ω` 的不动点：`M` 与 `ψ_M d`），`mkP` 按下标是否为 `M` 选构造子。

```agda
isM : Tm → Bool
isM (prin K) = true
isM _        = false

isFix : Tm → Bool
isFix (prin K)        = true
isFix (prin (psiK _)) = true
isFix _               = false

mkP : Tm → Tm → PTm
mkP (prin K) a = psiK a
mkP s        a = psi s a

scOf : Tm → Tm → List PTm
scOf κ b = if isM κ then scM b else []
```

## 2. 比较

燃料索引，结构递归。每个递归调用都传 `n < suc n`，故 Agda 的终止检查直接通过——不用良基递归。

```agda
mutual
  ltT : ℕ → Tm → Tm → Bool
  ltT zero    _ _ = false
  ltT (suc n) s t = ltL n (toList s) (toList t)

  ltL : ℕ → List PTm → List PTm → Bool
  ltL _       []       []       = false
  ltL _       []       (_ ∷ _)  = true
  ltL _       (_ ∷ _)  []       = false
  ltL zero    (_ ∷ _)  (_ ∷ _)  = false
  ltL (suc n) (p ∷ ps) (q ∷ qs) =
    if ltP n p q then true else (if ltP n q p then false else ltL n ps qs)

  ltP : ℕ → PTm → PTm → Bool
  ltP zero _ _ = false

  -- M 对各项
  ltP (suc n) K K           = false
  ltP (suc n) K (phi c d)   = not (ltL n (toList c) (K ∷ []) ∧ ltL n (toList d) (K ∷ []))
  ltP (suc n) K (Omg c)     = ltL n (K ∷ []) (toList c)          -- Ω_c ≺ M ⟺ c ≺ M
  ltP (suc n) K (psiK _)    = false                              -- ψ_M b ≺ M
  ltP (suc n) K (psi _ _)   = false

  -- φ 对各项：(≺′4) φab ≺ γ ⟺ a ≺ γ ∧ b ≺ γ（γ 强临界）
  ltP (suc n) (phi a b) K         = ltL n (toList a) (K ∷ []) ∧ ltL n (toList b) (K ∷ [])
  ltP (suc n) (phi a b) (Omg c)   = ltL n (toList a) (Omg c ∷ []) ∧ ltL n (toList b) (Omg c ∷ [])
  ltP (suc n) (phi a b) (psiK d)  = ltL n (toList a) (psiK d ∷ []) ∧ ltL n (toList b) (psiK d ∷ [])
  ltP (suc n) (phi a b) (psi t d) = ltL n (toList a) (psi t d ∷ []) ∧ ltL n (toList b) (psi t d ∷ [])
  ltP (suc n) (phi a b) (phi c d) =                              -- (≺′3) Veblen
       (ltT n a c ∧ ltL n (toList b) (phi c d ∷ []))
    ∨ (not (ltT n a c) ∧ not (ltT n c a) ∧ ltT n b d)
    ∨ (ltT n c a ∧ not (ltL n (toList d) (phi a b ∷ [])))

  -- Ω_a 对各项
  ltP (suc n) (Omg a) K         = ltL n (toList a) (K ∷ [])      -- (≺′10)
  ltP (suc n) (Omg a) (Omg c)   = ltT n a c                      -- (≺′9)
  ltP (suc n) (Omg a) (phi c d) = not (ltL n (toList c) (Omg a ∷ []) ∧ ltL n (toList d) (Omg a ∷ []))
  ltP (suc n) (Omg a) (psiK b)  = ltL n (toList a) (psiK b ∷ [])  -- (≺′7) 取反
  ltP (suc n) (Omg a) (psi t b) = if isFix t
                                    then ltL n (toList a) (psi t b ∷ [])
                                    else ltL n (Omg a ∷ []) (toList t)

  -- ψ_M a 对非 ψ 项
  ltP (suc n) (psiK a) K         = true                          -- (≺′8)
  ltP (suc n) (psiK a) (phi c d) = not (ltL n (toList c) (psiK a ∷ []) ∧ ltL n (toList d) (psiK a ∷ []))
  ltP (suc n) (psiK a) (Omg c)   = not (ltL n (toList c) (psiK a ∷ []))   -- (≺′7) ψ_M a ⪯ c
  -- ψ_σ a 对非 ψ 项
  ltP (suc n) (psi s a) K         = true
  ltP (suc n) (psi s a) (phi c d) = not (ltL n (toList c) (psi s a ∷ []) ∧ ltL n (toList d) (psi s a ∷ []))
  ltP (suc n) (psi s a) (Omg c)   = if isFix s
                                      then not (ltL n (toList c) (psi s a ∷ []))   -- (≺′7)
                                      else not (ltL n (Omg c ∷ []) (toList s))     -- (≺′6) σ ⪯ Ω_c

  -- ψ 对 ψ：(≺′5)，四种组合统一
  ltP (suc n) (psiK a)  (psiK b)  = lt5 n (prin K) a (prin K) b
  ltP (suc n) (psiK a)  (psi t b) = lt5 n (prin K) a t        b
  ltP (suc n) (psi s a) (psiK b)  = lt5 n s        a (prin K) b
  ltP (suc n) (psi s a) (psi t b) = lt5 n s        a t        b

  lt5 : ℕ → Tm → Tm → Tm → Tm → Bool
  lt5 zero    _ _ _ _ = false
  lt5 (suc m) π a κ b =
       not (ltL m (mkP κ b ∷ []) (toList π))                        -- (i)  π ⪯ ψ_κ b
    ∨  any (λ x → not (ltP m x (mkP π a))) (scOf κ b)               -- (ii) ψ_π a ⪯ sc_κ(b)
    ∨  (eqπκ ∧ ltT m a b ∧ allsc)                                   -- (iii)
    ∨  (ltL m (mkP π a ∷ []) (toList κ) ∧ ltT m κ π ∧ allsc)        -- (iv)
    where
      eqπκ : Bool
      eqπκ = not (ltT m π κ) ∧ not (ltT m κ π)
      allsc : Bool
      allsc = all (λ x → ltP m x (mkP κ b)) (scOf π a)
```

四条析取项就是 §118.1 转写的 (≺′5)。其中 (i) 是 §117.7 本项目**自行推出**的 (2a)，(ii) 的理由在 §119.2 推出，(iii) 的侧条件在 `OT` 上自动成立（§119.2），(iv) 是 §117.7 情形 3 的判据形式。

## 3. `≺` 与可判定性

燃料取 `8·(size s + size t) + 16`：每层比较至多消耗常数级燃料，而 `size` 已由 [`ExtOT`](ExtOT.lagda.md) §8 证明受范数线性控制。

```agda
fuel : Tm → Tm → ℕ
fuel s t = 8 * (size s + size t) + 16

_≺_ : Tm → Tm → Set
s ≺ t = ltT (fuel s t) s t ≡ true

_≺?_ : ∀ s t → Dec (s ≺ t)
s ≺? t = ltT (fuel s t) s t ≟ true
```

## 4. 算例

全部 `refl`——由机器求值确认，不是手算。

```agda
-- 记号
zero′ one′ ω′ ε₀′ Ω′ M′ : Tm
zero′ = zer
one′  = one                                   -- 1 = φ₀0
ω′    = prin (phi zer one)                    -- ω = φ₀1
ε₀′   = prin (phi one zer)                    -- ε₀ = φ₁0
Ω′    = prin (Omg one)                        -- Ω = Ω₁
M′    = prin K                                -- M

Ω_M+1 : Tm
Ω_M+1 = prin (Omg (sum K (phi zer zer) []))   -- Ω_{M+1}

ψM0 ψΩ0 : Tm
ψM0 = prin (psiK zer)                         -- ψ_M 0
ψΩ0 = prin (psi Ω′ zer)                       -- ψ_Ω 0

_ : zero′ ≺ one′
_ = refl

_ : one′ ≺ ω′
_ = refl

_ : ω′ ≺ ε₀′
_ = refl

_ : ε₀′ ≺ Ω′
_ = refl

_ : Ω′ ≺ M′
_ = refl

_ : M′ ≺ Ω_M+1
_ = refl

_ : ψM0 ≺ M′
_ = refl

_ : Ω′ ≺ ψM0                                  -- ψ_M 0 是 M 之下的正则，在 Ω 之上
_ = refl

_ : ψΩ0 ≺ Ω′
_ = refl

_ : ψΩ0 ≺ ψM0
_ = refl

-- 端点的内部结构
_ : Ω_M+1 ≺ prin (Omg (sum K (phi zer one) []))     -- Ω_{M+1} ≺ Ω_{M+ω}
_ = refl

_ : endpoint ≺ Ω′                                    -- ψ_{Ω₁}(Ω_{M+ω}) ≺ Ω₁
_ = refl

-- 反向不成立
_ : ltT (fuel one′ zero′) one′ zero′ ≡ false
_ = refl

_ : ltT (fuel M′ Ω′) M′ Ω′ ≡ false
_ = refl

-- 加法范式：字典序
_ : ω′ ≺ (prin (phi zer one) ⊕ one′)                 -- ω ≺ ω+1
_ = refl

_ : (prin (phi zer one) ⊕ one′) ≺ ε₀′                -- ω+1 ≺ ε₀
_ = refl
```

## 5. 接上 `ExtSearch`：`λ[n]` 完全可算

[`ExtSearch`](ExtSearch.lagda.md) §6 把候选表做成了以「可判定谓词」为参数的模块，参数现在有了。

```agda
open import Mahlo.Notation.ExtSearch using (cands; cands-complete)
open import Data.Nat.Base using (_≤_)
open import Data.List.Membership.Propositional using (_∈_)

-- λ[n] 的完整候选表：一个具体的、可计算的有限表
fsCands : Tm → ℕ → List Tm
fsCands lam n = cands (λ t → t ≺? lam) lam n

-- 不漏：凡 ≺ λ 且范数合格的项都在表里
fsCands-complete : ∀ lam n t → t ≺ lam → N t ≤ N lam + n → t ∈ fsCands lam n
fsCands-complete lam n t p le = cands-complete (λ u → u ≺? lam) {lam} {n} t p le
```

`λ[n]` 即在 `fsCands lam n` 上取 `≺`-极大。表有限（`ExtSearch` §4 的枚举完备性）、不漏（上式）、不多（`filter` 的定义），搜索界 `3·(N λ + n) + 1` 由范数给出。**CONTRACT §2 的「输出总可计算的 λ[n]」至此闭合。**

## 6. 结论与边界

**已给出**：`OTˣ` 上的全函数、可判定的 `≺`，配上 [`ExtSearch`](ExtSearch.lagda.md) 的 `cands`，`λ[n]` 完全可算——CONTRACT §2 的"总可计算的 λ[n]"至此闭合。

**未证**：

1. **线序**（自反、传递、三分）。Setzer 对同族的 `≺′` 的 Lemma 3.4 原话是 "easy, but very long"；本项目未做。
2. **燃料充分性**：`ltT n s t` 对一切 `n ≥ fuel s t` 给同一结果。所有递归调用都严格减小 `size s + size t`（`ExtSearch` §7 已机检十条），故 `8·size+16` 充裕，但**未形式化**。
3. **合式性 `OT ⊆ OTˣ`**：Setzer (OT1)–(OT6) 的对应物。比较规则对全体 `OTˣ` 项有定义，落在合式子集上才与序数一致。合式判定要 `C̃_κ(b)`，那里 `SC_κ`／`G_κ` 与 `≺` 确实互递归（§119.1 推出了分叉判据），**未做**。
4. `ltP` 里标"不可达"的分支（`psiView` 为 `nothing` 的 ψ 情形）已按构造子穷举消除，无需断言。

**来源与 E**：(≺′3)–(≺′10) 的形状取自 §118.1 转写的 Setzer Definition 3.3——它是 ψ-坍缩族上**类一致**的比较装置，CONTRACT §1 允许"预先固定适用于所支持规则类别的提取方法"。签名、参数、端点仍全部由规则读出（§111、§112、§115.2）。(≺′5) 的 (i) 与 (iii) 的侧条件本项目独立推出过（§117.7、§119.2），推导在核对之前。详见 §120.3。
