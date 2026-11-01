# 提取分支产出的项系统落在 BCW 配方内

[RESEARCH.md](../RESEARCH.md) §114–§115（目标 4）。本文件形式化**提取分支自己产出的**记号系统 `OTˣ`，不是 Setzer 的 `OT`——后者是参考分支的输入，在这里一次也不出现。

**本文件已按 §115、§117 改写两次。** 初版把坍缩函数取成三元的 `ψ^ν_σ`，那是 Arai `OT(Π₃)` 的形状，**过冲到 KPΠ₃**（其序数 `ψ_Ω(ε_{K+1})` 远高于 `(KPM)⁺`）。正确的读出是 Mahlo 度的上界 `m₂(K) = 2`，度只取 `{0,1}`，故坍缩只有两个符号：一元的 `ψ_K` 与二元的 `ψ_σ`。理由见 §115.2。

机器检验的内容：

1. 配方在 `OTˣ` 的签名上展开出的范数，与 **BCW 亲手为 Rathjen 的 `T(M)`（KPM 的记号系统）写下的七条**逐条相同，**连元数都相同**（`bcw1`–`bcw7`）；
2. BCW §4 要求的归一化条件 `N1′ = 1`，以及和符号上的可加性（配方定理的条件 (3)）；
3. Theorem 4 的两条假设（`N0 ≤ Nα`、`N(α+1) ≤ Nα+1`），并检验 `p := N` 合格；
4. 线性界的射程：BCW 比较定理的条件 (6) 在 `p := N` 下的反例；
5. 范数性质的定量形式：`size t ≤ 3 · N t + 1`——有限签名上这直接给出 `card{t : N t ≤ n} < ω`。

**边界**：这里只形式化项语法与范数，**不**涉及 `≺`、`H_a` 闭包归属、良基性。签名的来源是 §115.2 的纸面推理，本文件不重证。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Notation.ExtOT where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-mono-≤; +-comm; +-assoc; +-identityʳ;
         n≤1+n; m≤m+n; m≤n+m)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
```

## 1. 签名从哪里来

Arai Definition 2.2（＝ Definition 5.3 在 `N = 3`）用三元的 `ψ^ν_σ(a)`，其中 `ν = m₂(κ) < m₂(σ)` 是 **Mahlo 度**。度的取值范围由 `m₂(K)` 定：`OT(Π₃)` 取 `m₂(K) = ε_{K+1}`，度是真参数。

§112.2(a) 读出的是 `𝒪♭ ⟺ M ∈ RM₂(RM₂)`——**一次**应用，不是沿序数的迭代。按 Def 2.2 子句 2 逐层算：`Mh₂(0)` 是极限序数，`Mh₂(1) = M₂(Mh₂(0)) = RM₂`，`Mh₂(2) = RM₂(RM₂)`。故 `m₂(K) = 2`，度只取 `{0,1}`，**有限**，于是被吸收成两个函数符号：

| 来源 | 符号 | 元数 |
|---|---|---|
| Buchholz Def 1.2.1 的闭包基 `{0, M}` 与 `+`、`φ`、`Ω` | `zer`、`K`、`sum`、`phi`、`Omg` | — |
| Def 1.2.2 的 `D_κ(α)`，`κ = M` 一支（落点须 `∈ R`） | `psiK` | **一元**（下标固定在 `K`） |
| Def 1.2.2 的 `D_κ(α)`，`κ < M` 一支 | `psi` | 二元 |

**§117.3 去掉了一个冗余常量。** 初版照 Arai Def 2.2 把 `Ω` 取作常量；但 Arai 的系统没有 `Ω_·` 函数，而 `OTˣ` 有（来自 `𝓘`），于是 `Ω = Ω_1 = Omg one`，常量多余。Buchholz 的 Def 1.2.1 本来就只取 `{0, M}` 作基、把 `Ω` 列为闭包运算。去掉后端点范数变成 **7**，与 Setzer 的 `OT` 上同一个项**完全相同**（§83.1 的表）。

七个符号，**有限**——BCW §4 的第一条要求。和是变元数的，分量必属加法主元，故 `0` 不能作分量（与 §83.3 同一理由，这里是类型层面的事实）。

```agda
data Tm : Set
data PTm : Set

data Tm where
  zer  : Tm                           -- 0
  prin : PTm → Tm
  sum  : PTm → PTm → List PTm → Tm    -- (a₀,…,aₙ)，n ≥ 1

data PTm where
  K    : PTm                          -- M，Mahlo 常量
  phi  : Tm → Tm → PTm                -- φ_a b
  Omg  : Tm → PTm                     -- Ω_a      来自 𝓘；Ω = Omg one
  psiK : Tm → PTm                     -- ψ_M(a)   Def 1.2.2 的 κ = M 支
  psi  : Tm → Tm → PTm                -- ψ_σ(a)   Def 1.2.2 的 κ < M 支
```

## 2. 配方的范数

BCW §4 的配方原话：范数取项中**非和函数符号与非零常量的出现次数**。照抄到上面的签名：

```agda
mutual
  N : Tm → ℕ
  N zer          = 0
  N (prin p)     = NP p
  N (sum p q ps) = NP p + NP q + NL ps

  NP : PTm → ℕ
  NP K          = 1
  NP (phi a b)  = 1 + N a + N b
  NP (Omg a)    = 1 + N a
  NP (psiK a)   = 1 + N a
  NP (psi s a)  = 1 + N s + N a

  NL : List PTm → ℕ
  NL []       = 0
  NL (p ∷ ps) = NP p + NL ps
```

## 3. 与 BCW 为 `T(M)` 亲手写的七条对照

BCW 1994 页 283 给 Rathjen 的 `T(M)`（他们称"characteristic for the theory KPM formalizing a recursively Mahlo universe"）写下

> 1. `N0 := 0`  　 2. `NM := 1`  　 3. `N ⊕(α₁,…,αₙ) := Nα₁ + ⋯ + Nαₙ`
> 4. `N ω̄^α := Nα + 1`  　 5. `N φ̄αβ := 1 + Nα + Nβ`
> 6. `N ψκα := 1 + Nκ + Nα`  　 7. `N Zα := Nα + 1`

这七条是**手写的**。下面检验：上一节那个统一的计数规则在 `OTˣ` 上展开，逐条给出同样的值。对应关系：`ω̄^α ↔ φ₀α`（`φ₀β = ω^β`），`Zα ↔ ψ_K(α)`——**注意 `Z` 是一元**，这正是度 1 的坍缩下标固定在 `K` 的结果。

```agda
bcw1 : N zer ≡ 0
bcw1 = refl

bcw2 : NP K ≡ 1
bcw2 = refl

bcw3 : ∀ p q ps → N (sum p q ps) ≡ NP p + NP q + NL ps
bcw3 _ _ _ = refl

bcw4 : ∀ a → NP (phi zer a) ≡ N a + 1
bcw4 a = +-comm 1 (N a)

bcw5 : ∀ a b → NP (phi a b) ≡ 1 + N a + N b
bcw5 _ _ = refl

bcw6 : ∀ s a → NP (psi s a) ≡ 1 + N s + N a
bcw6 _ _ = refl

bcw7 : ∀ a → NP (psiK a) ≡ N a + 1
bcw7 a = +-comm 1 (N a)
```

七条全过，元数全合，且**符号数也对上了**：`0, M, ⊕, φ(含 ω̄^), ψ, Z` 六样加上 `Omg`——若 BCW 的 `Z` 是 `Ω_·`（§117.4 指出这是另一种可能读法），则 `psiK` 归入二元 `ψ` 的 `κ = M` 情形，七对七。

**本文件不声称 `OTˣ ≅ T(M)`**——Rathjen [10] 未取得（§114.8）。声称的是：配方在这个签名上展开，与文献手写的表逐条重合。

## 4. BCW §4 的归一化要求

配方额外要求 `N1′ = 1`，其中 `1′` 是 `0′` 的 `<_T`-后继。在 `OTˣ` 里 `1 = φ₀0 = ω⁰`：

```agda
one : Tm
one = prin (phi zer zer)

N-one : N one ≡ 1
N-one = refl
```

## 5. 和：配方定理的条件 (3)

BCW 那条不提基本列的定理要求 `N(α # β) = Nα + Nβ`。把项与其 Cantor 范式的分量表互换，可加性即随之而来。

```agda
toList : Tm → List PTm
toList zer          = []
toList (prin p)     = p ∷ []
toList (sum p q ps) = p ∷ q ∷ ps

fromList : List PTm → Tm
fromList []           = zer
fromList (p ∷ [])     = prin p
fromList (p ∷ q ∷ ps) = sum p q ps

NL-toList : ∀ t → NL (toList t) ≡ N t
NL-toList zer          = refl
NL-toList (prin p)     = +-identityʳ (NP p)
NL-toList (sum p q ps) = sym (+-assoc (NP p) (NP q) (NL ps))

N-fromList : ∀ xs → N (fromList xs) ≡ NL xs
N-fromList []           = refl
N-fromList (p ∷ [])     = sym (+-identityʳ (NP p))
N-fromList (p ∷ q ∷ ps) = +-assoc (NP p) (NP q) (NL ps)

NL-++ : ∀ xs ys → NL (xs ++ ys) ≡ NL xs + NL ys
NL-++ []       ys = refl
NL-++ (p ∷ xs) ys =
  trans (cong (NP p +_) (NL-++ xs ys)) (sym (+-assoc (NP p) (NL xs) (NL ys)))

infixl 6 _⊕_
_⊕_ : Tm → Tm → Tm
t ⊕ u = fromList (toList t ++ toList u)

⊕-N : ∀ t u → N (t ⊕ u) ≡ N t + N u
⊕-N t u = trans (N-fromList (toList t ++ toList u))
          (trans (NL-++ (toList t) (toList u))
                 (cong₂ _+_ (NL-toList t) (NL-toList u)))
```

后继是在分量表末尾接一个 `1′`：

```agda
suc′ : Tm → Tm
suc′ t = t ⊕ one

N-suc′ : ∀ t → N (suc′ t) ≡ N t + 1
N-suc′ t = ⊕-N t one
```

## 6. Theorem 4 的假设，以及 `p := N` 合格

Theorem 4 要 `N0 ≤ Nα`、`N(α+1) ≤ Nα+1`，以及一个 `p` 满足 `Nα ≤ p(α)+1 ≤ p(α+1)`。

```agda
thm4-N0 : ∀ t → N zer ≤ N t
thm4-N0 _ = z≤n

thm4-suc : ∀ t → N (suc′ t) ≤ N t + 1
thm4-suc t = ≤-reflexive (N-suc′ t)

thm4-pˡ : ∀ t → N t ≤ N t + 1
thm4-pˡ t = m≤m+n (N t) 1

thm4-pʳ : ∀ t → N t + 1 ≤ N (suc′ t)
thm4-pʳ t = ≤-reflexive (sym (N-suc′ t))
```

于是 `λ[n] := max{β ≺ λ : Nβ ≤ Nλ + n}` 在 `OTˣ` 上由 Theorem 4(a) 自动是带范数的 Bachmann 系统——这正是参考分支 §83.6 的那条，现在换成提取分支自己的项系统。

## 7. 线性界够到哪里：BCW 条件 (6) 的反例

BCW 为 `T(M)` 取的基本列是 `α[x]_M := max{β < α : Nβ ≤ 3^(3^(Nα+x+1))}`——**双指数**，不是参考分支 §83.6 用的线性界 `Nλ + n`。差别在哪里，这里检验清楚。

Theorem 4 只要 `Nα ≤ p(α)+1 ≤ p(α+1)`，上一节已验 `p := N` 合格，故**线性界足以给出带范数的 Bachmann 系统**。但 BCW 另有一条不提基本列的比较定理（`Cl(R(τ,N)) = Cl({H^{N,p}_α})`），其条件 (6) 要求 `N(ωᵐ·n) ≤ p(ωᵐ⁺¹ + n)`。取 `p := N`、`m = n = 3` 即失效：

```agda
num : ℕ → Tm
num zero    = zer
num (suc n) = suc′ (num n)

N-num : ∀ n → N (num n) ≡ n
N-num zero    = refl
N-num (suc n) =
  trans (N-suc′ (num n)) (trans (cong (_+ 1) (N-num n)) (+-comm n 1))

ω^_ : Tm → Tm
ω^ a = prin (phi zer a)

N-ω^ : ∀ a → N (ω^ a) ≡ N a + 1
N-ω^ a = +-comm 1 (N a)

rep : ℕ → Tm → Tm
rep zero    t = zer
rep (suc n) t = t ⊕ rep n t

N-rep : ∀ n t → N (rep n t) ≡ n * N t
N-rep zero    t = refl
N-rep (suc n) t = trans (⊕-N t (rep n t)) (cong (N t +_) (N-rep n t))

lhs₆ rhs₆ : ℕ
lhs₆ = N (rep 3 (ω^ (num 3)))     -- ω³·3
rhs₆ = N (ω^ (num 4) ⊕ num 3)     -- ω⁴+3

cond6-lhs : lhs₆ ≡ 12
cond6-lhs = refl

cond6-rhs : rhs₆ ≡ 8
cond6-rhs = refl

cond6-fails : rhs₆ < lhs₆
cond6-fails = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
```

结论：线性界给 C2（正则性）、C3、C4、C7 够用；要 BCW 那条推论的形式（"KPM 的每个可证全函数被某个 `H_α` 支配"，即 C6 的反向），必须换成他们的双指数界。这不推翻 §83.5——那里核的是 Theorem 4 的假设，仍然成立——而是划清它管到哪里。

## 8. 范数性质：项的大小受范数线性控制

"`N` 是范数"即 `card{β ≺ α : Nβ ≤ n} < ω`。有限签名上，它等价于**范数控制项的大小**。常数 `3` 来自最宽的符号（`phi`、`psi`，二元）；初版用三元的 `ψ^ν_σ` 时是 `4`。

```agda
mutual
  size : Tm → ℕ
  size zer          = 1
  size (prin p)     = 1 + sizeP p
  size (sum p q ps) = 1 + sizeP p + sizeP q + sizeL ps

  sizeP : PTm → ℕ
  sizeP K          = 1
  sizeP (phi a b)  = 1 + size a + size b
  sizeP (Omg a)    = 1 + size a
  sizeP (psiK a)   = 1 + size a
  sizeP (psi s a)  = 1 + size s + size a

  sizeL : List PTm → ℕ
  sizeL []       = 0
  sizeL (p ∷ ps) = sizeP p + sizeL ps
```

`size (prin p)` 取 `1 + sizeP p` 而非 `sizeP p`：多计的那个 `1` 使"大小 ≤ n 的项只由大小 ≤ n−1 的部件搭成"，[`ExtSearch`](ExtSearch.lagda.md) 的枚举递归靠它结构递减。这不影响下面的界。

算术骨架。`cast` 把一条 `≤` 沿两端的等式搬运；`e*` 由环解法器给出。

```agda
cast : ∀ {a b c d} → a ≡ c → b ≡ d → c ≤ d → a ≤ b
cast refl refl le = le

e₂ : ∀ x y → 1 + (3 * x + 1) + (3 * y + 1) ≡ 3 * (1 + x + y)
e₂ = solve 2 (λ x y → con 1 :+ (con 3 :* x :+ con 1) :+ (con 3 :* y :+ con 1)
                   := con 3 :* (con 1 :+ x :+ y)) refl

e₁ : ∀ x → 1 + (3 * x + 1) ≡ 2 + 3 * x
e₁ = solve 1 (λ x → con 1 :+ (con 3 :* x :+ con 1) := con 2 :+ con 3 :* x) refl

e₁′ : ∀ x → 3 * (1 + x) ≡ 3 + 3 * x
e₁′ = solve 1 (λ x → con 3 :* (con 1 :+ x) := con 3 :+ con 3 :* x) refl

eL : ∀ x y → 3 * x + 3 * y ≡ 3 * (x + y)
eL = solve 2 (λ x y → con 3 :* x :+ con 3 :* y := con 3 :* (x :+ y)) refl

eS : ∀ x y z → 1 + 3 * x + 3 * y + 3 * z ≡ 3 * (x + y + z) + 1
eS = solve 3 (λ x y z → con 1 :+ con 3 :* x :+ con 3 :* y :+ con 3 :* z
                     := con 3 :* (x :+ y :+ z) :+ con 1) refl

un : ∀ x → 1 + (3 * x + 1) ≤ 3 * (1 + x)
un x = cast (e₁ x) (e₁′ x) (s≤s (s≤s (n≤1+n (3 * x))))
```

主定理，三路互递归：

```agda
mutual
  size≤ : ∀ t → size t ≤ 3 * N t + 1
  size≤ zer          = ≤-refl
  size≤ (prin p)     = cast refl (+-comm (3 * NP p) 1) (s≤s (sizeP≤ p))
  size≤ (sum p q ps) =
    cast refl (sym (eS (NP p) (NP q) (NL ps)))
      (+-mono-≤ (+-mono-≤ (+-mono-≤ (≤-refl {1}) (sizeP≤ p)) (sizeP≤ q)) (sizeL≤ ps))

  sizeP≤ : ∀ p → sizeP p ≤ 3 * NP p
  sizeP≤ K          = s≤s z≤n
  sizeP≤ (phi a b)  = cast refl (sym (e₂ (N a) (N b)))
                        (+-mono-≤ (+-mono-≤ (≤-refl {1}) (size≤ a)) (size≤ b))
  sizeP≤ (psi s a)  = cast refl (sym (e₂ (N s) (N a)))
                        (+-mono-≤ (+-mono-≤ (≤-refl {1}) (size≤ s)) (size≤ a))
  sizeP≤ (psiK a)   = ≤-trans (+-mono-≤ (≤-refl {1}) (size≤ a)) (un (N a))
  sizeP≤ (Omg a)    = ≤-trans (+-mono-≤ (≤-refl {1}) (size≤ a)) (un (N a))

  sizeL≤ : ∀ ps → sizeL ps ≤ 3 * NL ps
  sizeL≤ []       = z≤n
  sizeL≤ (p ∷ ps) = cast refl (sym (eL (NP p) (NL ps)))
                      (+-mono-≤ (sizeP≤ p) (sizeL≤ ps))
```

## 9. 端点

参考分支的端点 `λ_M = ψ_{Ω′₁}Ω′_{M+ω}`（§66）在 `OTˣ` 里写作 `ψ_Ω(Ω_{K+ω})`：

```agda
Om : Tm
Om = prin (Omg one)                              -- Ω = Ω₁

endpoint : Tm
endpoint = prin (psi Om (prin (Omg (sum K (phi zer one) []))))

N-endpoint : N endpoint ≡ 7
N-endpoint = refl
```

Setzer 的 `OT` 上同一个项范数**也是 7**（§83.1 的表）。初版把 `Ω` 取作常量时是 `6`；§117.3 去掉那个冗余后两边完全相同——这是 §114.7 对应表的一次定量确证。`N_M = F_{λ_M}(8)` 里冻结的 `k = 8` 不变。

## 10. 强临界子项 `SC`，以及正则性判定

`≺` 的两样原料在这里先做出来。**第三样不是一个集合而是两个**（§118.2 更正 §116.2）：`SC_a` 管值、`G_a` 管下标，且与 `≺` 互递归——那部分未做。

**`SC(γ)`（强临界子项）** 按 Buchholz 1993 页 2 的四条：`SC(0)=∅`；`SC(γ)={γ}` 当 `γ ∈ SC`；和取各分量之并；`SC(φξη)=SC(ξ)∪SC(η)`。在 `OTˣ` 的签名上，强临界的主元项恰是 `K`、`Omg _`、`psiK _`、`psi _ _`（原文"每个不可数基数强临界"加 Lemma 1.3c "`ψ_κα ∈ SC`"），`phi` 不是——二元 Veblen 到不了 Γ 数。

```agda
mutual
  SC : Tm → List PTm
  SC zer          = []
  SC (prin p)     = SCP p
  SC (sum p q ps) = SCP p ++ SCP q ++ SCL ps

  SCP : PTm → List PTm
  SCP K         = K ∷ []
  SCP (phi a b) = SC a ++ SC b
  SCP (Omg a)   = Omg a ∷ []
  SCP (psiK a)  = psiK a ∷ []
  SCP (psi s a) = psi s a ∷ []

  SCL : List PTm → List PTm
  SCL []       = []
  SCL (p ∷ ps) = SCP p ++ SCL ps

isSC : PTm → Bool
isSC K         = true
isSC (phi _ _) = false
isSC (Omg _)   = true
isSC (psiK _)  = true
isSC (psi _ _) = true
```

`SC` 只吐强临界项：

```agda
mutual
  SC-isSC : ∀ {p} t → p ∈ SC t → isSC p ≡ true
  SC-isSC (prin q)     q∈ = SCP-isSC q q∈
  SC-isSC (sum q r ps) q∈ with ∈-++⁻ (SCP q) q∈
  ... | inj₁ h = SCP-isSC q h
  ... | inj₂ h with ∈-++⁻ (SCP r) h
  ...   | inj₁ h′ = SCP-isSC r h′
  ...   | inj₂ h′ = SCL-isSC ps h′

  SCP-isSC : ∀ {p} q → p ∈ SCP q → isSC p ≡ true
  SCP-isSC K         (here refl) = refl
  SCP-isSC (Omg _)   (here refl) = refl
  SCP-isSC (psiK _)  (here refl) = refl
  SCP-isSC (psi _ _) (here refl) = refl
  SCP-isSC (phi a b) h with ∈-++⁻ (SC a) h
  ... | inj₁ h′ = SC-isSC a h′
  ... | inj₂ h′ = SC-isSC b h′

  SCL-isSC : ∀ {p} ps → p ∈ SCL ps → isSC p ≡ true
  SCL-isSC (q ∷ ps) h with ∈-++⁻ (SCP q) h
  ... | inj₁ h′ = SCP-isSC q h′
  ... | inj₂ h′ = SCL-isSC ps h′
```

并且受 `size` 控制——`K_a` 与 `≺` 的互递归要靠这一条：

```agda
mutual
  SC-size : ∀ {p} t → p ∈ SC t → sizeP p ≤ size t
  SC-size (prin q)     h = ≤-trans (SCP-size q h) (n≤1+n (sizeP q))
  SC-size (sum q r ps) h with ∈-++⁻ (SCP q) h
  ... | inj₁ h′ = ≤-trans (SCP-size q h′)
                    (≤-trans (≤-trans (m≤m+n (sizeP q) (sizeP r))
                                      (m≤m+n (sizeP q + sizeP r) (sizeL ps)))
                             (n≤1+n _))
  ... | inj₂ h′ with ∈-++⁻ (SCP r) h′
  ...   | inj₁ h″ = ≤-trans (SCP-size r h″)
                      (≤-trans (≤-trans (m≤n+m (sizeP r) (sizeP q))
                                        (m≤m+n (sizeP q + sizeP r) (sizeL ps)))
                               (n≤1+n _))
  ...   | inj₂ h″ = ≤-trans (SCL-size ps h″)
                      (≤-trans (m≤n+m (sizeL ps) (sizeP q + sizeP r)) (n≤1+n _))

  SCP-size : ∀ {p} q → p ∈ SCP q → sizeP p ≤ sizeP q
  SCP-size K         (here refl) = ≤-refl
  SCP-size (Omg _)   (here refl) = ≤-refl
  SCP-size (psiK _)  (here refl) = ≤-refl
  SCP-size (psi _ _) (here refl) = ≤-refl
  SCP-size (phi a b) h with ∈-++⁻ (SC a) h
  ... | inj₁ h′ = ≤-trans (SC-size a h′) (≤-trans (m≤m+n (size a) (size b)) (n≤1+n _))
  ... | inj₂ h′ = ≤-trans (SC-size b h′) (≤-trans (m≤n+m (size b) (size a)) (n≤1+n _))

  SCL-size : ∀ {p} ps → p ∈ SCL ps → sizeP p ≤ sizeL ps
  SCL-size (q ∷ ps) h with ∈-++⁻ (SCP q) h
  ... | inj₁ h′ = ≤-trans (SCP-size q h′) (m≤m+n (sizeP q) (sizeL ps))
  ... | inj₂ h′ = ≤-trans (SCL-size ps h′) (m≤n+m (sizeL ps) (sizeP q))
```

**正则性。** Buchholz Def 1.1 的 Remark：`∀κ ∈ R (κ = Ω_κ 或 κ ∈ {Ω_{σ+1} : σ < M})`。加上 Lemma 1.4e（`Ω_{ψ_M α} = ψ_M α`，即 `ψ_M` 的值是 `Ω` 的不动点）与 `M` 自身正则，在 `OTˣ` 上：

```agda
isSuc : Tm → Bool            -- CNF 末项为 1 = φ₀0
isSucL : PTm → List PTm → Bool
isSucL p []       = isOne p  where
                      isOne : PTm → Bool
                      isOne (phi zer zer) = true
                      isOne _             = false
isSucL _ (q ∷ qs) = isSucL q qs

isSuc zer          = false
isSuc (prin p)     = isSucL p []
isSuc (sum p q ps) = isSucL q ps

isReg : PTm → Bool
isReg K         = true       -- M 正则
isReg (psiK _)  = true       -- Lemma 1.4e：Ω 的不动点
isReg (Omg a)   = isSuc a    -- Ω_{σ+1}
isReg (phi _ _) = false
isReg (psi _ _) = false      -- Lemma 1.3b：κ < M ⟹ ψ_κα ∉ R
```

`isReg` 判定 `ψ` 下标的合法性（Def 1.2.1 的 `π ∈ R`）。注意 `isReg (Omg a)` 漏掉了 `a` 为弱不可达的情形——那类 `Ω_a` 在 `OTˣ` 里表示不出来（`Omg` 的下标只由 `+, φ, Ω, ψ` 生成），故不损失。

## 11. 结论

`OTˣ` 的项系统满足 BCW §4 配方的全部**语法**条件：有限签名（七个符号）、零常量 `zer`、序型为各分量之和的变元数 `sum`、归一化 `N1′ = 1`；范数在和上可加、在后继上恰加 `1`、线性控制项的大小，并逐条重现 BCW 手写的七条。由 Theorem 4(a)，相对界 `λ[n] := max{β ≺ λ : Nβ ≤ Nλ + n}` 自动给出带范数的 Bachmann 系统，Lemma 1 随之给出正则性与范数性。

**本文件不覆盖**：`≺` 的定义与原始递归性、`H_a` 闭包归属的可判定性、良基性、以及 `OTˣ` 与 `T(M)`／Setzer `OT` 的同构。前两项是 BCW 配方的另外两条要求，登记在 §115.6。

与 `OTNorm.lagda.md` 的分工：那份处理**参考分支**的两种范数互控（Setzer 的 `length` 对 BCW 的 `N`），是参考分支特有的义务；提取分支只有配方产出的一个范数，那条义务在这里不出现。`NormFGH.lagda.md` 与 `Bachmann.lagda.md` 针对抽象接口，对 `OTˣ` 同样适用。
