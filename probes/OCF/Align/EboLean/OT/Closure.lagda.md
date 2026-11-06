# 闭包与合式性：Setzer [Se98] Definitions 2.6–2.9

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.Closure` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

`G_π(a)`（Def 2.7）、`Cr′(a)`（Def 2.8a）、`C̃_a(b)`（Def 2.8b）、`OT`（Def 2.9）。全部可判定；`G` 对项结构递归，其中的比较调用带典范燃料的 `lt`——**`≺′` 本身不依赖 `G`**，所以这里没有互递归。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module OCF.Align.EboLean.OT.Closure where

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Bool.ListAction using (all)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## 1. 有限集上的 ⪯′、≺′（Def 2.6）

`M ≺′ M′ :⟺ ∀x ∈ M ∃y ∈ M′. x ≺′ y`；对单点 `M′ = {b}` 即 `∀x ∈ M. x ≺′ b`。

```agda
allLt : List Tm → Tm → Bool             -- M ≺′ {b}
allLt xs b = all (λ x → lt x b) xs
```

## 2. `G_π(a)`（Def 2.7）

按 `length(a)` 递归的有限集。(G4) 对 `ψ_κ b` 分三支：

- `{b} ∪ G_π(κ) ∪ G_π(b)`，若 `π ⪯′ κ ≠ I` 或 `κ = I ∧ (π ⪯′ ψ_I b ∨ π = I)`；
- `G_π(κ)`，若 `κ ≺′ π = I`；
- `∅`，若 `κ ≺′ π ≠ I` 或 `κ = I ∧ ψ_I b ≺′ π ≺′ I`。

三支按 κ 的形状与 π 的形状展开如下。κ = I、π = Ω′_a 且 `π ⪯′ ψ_I b` 不成立时，无论 π ≺′ I 与否都落到 ∅（第三支两个析取项各盖一半）。

```agda
mutual
  G : Reg → Tm → List Tm
  G π zer     = []
  G π (a ▹ p) = G π a ++ GP π p                                      -- (G1)(G2)

  GP : Reg → PTm → List Tm
  GP π (phi a b)      = G π a ++ G π b                              -- (G3)
  GP π (Om a)         = G π a                                        -- (G5)
  GP π I              = []                                           -- (G6)
  GP IR     (psi IR b)     = b ∷ G IR b                              -- (G4) κ = I = π
  GP (ΩR a) (psi IR b)     = if le ⟨ Om a ⟩ ⟨ psi IR b ⟩             -- (G4) κ = I ≠ π
                               then b ∷ G (ΩR a) b else []
  GP π      (psi (ΩR c) b) =                                         -- (G4) κ = Ω′_c ≠ I
    if le (regTm π) ⟨ Om c ⟩
      then b ∷ (G π c ++ G π b)
      else (if isI π then G π c else [])
```

(G5) 给 `G_π(Ω′_c) = G_π(c)`，所以上面 `G π ⟨ Om c ⟩` 直接写成 `G π c`（结构递归）。

## 3. `Cr′(a)` 与 `C̃_a(b)`（Def 2.8）

`a`-临界项：`0`、和 ∉ Cr′(a)；`φ′_b c ∈ Cr′(a) ⟺ a ≺′ b`；`b ∈ G′ ⟹ (b ∈ Cr′(a) ⟺ a ≺′ b)`。
`C̃_a(b) := {c ∈ T′ | G_a(c) ≺′ b}`——`a` 是 R′ 的元素。

```agda
inCr : Tm → Tm → Bool                   -- c ∈ Cr′(a)
inCr a (zer ▹ phi b c) = lt a b
inCr a (zer ▹ p)       = lt a ⟨ p ⟩       -- p ∈ G′
inCr a _               = false

inC̃ : Reg → Tm → Tm → Bool             -- c ∈ C̃_a(b)
inC̃ a b c = allLt (G a c) b
```

## 4. `OT`（Def 2.9）

- (OT1) `0 ∈ OT`
- (OT2) `n > 0`，`aᵢ ∈ OT ∩ A′`，`aₙ ⪯′ aₙ₋₁ ⪯′ ⋯ ⪯′ a₀` ⟹ `(a₀,…,aₙ) ∈ OT`
- (OT3) `a, b ∈ OT`，`b ∉ Cr′(a)`，`¬(b = 0 ∧ a ∈ G′)` ⟹ `φ′_a b ∈ OT`
- (OT4) `b ∈ OT`，`π ∈ R′ ∩ OT`，`G_π(b) ≺′ b` ⟹ `ψ_π b ∈ OT`
- (OT5) `a ∈ OT ∖ (Fi′ ∪ {0})` ⟹ `Ω′_a ∈ OT`
- (OT6) `I ∈ OT`

```agda
mutual
  isOT : Tm → Bool
  isOT zer         = true
  isOT (zer ▹ p)   = isOTP p
  isOT (a ▹ q ▹ p) = isOT (a ▹ q) ∧ isOTP p ∧ le ⟨ p ⟩ ⟨ q ⟩          -- (OT2)

  isOTP : PTm → Bool
  isOTP (phi a b) = isOT a ∧ isOT b ∧ not (inCr a b) ∧ not (isZero b ∧ isGT a)
  isOTP (psi π b) = isOT b ∧ isOTR π ∧ isRR π ∧ allLt (G π b) b
  isOTP (Om a)    = isOT a ∧ not (isFiT a) ∧ not (isZero a)
  isOTP I         = true

  isOTR : Reg → Bool                    -- π ∈ OT
  isOTR (ΩR a) = isOT a ∧ not (isFiT a) ∧ not (isZero a)
  isOTR IR     = true
```

`OT ⊆ T′`：`isOTP` 的各支已含 (T′4)(T′5) 的侧条件（ψ 的下标 ∈ R′、Ω′ 的下标 ≠ 0）。

作为谓词的 `OT`（同 `≺` 的理由，包成记录）：

```agda
record OT (x : Tm) : Set where
  constructor ot!
  field isOT≡ : isOT x ≡ true
open OT public
```

## 5. 算例

```agda

```
