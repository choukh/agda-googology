# OT_I 的序 ≺′：Setzer [Se98] Definition 2.3

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.Order` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

(≺′1)–(≺′11) 逐字转写。原文按 `length(a) + length(b)` 递归；这里用燃料索引的结构递归（与 [../Notation/ExtOrd](../Notation/ExtOrd.lagda.md) 同法），每个递归调用传 `n < suc n`，Agda 直接通过终止检查。燃料充分性（`n ≥ fuel a b` 时结果稳定）与线序（Lemma 2.4，原文"easy, but tedious"）是 [../ROADMAP.md](../ROADMAP.md) 的 P1，本文件不证。

原文 (≺′11)「其余情形 a ≺′ b :⟺ ¬(b ⪯′ a)」：这里把它**内联**——反向那一对落在 (≺′3)–(≺′10) 的哪条显式子句里，就把那条子句的否定直接写出（形状不同，等号不会成立）。这样每次递归调用都严格减小 `length(a) + length(b)`（原文按此递归；若照抄成 `not (ltP n q p)`，交换后的一对度量不减，燃料充分性就要多绕一步）。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module OCF.Align.EboLean.OT.Order where

open import OCF.Align.EboLean.OT.Syntax

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Bool.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Nullary.Decidable.Core using (Dec; map′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## 1. 比较

`ltT` 比较项（经首分量在前的分量表），`ltL` 是 (≺′2) 的字典序，`ltP` 是主元项之间的 (≺′3)–(≺′11)。辅助：`leT`（⪯′）、`ltTP`／`ltPT`（项对主元／主元对项）。

```agda
isI notI : Reg → Bool
isI IR = true
isI _  = false
notI r = not (isI r)

mutual
  ltT : ℕ → Tm → Tm → Bool
  ltT zero    _ _ = false
  ltT (suc n) s t = ltL n (toList s) (toList t)

  -- (≺′1) 0 ≺′ c ⟺ c ≠ 0；(≺′2) 字典序：相等分量跳过，真前缀者小
  ltL : ℕ → List PTm → List PTm → Bool
  ltL _       []       []       = false
  ltL _       []       (_ ∷ _)  = true
  ltL _       (_ ∷ _)  []       = false
  ltL zero    (_ ∷ _)  (_ ∷ _)  = false
  ltL (suc n) (p ∷ ps) (q ∷ qs) =
    if eqP p q then ltL n ps qs else ltP n p q

  leT : ℕ → Tm → Tm → Bool             -- a ⪯′ b
  leT n s t = ltT n s t ∨ eqT s t

  ltTP : ℕ → Tm → PTm → Bool            -- 项 ≺′ 主元
  ltTP n t p = ltL n (toList t) (p ∷ [])

  ltPT : ℕ → PTm → Tm → Bool            -- 主元 ≺′ 项
  ltPT n p t = ltL n (p ∷ []) (toList t)

  lePT : ℕ → PTm → Tm → Bool            -- 主元 ⪯′ 项
  lePT n p t = ltPT n p t ∨ eqT ⟨ p ⟩ t

  ltP : ℕ → PTm → PTm → Bool
  ltP zero _ _ = false

  -- (≺′3) Veblen：(a≺c ∧ b≺φ′_c d) ∨ (a=c ∧ b≺d) ∨ (c≺a ∧ φ′_a b ⪯ d)
  ltP (suc n) (phi a b) (phi c d) =
       (ltT n a c ∧ ltTP n b (phi c d))
    ∨ (eqT a c ∧ ltT n b d)
    ∨ (ltT n c a ∧ lePT n (phi a b) d)

  -- (≺′4) φ′_a b ≺′ c（c ∈ G′）⟺ max{a,b} ≺′ c ⟺ a ≺′ c ∧ b ≺′ c
  ltP (suc n) (phi a b) c = ltTP n a c ∧ ltTP n b c

  -- (≺′5) ψ 对 ψ
  ltP (suc n) (psi π b) (psi κ d) =
       (eqR π κ ∧ ltT n b d)
    ∨ (notI π ∧ notI κ ∧ ltT n (regTm π) (regTm κ))
    ∨ (isI π ∧ notI κ ∧ ltP n (psi π b) (regP κ))
    ∨ (notI π ∧ isI κ ∧ ltTP n (regTm π) (psi κ d))

  -- (≺′6) I ≠ π ∈ R′，κ ∈ Car′：ψ_π b ≺′ κ ⟺ π ⪯′ κ
  -- (≺′7) ψ_I b ≺′ Ω′_c ⟺ ψ_I b ⪯′ c
  ltP (suc n) (psi (ΩR a) b) (Om c) = leT n ⟨ Om a ⟩ ⟨ Om c ⟩
  ltP (suc n) (psi IR b)     (Om c) = lePT n (psi IR b) c
  -- (≺′6) 对 κ = I；(≺′8) ψ_I b ≺′ I
  ltP (suc n) (psi (ΩR a) b) I      = leT n ⟨ Om a ⟩ ⟨ I ⟩
  ltP (suc n) (psi IR b)     I      = true
  -- (≺′11) ψ 对 φ：¬(φ′_c d ⪯′ ψ_π b) = ¬(c ≺′ ψ_π b ∧ d ≺′ ψ_π b)（经 (≺′4)）
  ltP (suc n) (psi π b) (phi c d)   = not (ltTP n c (psi π b) ∧ ltTP n d (psi π b))

  -- (≺′9) (≺′10)
  ltP (suc n) (Om a) (Om c) = ltT n a c
  ltP (suc n) (Om a) I      = ltT n a ⟨ I ⟩
  -- (≺′11) Ω′_a 对 φ：¬(c ≺′ Ω′_a ∧ d ≺′ Ω′_a)；Ω′_a 对 ψ_κ d：¬(ψ_κ d ≺′ Ω′_a)，经 (≺′6)(≺′7)
  ltP (suc n) (Om a) (phi c d)      = not (ltTP n c (Om a) ∧ ltTP n d (Om a))
  ltP (suc n) (Om a) (psi (ΩR z) d) = not (leT n ⟨ Om z ⟩ ⟨ Om a ⟩)
  ltP (suc n) (Om a) (psi IR d)     = not (lePT n (psi IR d) a)

  -- I 对各项：(≺′11)，经 (≺′4)(≺′6)(≺′8)(≺′10)
  ltP (suc n) I I              = false
  ltP (suc n) I (phi c d)      = not (ltTP n c I ∧ ltTP n d I)
  ltP (suc n) I (psi (ΩR z) d) = not (leT n ⟨ Om z ⟩ ⟨ I ⟩)
  ltP (suc n) I (psi IR d)     = false
  ltP (suc n) I (Om c)         = not (ltT n c ⟨ I ⟩)
```

(≺′5) 的第三支「π = I ≠ κ ∧ ψ_π b ≺′ κ」里 κ 是 Ω′_c，比较落到 (≺′7)；第四支「π ≠ κ = I ∧ π ≺′ ψ_κ d」落到 (≺′11) 的 Ω′ 对 ψ，再到 (≺′7)。

## 2. `≺′` 与可判定性

```agda
fuel : Tm → Tm → ℕ
fuel s t = 8 * (size s + size t) + 16

lt : Tm → Tm → Bool                      -- 带典范燃料的比较
lt s t = ltT (fuel s t) s t

le : Tm → Tm → Bool
le s t = lt s t ∨ eqT s t


infix 4 _≺_ _⪯_

record _≺_ (s t : Tm) : Set where
  constructor lt!
  field lt≡ : lt s t ≡ true
open _≺_ public

record _⪯_ (s t : Tm) : Set where
  constructor le!
  field le≡ : le s t ≡ true
open _⪯_ public

```

`≺`、`⪯` 包成单字段记录而不是直接写 `lt s t ≡ true`：记录是刚性的类型构造子，从 `x ≺ a` 的证明能唯一推出隐参 `x`；裸的 `ltT (fuel x a) x a ≡ true` 会先归约，统一失败。

## 3. 算例（全部机器求值）

```agda

```
