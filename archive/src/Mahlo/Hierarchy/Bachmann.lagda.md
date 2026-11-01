# Bachmann 性质：BCW Lemma 1(a) 的形式化

[RESEARCH.md](../RESEARCH.md) §84.1 指出 Bachmann 性质 (B2) 不在 [NormFGH.lagda.md](NormFGH.lagda.md) 的覆盖范围内——它不是 `FSNorm` 公理的推论，而要由 (B3)+(B4) 推出。本文件补上这一步，即 [Buchholz–Cichon–Weiermann 1994](https://epub.ub.uni-muenchen.de/3849/1/16.pdf) 的 Lemma 1(a)。

**顺带记下一件事**：这条证明**需要序的三分法**。本项目 §57 的卖点是"计算 `λ[n]` 与 `F` 不需要判定零／后继／极限"，那一条仍然成立；但**证明该基本列是 Bachmann 系统**要对 `β[0]` 与 `α[n]` 作三分。所以无三分性是**计算**层面的，不是**验证**层面的。这与本仓库其他路线撞过的 BoundedTrich 墙不冲突——那堵墙挡的是定义，不是元层面的证明——但不能把"不需要三分"说得比实际更宽。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Hierarchy.Bachmann where

open import Data.Nat.Base using (ℕ; suc; _+_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; n≮n; _≤?_; _<?_; ≰⇒>; ≮⇒≥; +-monoˡ-≤)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary.Decidable.Core using (yes; no)
```

## 1. 接口

只取 BCW §1 定义里本条证明用到的部分：序、范数、基本列指派、(B3)、(B4)，以及序的传递性与三分法。`Lim` 是极限谓词，不要求可判定——它只作为 (B4) 的前提出现。

```agda
record BSys : Set₁ where
  field
    Car   : Set
    _⊏_   : Car → Car → Set
    N     : Car → ℕ
    fs    : Car → ℕ → Car
    Lim   : Car → Set

    ⊏-trans : ∀ {x y z} → x ⊏ y → y ⊏ z → x ⊏ z
    ⊏-tri   : ∀ x y → x ⊏ y ⊎ x ≡ y ⊎ y ⊏ x

    -- (B3)：α[n] ⊏ β ⊏ α ⟹ N α[n] < N β
    B3 : ∀ {α β n} → fs α n ⊏ β → β ⊏ α → N (fs α n) < N β
    -- (B4)：β 为极限 ⟹ N β ≤ suc (N β[0])
    B4 : ∀ {β} → Lim β → N β ≤ suc (N (fs β 0))
```

## 2. Lemma 1(a) 的极限情形

`α[n] ⊑ β[0]`，其中 `⊑` 写成 `≡ ⊎ ⊏`。非极限情形由 (B1) 直接给出（`(γ+1)[0] = γ`，而 `α[n] ⊏ γ+1` 即 `α[n] ⊑ γ`），不需要本引理，故不在接口内。

```agda
module _ (S : BSys) where
  open BSys S

  B2-lim : ∀ {α β n} → Lim β → fs α n ⊏ β → β ⊏ α →
           (fs α n ≡ fs β 0) ⊎ (fs α n ⊏ fs β 0)
  B2-lim {α} {β} {n} limβ αn⊏β β⊏α with ⊏-tri (fs β 0) (fs α n)
  ... | inj₂ (inj₁ e)  = inj₁ (sym e)
  ... | inj₂ (inj₂ p)  = inj₂ p
  ... | inj₁ β0⊏αn     = ⊥-elim (n≮n (N (fs α n)) absurd)
    where
    -- (B3) 用于 β：β[0] ⊏ α[n] ⊏ β
    step₁ : N (fs β 0) < N (fs α n)
    step₁ = B3 β0⊏αn αn⊏β
    -- (B4) 用于 β，再接上 step₁
    step₂ : N β ≤ N (fs α n)
    step₂ = ≤-trans (B4 limβ) step₁
    -- (B3) 用于 α：α[n] ⊏ β ⊏ α
    step₃ : N (fs α n) < N β
    step₃ = B3 αn⊏β β⊏α
    absurd : N (fs α n) < N (fs α n)
    absurd = ≤-trans step₃ step₂
```

## 3. 说明

证明逐字跟随 BCW Lemma 1(a)：设 `β[0] ⊏ α[n]`，则由 (B3)（用于 `β`）得 `N β[0] < N α[n]`，由 (B4) 得 `N β ≤ N β[0] + 1 ≤ N α[n]`，而 (B3)（用于 `α`）给 `N α[n] < N β`，矛盾。

**三分法是必需的**：结论 `α[n] ⊑ β[0]` 只能通过排除 `β[0] ⊏ α[n]` 得到，而排除需要先知道三种情形之一成立。对 `OT` 这不成问题（`≺` 原始递归可判定，§65.1），但它说明"无三分"这一好处只在计算层。

本文件**没有**做的：从 Cichon 的定义推出 (B3)、(B4)（那是 BCW Theorem 4(a)，依赖 `bud` 的具体形状）；非极限情形（由 (B1) 平凡）；以及 `OT` 上的实例化。

## 4. 由 Cichon 的定义推出 (B3)

§3 把 (B2) 归约到 (B3)+(B4)。本节再往回推一步：(B3) 由 Cichon 的极大性定义直接得到，**不需要任何序数结构**（不需要后继、极限、良基性），只要序的反自反与反对称，加上 `ℕ` 上 `≤` 的可判定性。

接口即 [BCW 1994](https://epub.ub.uni-muenchen.de/3849/1/16.pdf) Theorem 4 的定义 `α[n] := max{β ⊏ α : N β ≤ p(α+n)}` 拆成三条：`fs α n ⊏ α`、`N (fs α n) ≤ p α n`、以及极大性。

```agda
record CichonFS : Set₁ where
  field
    Car : Set
    _⊏_ : Car → Car → Set
    N   : Car → ℕ
    p   : Car → ℕ → ℕ
    fs  : Car → ℕ → Car

    ⊏-irrefl : ∀ {x} → x ⊏ x → ⊥
    ⊏-asym   : ∀ {x y} → x ⊏ y → y ⊏ x → ⊥

    fs-⊏   : ∀ {α n} → fs α n ⊏ α
    fs-N   : ∀ {α n} → N (fs α n) ≤ p α n
    fs-max : ∀ {α n β} → β ⊏ α → N β ≤ p α n → (β ≡ fs α n) ⊎ (β ⊏ fs α n)

module _ (C : CichonFS) where
  open CichonFS C

  B3-from-max : ∀ {α β n} → fs α n ⊏ β → β ⊏ α → N (fs α n) < N β
  B3-from-max {α} {β} {n} αn⊏β β⊏α with N β ≤? p α n
  ... | no  ¬le = ≤-trans (s≤s fs-N) (≰⇒> ¬le)
  ... | yes le  with fs-max β⊏α le
  ...   | inj₁ e   = ⊥-elim (⊏-irrefl (subst (λ z → fs α n ⊏ z) e αn⊏β))
  ...   | inj₂ q   = ⊥-elim (⊏-asym αn⊏β q)
```

论证：若 `N β ≤ p α n`，极大性给出 `β ⊑ α[n]`，与前提 `α[n] ⊏ β` 冲突（分别用反自反与反对称）；故 `N β > p α n`，再接上 `N (fs α n) ≤ p α n` 即得。

**因此形式化链补齐两环**：Cichon 的极大性定义 ⟹ (B3)（本节）；(B3)+(B4) ⟹ (B2) 的极限情形（§2）。仍缺的一环是 **(B4)**，它要用 BCW Theorem 4(b)（`N α[n] = p(α+n)`），而那条依赖后继与极限的结构，须另加序数层的接口。

## 5. (B4) 与整条链

(B4) 要用 BCW **Theorem 4(b)**（\(N\alpha[n]=p(\alpha+n)\)），而那条确实依赖后继与极限的结构。把所需的序数层接口补进来：后继运算、`N (suc γ) ≤ suc (N γ)`、极限对后继封闭，以及 BCW 对 `p` 的假设 `N α ≤ p α 0 + 1`。

```agda
record CichonFS⁺ : Set₁ where
  field
    Car : Set
    _⊏_ : Car → Car → Set
    N   : Car → ℕ
    p   : Car → ℕ → ℕ
    fs  : Car → ℕ → Car
    sucC : Car → Car
    Lim  : Car → Set

    ⊏-irrefl : ∀ {x} → x ⊏ x → ⊥
    ⊏-asym   : ∀ {x y} → x ⊏ y → y ⊏ x → ⊥
    ⊏-trans  : ∀ {x y z} → x ⊏ y → y ⊏ z → x ⊏ z
    ⊏-tri    : ∀ x y → x ⊏ y ⊎ x ≡ y ⊎ y ⊏ x

    fs-⊏   : ∀ {α n} → fs α n ⊏ α
    fs-N   : ∀ {α n} → N (fs α n) ≤ p α n
    fs-max : ∀ {α n β} → β ⊏ α → N β ≤ p α n → (β ≡ fs α n) ⊎ (β ⊏ fs α n)

    ⊏-sucC   : ∀ {γ} → γ ⊏ sucC γ
    lim-sucC : ∀ {l γ} → Lim l → γ ⊏ l → sucC γ ⊏ l
    N-sucC   : ∀ {γ} → N (sucC γ) ≤ suc (N γ)
    N-p      : ∀ {α} → N α ≤ suc (p α 0)

module _ (C : CichonFS⁺) where
  open CichonFS⁺ C

  B3⁺ : ∀ {α β n} → fs α n ⊏ β → β ⊏ α → N (fs α n) < N β
  B3⁺ {α} {β} {n} αn⊏β β⊏α with N β ≤? p α n
  ... | no  ¬le = ≤-trans (s≤s fs-N) (≰⇒> ¬le)
  ... | yes le  with fs-max β⊏α le
  ...   | inj₁ e = ⊥-elim (⊏-irrefl (subst (λ z → fs α n ⊏ z) e αn⊏β))
  ...   | inj₂ q = ⊥-elim (⊏-asym αn⊏β q)
```

Theorem 4(b) 的下界方向：若 `N α[n] < p(α+n)`，则 `suc α[n]` 也是候选（其范数 `≤ suc (N α[n]) ≤ p(α+n)`，且因 `α` 是极限仍 `⊏ α`），极大性给 `suc α[n] ⊑ α[n]`，与 `α[n] ⊏ suc α[n]` 冲突。

```agda
  thm4b : ∀ {l n} → Lim l → p l n ≤ N (fs l n)
  thm4b {l} {n} liml with N (fs l n) <? p l n
  ... | no  ¬lt = ≮⇒≥ ¬lt
  ... | yes lt with fs-max (lim-sucC liml fs-⊏) (≤-trans N-sucC lt)
  ...   | inj₁ e = ⊥-elim (⊏-irrefl (subst (λ z → fs l n ⊏ z) e ⊏-sucC))
  ...   | inj₂ q = ⊥-elim (⊏-asym ⊏-sucC q)

  B4⁺ : ∀ {l} → Lim l → N l ≤ suc (N (fs l 0))
  B4⁺ liml = ≤-trans N-p (s≤s (thm4b liml))
```

于是整条链闭合：由 Cichon 的极大性定义造出一个 `BSys`，再套用 §2 的 `B2-lim`。

```agda
  asBSys : BSys
  asBSys = record
    { Car = Car ; _⊏_ = _⊏_ ; N = N ; fs = fs ; Lim = Lim
    ; ⊏-trans = ⊏-trans ; ⊏-tri = ⊏-tri ; B3 = B3⁺ ; B4 = B4⁺ }

  B2⁺ : ∀ {α β n} → Lim β → fs α n ⊏ β → β ⊏ α →
        (fs α n ≡ fs β 0) ⊎ (fs α n ⊏ fs β 0)
  B2⁺ = B2-lim asBSys
```

**至此 C2 的正则性是机器检验过的**：从 Cichon 的极大性定义（加上序与 `ℕ` 的基本性质、后继与极限的接口）推出 Bachmann 性质的极限情形。非极限情形由 (B1) 平凡。仍未形式化的是：这套接口在真实 `OT` 上的实例化（要先有 `≺`）。
