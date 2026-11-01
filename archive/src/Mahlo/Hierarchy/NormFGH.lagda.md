# 范数基本列上的 FGH：§62 的形式化

本文件形式化 [RESEARCH.md](../RESEARCH.md) §62 的引理 A、B、C 与命题 P。

**归属与范围（§82）**：本文件证明的内容不是新结果——Cichon 的方法与 [Buchholz–Cichon–Weiermann 1994](https://epub.ub.uni-muenchen.de/3849/1/16.pdf) 的 (EMP) 已有同一内容，本项目是独立重新发现。此外，绝对范数界（`∥b∥ ≤ n`）一般**不满足** Bachmann 性质，文献用的是相对界（`Nβ ≤ Nα+n`）。本文件把界抽象成**预算** `bud x n`（§2），两种取法同时被覆盖；但下面证到的是 `FSNorm` 各条公理的推论，Bachmann 性质本身不在其中。

这里**不**涉及提取（CONTRACT 的 E），也不构造任何记号系统。被形式化的是一条与具体记号系统无关的事实：**只要一个良基序配上"范数截断取极大"式的基本列，其上的 FGH 就自动具备输入单调性与带可算阈值的层级支配**。真实的 `OT` 是否提供这样的结构，是 §65 的内容，不在本文件内。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Hierarchy.NormFGH where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; n≤1+n; +-suc; +-identityʳ; +-monoˡ-≤)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Induction.WellFounded using (WellFounded; Acc; acc)

private
  absurd : ∀ {A B : Set} {v : Maybe A} {y} → v ≡ just y → v ≡ nothing → B
  absurd refl ()
```

## 1. 有限迭代

`F` 的定义里有 `n+1` 次迭代，先把迭代的性质单独证出来。这五条是 §62 全部不等式推理的组合内核。

```agda
iter : ℕ → (ℕ → ℕ) → ℕ → ℕ
iter zero    f n = n
iter (suc k) f n = f (iter k f n)

module _ {f : ℕ → ℕ} (inc : ∀ m → suc m ≤ f m) where

  iter-≥ : ∀ k n → n ≤ iter k f n
  iter-≥ zero    n = ≤-refl
  iter-≥ (suc k) n = ≤-trans (iter-≥ k n)
                             (≤-trans (n≤1+n _) (inc (iter k f n)))

  module _ (mf : ∀ {a b} → a ≤ b → f a ≤ f b) where

    iter-≥1 : ∀ k n → f n ≤ iter (suc k) f n
    iter-≥1 k n = mf (iter-≥ k n)

    iter-≥add : ∀ k n → f n + k ≤ iter (suc k) f n
    iter-≥add zero    n = ≤-reflexive (+-identityʳ (f n))
    iter-≥add (suc k) n = ≤-trans (≤-reflexive (+-suc (f n) k))
                                  (≤-trans (s≤s (iter-≥add k n)) (inc _))

    iter-mono-cnt : ∀ {j k} → j ≤ k → ∀ n → iter j f n ≤ iter k f n
    iter-mono-cnt {j = zero}  {k = k}     z≤n     n = iter-≥ k n
    iter-mono-cnt {j = suc j} {k = suc k} (s≤s p) n = mf (iter-mono-cnt p n)

iter-mono-arg : ∀ {f} → (∀ {a b} → a ≤ b → f a ≤ f b) →
                ∀ k {m n} → m ≤ n → iter k f m ≤ iter k f n
iter-mono-arg mf zero    m≤n = m≤n
iter-mono-arg mf (suc k) m≤n = mf (iter-mono-arg mf k m≤n)
```

逐点支配的迭代版本。两个版本的区别是：全域版本用于 `Acc` 无关性（那里无阈值），带阈值版本用于引理 B（那里 `F′ y ≤ F′ z` 只在实参 `≥ ‖y‖` 时成立）。阈值可用，是因为迭代的实参只增不减。

```agda
iter-mono-fun : ∀ {f g} → (∀ {a b} → a ≤ b → g a ≤ g b) → (∀ m → f m ≤ g m) →
                ∀ k n → iter k f n ≤ iter k g n
iter-mono-fun mg f≤g zero    n = ≤-refl
iter-mono-fun {f} mg f≤g (suc k) n =
  ≤-trans (f≤g (iter k f n)) (mg (iter-mono-fun mg f≤g k n))

iter-mono-fun′ : ∀ {f g t} → (∀ m → suc m ≤ f m) →
                 (∀ {a b} → a ≤ b → g a ≤ g b) →
                 (∀ {m} → t ≤ m → f m ≤ g m) →
                 ∀ k {n} → t ≤ n → iter k f n ≤ iter k g n
iter-mono-fun′ inc mg f≤g zero    t≤n = ≤-refl
iter-mono-fun′ {f} inc mg f≤g (suc k) {n} t≤n =
  ≤-trans (f≤g (≤-trans t≤n (iter-≥ inc k n)))
          (mg (iter-mono-fun′ inc mg f≤g k t≤n))
```

## 2. 结构

下面的记录把 §62 的"约定"一段写成接口。`fs x n` 即 `x[n]`，`Maybe` 表达 `S_n(x)` 可能为空。四条公理依次是：`x[n] ⊏ x`；`‖x[n]‖ ≤ n`；**存在性**——有范数 `≤ n` 的真前驱时 `x[n]` 有定义；**极大性**——这样的前驱都被 `x[n]` 支配。

```agda
record FSNorm : Set₁ where
  field
    Car   : Set
    _⊏_   : Car → Car → Set
    ⊏-wf  : WellFounded _⊏_
    ∥_∥   : Car → ℕ
    bud   : Car → ℕ → ℕ
    fs    : Car → ℕ → Maybe Car

    bud-mono : ∀ {x m n} → m ≤ n → bud x m ≤ bud x n
    bud-lift : ∀ {x n y m k} → fs x n ≡ just y → m ≤ n → m ≤ k → bud x m ≤ bud y k

    fs-⊏    : ∀ {x n y} → fs x n ≡ just y → y ⊏ x
    fs-norm : ∀ {x n y} → fs x n ≡ just y → ∥ y ∥ ≤ bud x n
    fs-tot  : ∀ {x n b} → b ⊏ x → ∥ b ∥ ≤ bud x n → Σ[ y ∈ Car ] (fs x n ≡ just y)
    fs-max  : ∀ {x n b y} → fs x n ≡ just y → b ⊏ x → ∥ b ∥ ≤ bud x n → b ≡ y ⊎ b ⊏ y
```

`bud x n` 是取 `x[n]` 时允许的**范数预算**。两种实例：

- **绝对界**（本项目 §57／§62 原用）：`bud x n = n`。`bud-mono` 即 `≤` 自身；`bud-lift` 化为 `m ≤ k`。
- **相对界**（Cichon／BCW 1994，§82–§83 表明这才是给出 Bachmann 系统的那个）：`bud x n = ∥ x ∥ + n`。`bud-mono` 显然；`bud-lift` 由 `∥ x[n] ∥ ≥ ∥ x ∥`（BCW Theorem 4(b) 给出等号）加 `m ≤ k` 得到。

把预算抽象出来，下面的证明对两者同时成立。

## 3. FGH

沿 `⊏` 的良基性递归。带显式 `Acc` 参数，随后一并证明取值与所选 `Acc` 无关。

定义里不能直接用 `with`：那样生成的 with-函数在后续证明中不可约，`F′ x a n` 无法展开。改用一个显式的 view，`F′` 对 view 作模式匹配，证明里 `with view x n` 即可让两边同步归约。

```agda
module _ (S : FSNorm) where
  open FSNorm S

  data FSView (x : Car) (n : ℕ) : Set where
    none : fs x n ≡ nothing → FSView x n
    some : ∀ y → fs x n ≡ just y → FSView x n

  view : ∀ x n → FSView x n
  view x n with fs x n in eq
  ... | nothing = none eq
  ... | just y  = some y eq

  F′ : ∀ x → Acc _⊏_ x → ℕ → ℕ
  F′ x (acc rs) n = go (view x n)
    where
    go : FSView x n → ℕ
    go (none _)    = suc n
    go (some y eq) = iter (suc n) (F′ y (rs (fs-⊏ eq))) n

  F : Car → ℕ → ℕ
  F x = F′ x (⊏-wf x)
```

## 4. 引理 A、B、C

四条相互依赖（B 用 C 与 I，C 用 A、B 与 I），故打包后对 `⊏` 作一次良基归纳。`gI` 是 `Acc` 无关性，它在 `gC` 的 `b ≡ x[n]` 支上必需。

```agda
  record Good (x : Car) : Set where
    field
      gA : ∀ (a : Acc _⊏_ x) n → suc n ≤ F′ x a n
      gB : ∀ (a : Acc _⊏_ x) {m n} → m ≤ n → F′ x a m ≤ F′ x a n
      gC : ∀ (a : Acc _⊏_ x) {b} (ab : Acc _⊏_ b) {n} →
           (b ≡ x ⊎ (b ⊏ x × ∥ b ∥ ≤ bud x n)) → F′ b ab n ≤ F′ x a n
  open Good public
```

`gC` 的 `⊎` 左支就是 `Acc` 无关性（`b ≡ x` 时两边只差所取的 `Acc` 证明），右支是引理 C 本身。把两者合并，是为了避免在证明内部对 `refl` 作模式匹配——那会与 `where` 绑定的类型冲突。左支不需要范数条件，这也正是 §62 引理 C 的阈值只出现在严格小于的情形。

```agda
  good : ∀ x → Good x
  good x = go x (⊏-wf x)
    where
    go : ∀ x → Acc _⊏_ x → Good x
    go x (acc rs) = record { gA = A ; gB = B ; gC = C }
      where
      ih : ∀ {y} → y ⊏ x → Good y
      ih p = go _ (rs p)

      A : ∀ (a : Acc _⊏_ x) n → suc n ≤ F′ x a n
      A (acc rs′) n with view x n
      ... | none _    = ≤-refl
      ... | some y eq = ≤-trans (s≤s (iter-≥ inc n n)) (inc (iter n (F′ y ay) n))
        where
        ay  = rs′ (fs-⊏ eq)
        inc = gA (ih (fs-⊏ eq)) ay

      C : ∀ (a : Acc _⊏_ x) {b} (ab : Acc _⊏_ b) {n} →
          (b ≡ x ⊎ (b ⊏ x × ∥ b ∥ ≤ bud x n)) → F′ b ab n ≤ F′ x a n
      C (acc rs′) (acc r₁) {n} (inj₁ refl) with view x n
      ... | none _    = ≤-refl
      ... | some y eq =
            iter-mono-fun (gB g (rs′ p)) (λ m → gC g (rs′ p) (r₁ p) (inj₁ refl))
                          (suc n) n
        where
        p = fs-⊏ eq
        g = ih p
      C (acc rs′) {b} ab {n} (inj₂ (b⊏x , ∥b∥≤n)) with view x n
      ... | none e    = absurd (proj₂ (fs-tot b⊏x ∥b∥≤n)) e
      ... | some z eq =
            ≤-trans (gC gz az ab (conv (fs-max eq b⊏x ∥b∥≤n)))
                    (iter-≥1 incz mz n n)
        where
        az   = rs′ (fs-⊏ eq)
        gz   = ih (fs-⊏ eq)
        incz = gA gz az
        mz   = gB gz az
        conv : b ≡ z ⊎ b ⊏ z → b ≡ z ⊎ (b ⊏ z × ∥ b ∥ ≤ bud z n)
        conv (inj₁ e) = inj₁ e
        conv (inj₂ q) = inj₂ (q , ≤-trans ∥b∥≤n (bud-lift eq ≤-refl ≤-refl))

      B : ∀ (a : Acc _⊏_ x) {m n} → m ≤ n → F′ x a m ≤ F′ x a n
      B (acc rs′) {m} {n} m≤n with view x m | view x n
      ... | none _     | none _     = s≤s m≤n
      ... | none _     | some z eqn =
            ≤-trans (s≤s m≤n)
              (≤-trans (s≤s (iter-≥ incz n n)) (incz (iter n (F′ z az) n)))
        where
        az   = rs′ (fs-⊏ eqn)
        incz = gA (ih (fs-⊏ eqn)) az
      ... | some y eqm | none e =
            absurd (proj₂ (fs-tot (fs-⊏ eqm)
                     (≤-trans (fs-norm eqm) (bud-mono m≤n)))) e
      ... | some y eqm | some z eqn =
            ≤-trans (iter-mono-fun′ incy mz y≤z (suc m) ≤-refl)
              (≤-trans (iter-mono-arg mz (suc m) m≤n)
                       (iter-mono-cnt incz mz (s≤s m≤n) n))
        where
        py   = fs-⊏ eqm
        pz   = fs-⊏ eqn
        ay   = rs′ py
        az   = rs′ pz
        gz   = ih pz
        incy = gA (ih py) ay
        incz = gA gz az
        mz   = gB gz az
        y≤z : ∀ {k} → m ≤ k → F′ y ay k ≤ F′ z az k
        y≤z {k} m≤k =
          gC gz az ay (conv (fs-max eqn py (≤-trans (fs-norm eqm) (bud-mono m≤n))))
          where
          conv : y ≡ z ⊎ y ⊏ z → y ≡ z ⊎ (y ⊏ z × ∥ y ∥ ≤ bud z k)
          conv (inj₁ e) = inj₁ e
          conv (inj₂ q) = inj₂ (q , ≤-trans (fs-norm eqm) (bud-lift eqn m≤n m≤k))
```

## 5. 结论：引理 A–C 与命题 P

把 `Acc` 参数实例化到 `⊏-wf`，得到 §62 的四条陈述。

```agda
  lemA : ∀ x n → suc n ≤ F x n
  lemA x = gA (good x) (⊏-wf x)

  lemB : ∀ x {m n} → m ≤ n → F x m ≤ F x n
  lemB x = gB (good x) (⊏-wf x)

  lemC : ∀ {b x n} → b ⊏ x → ∥ b ∥ ≤ bud x n → F b n ≤ F x n
  lemC {b} {x} p q = gC (good x) (⊏-wf x) (⊏-wf b) (inj₂ (p , q))
```

命题 P：定量支配。阈值同样是 `‖b‖`。

```agda
  propP : ∀ {b x n} → b ⊏ x → ∥ b ∥ ≤ bud x n → F b n + n ≤ F x n
  propP {b} {x} {n} b⊏x ∥b∥≤n = go (⊏-wf x)
    where
    go : (a : Acc _⊏_ x) → F b n + n ≤ F′ x a n
    go (acc rs) with view x n
    ... | none e    = absurd (proj₂ (fs-tot b⊏x ∥b∥≤n)) e
    ... | some z eq = ≤-trans (+-monoˡ-≤ n b≤z) (iter-≥add incz mz n n)
      where
      az   = rs (fs-⊏ eq)
      gz   = good z
      incz = gA gz az
      mz   = gB gz az
      conv : b ≡ z ⊎ b ⊏ z → b ≡ z ⊎ (b ⊏ z × ∥ b ∥ ≤ bud z n)
      conv (inj₁ e) = inj₁ e
      conv (inj₂ q) = inj₂ (q , ≤-trans ∥b∥≤n (bud-lift eq ≤-refl ≤-refl))
      b≤z : F b n ≤ F′ z az n
      b≤z = gC gz az (⊏-wf b) (conv (fs-max eq b⊏x ∥b∥≤n))
```

## 6. 这条形式化说明了什么

`lemA`–`lemC` 与 `propP` 合起来就是 CONTRACT 的 **C4**（输入单调、层级支配、阈值可算），阈值即 `∥ b ∥`。它们**只**依赖 `FSNorm` 的四条公理，与任何具体记号系统无关。

它**没有**说明的：`FSNorm` 是否可由 `OT` 实例化（§65 在纸面上验证了，尚未形式化）；端点 `λ_M` 的取法（§66）；C5 的受控比较（§63、§64、§74）；以及全部输入端内容。特别地，本文件里 `FSNorm` 是一个**假设**，不是构造——把它当作提取成功的证据是错误的。
