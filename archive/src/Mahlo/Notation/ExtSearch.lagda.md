# 提取分支的基本列是可计算的：搜索界由范数给出

[RESEARCH.md](../RESEARCH.md) §116。CONTRACT §2 要求"对表示为非零极限的 λ，输出**总可计算的** λ[n]"。而

    λ[n] := max{β ≺ λ : N β ≤ N λ + n}

表面上是对一个**无穷集**取极大。本文件机器检验它其实是**有界搜索**：所有候选项都落在一张由 `N λ + n` 显式算出的有限表里。界的来源是 [`ExtOT`](ExtOT.lagda.md) §8 已证的 `size t ≤ 3 · N t + 1`——**提取分支自己的范数**，不是外部输入。

于是 `λ[n]` 的可计算性归约到**唯一一条**剩余义务：`≺` 可判定。良基性与线性由参考分析承担（§113.4），本文件与它们无关。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Notation.ExtSearch where

open import Mahlo.Notation.ExtOT

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; +-mono-≤; *-mono-≤; m≤m+n; m≤n+m; _≤?_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Base
  using (List; []; _∷_; _++_; map; length; filter; cartesianProduct; cartesianProductWith)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺; ∈-cartesianProductWith⁺; ∈-cartesianProduct⁺; ∈-filter⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable.Core using (_×?_)
open import Relation.Unary using (Decidable)
```

## 1. 分量表的枚举

和项的分量表需要单独枚举。每个主元项大小 `≥ 1`，故总大小 `≤ k` 的表长度 `≤ k`，元素大小也 `≤ k`。

```agda
listsOf : ℕ → List PTm → List (List PTm)
listsOf zero    _  = [] ∷ []
listsOf (suc k) xs = [] ∷ cartesianProductWith _∷_ xs (listsOf k xs)

listsOf-complete : ∀ {xs} ps k →
                   (∀ {p} → p ∈ ps → p ∈ xs) → length ps ≤ k → ps ∈ listsOf k xs
listsOf-complete []       zero    _ _        = here refl
listsOf-complete []       (suc k) _ _        = here refl
listsOf-complete (p ∷ ps) (suc k) h (s≤s le) =
  there (∈-cartesianProductWith⁺ _∷_
          (h (here refl))
          (listsOf-complete ps k (λ q∈ → h (there q∈)) le))
```

## 2. 项的枚举

`enumT n`／`enumP n` 列出大小 `≤ n` 的项。递归**结构递减**——这正是 [`ExtOT`](ExtOT.lagda.md) §8 把 `size (prin p)` 取作 `1 + sizeP p` 的理由：大小 `≤ suc n` 的项只由大小 `≤ n` 的部件搭成。

```agda
mkSum : PTm → PTm × List PTm → Tm
mkSum p (q , ps) = sum p q ps

mutual
  enumT : ℕ → List Tm
  enumT zero    = []
  enumT (suc n) =
    zer ∷ (map prin (enumP n)
        ++ cartesianProductWith mkSum (enumP n)
             (cartesianProduct (enumP n) (listsOf n (enumP n))))

  enumP : ℕ → List PTm
  enumP zero    = []
  enumP (suc n) =
    K ∷ (cartesianProductWith phi (enumT n) (enumT n)
      ++ map Omg (enumT n)
      ++ map psiK (enumT n)
      ++ cartesianProductWith psi (enumT n) (enumT n))
```

## 3. 主元项的大小下界

```agda
sizeP≥1 : ∀ p → 1 ≤ sizeP p
sizeP≥1 K         = s≤s z≤n
sizeP≥1 (phi _ _) = s≤s z≤n
sizeP≥1 (Omg _)   = s≤s z≤n
sizeP≥1 (psiK _)  = s≤s z≤n
sizeP≥1 (psi _ _) = s≤s z≤n

∈-sizeL : ∀ {p ps} → p ∈ ps → sizeP p ≤ sizeL ps
∈-sizeL {ps = q ∷ ps} (here refl) = m≤m+n (sizeP q) (sizeL ps)
∈-sizeL {ps = q ∷ ps} (there r∈)  = ≤-trans (∈-sizeL r∈) (m≤n+m (sizeL ps) (sizeP q))

len≤sizeL : ∀ ps → length ps ≤ sizeL ps
len≤sizeL []       = z≤n
len≤sizeL (p ∷ ps) = +-mono-≤ (sizeP≥1 p) (len≤sizeL ps)
```

## 4. 枚举是完备的

```agda
mutual
  enumT-complete : ∀ t n → size t ≤ n → t ∈ enumT n
  enumT-complete zer          (suc n) _        = here refl
  enumT-complete (prin p)     (suc n) (s≤s le) =
    there (∈-++⁺ˡ (∈-map⁺ prin (enumP-complete p n le)))
  enumT-complete (sum p q ps) (suc n) (s≤s le) =
    there (∈-++⁺ʳ (map prin (enumP n)) (∈-cartesianProductWith⁺ mkSum
      (enumP-complete p n p≤)
      (∈-cartesianProduct⁺ (enumP-complete q n q≤)
        (listsOf-complete ps n
          (λ {r} r∈ → enumP-complete r n (≤-trans (∈-sizeL r∈) ps≤))
          (≤-trans (len≤sizeL ps) ps≤)))))
    where
      p≤ : sizeP p ≤ n
      p≤ = ≤-trans (≤-trans (m≤m+n (sizeP p) (sizeP q))
                            (m≤m+n (sizeP p + sizeP q) (sizeL ps))) le
      q≤ : sizeP q ≤ n
      q≤ = ≤-trans (≤-trans (m≤n+m (sizeP q) (sizeP p))
                            (m≤m+n (sizeP p + sizeP q) (sizeL ps))) le
      ps≤ : sizeL ps ≤ n
      ps≤ = ≤-trans (m≤n+m (sizeL ps) (sizeP p + sizeP q)) le

  enumP-complete : ∀ p n → sizeP p ≤ n → p ∈ enumP n
  enumP-complete K         (suc n) _        = here refl
  enumP-complete (phi a b) (suc n) (s≤s le) =
    there (∈-++⁺ˡ (∈-cartesianProductWith⁺ phi
      (enumT-complete a n (≤-trans (m≤m+n (size a) (size b)) le))
      (enumT-complete b n (≤-trans (m≤n+m (size b) (size a)) le))))
  enumP-complete (Omg a)   (suc n) (s≤s le) =
    there (∈-++⁺ʳ (cartesianProductWith phi (enumT n) (enumT n))
      (∈-++⁺ˡ (∈-map⁺ Omg (enumT-complete a n le))))
  enumP-complete (psiK a)  (suc n) (s≤s le) =
    there (∈-++⁺ʳ (cartesianProductWith phi (enumT n) (enumT n))
      (∈-++⁺ʳ (map Omg (enumT n))
        (∈-++⁺ˡ (∈-map⁺ psiK (enumT-complete a n le)))))
  enumP-complete (psi s a) (suc n) (s≤s le) =
    there (∈-++⁺ʳ (cartesianProductWith phi (enumT n) (enumT n))
      (∈-++⁺ʳ (map Omg (enumT n))
        (∈-++⁺ʳ (map psiK (enumT n))
          (∈-cartesianProductWith⁺ psi
            (enumT-complete s n (≤-trans (m≤m+n (size s) (size a)) le))
            (enumT-complete a n (≤-trans (m≤n+m (size a) (size s)) le))))))
```

## 5. 搜索界

```agda
bound : Tm → ℕ → ℕ
bound lam n = 3 * (N lam + n) + 1

search-complete : ∀ {lam n} t → N t ≤ N lam + n → t ∈ enumT (bound lam n)
search-complete {lam} {n} t le =
  enumT-complete t (bound lam n)
    (≤-trans (size≤ t) (+-mono-≤ (*-mono-≤ (≤-refl {3}) le) (≤-refl {1})))
```

**这就是结论**：凡范数满足 `N t ≤ N λ + n` 的项，都在 `enumT (3 · (N λ + n) + 1)` 这张**显式有限表**里。取极大只需在表上扫一遍。

## 6. 候选表

把 `≺` 抽象成任一可判定谓词——本文件不依赖 `≺` 的定义。

```agda
module _ {P : Tm → Set} (P? : Decidable P) where

  cands : Tm → ℕ → List Tm
  cands lam n =
    filter (λ t → P? t ×? (N t ≤? N lam + n)) (enumT (bound lam n))

  cands-complete : ∀ {lam n} t → P t → N t ≤ N lam + n → t ∈ cands lam n
  cands-complete {lam} {n} t Pt le =
    ∈-filter⁺ (λ s → P? s ×? (N s ≤? N lam + n)) (search-complete {lam} {n} t le) (Pt , le)
```

取 `P := (_≺ λ)`，`cands λ n` 就是 `λ[n]` 的完整候选集；`cands-complete` 说它不漏，`filter` 的定义说它不多。

## 7. `≺` 递归的测度

配方给出的 `≺` 按 Arai Def 2.2 子句 3 的 `min` 与条件 (9) 定义，全部子句只比较**直接子项**（§116.2）。要它良定义，需要每个直接子项的 `size` 严格递减。这一条在这里一次证清：

```agda
sub-prin : ∀ p → sizeP p < size (prin p)
sub-prin p = ≤-refl

sub-phiˡ : ∀ a b → size a < sizeP (phi a b)
sub-phiˡ a b = s≤s (m≤m+n (size a) (size b))

sub-phiʳ : ∀ a b → size b < sizeP (phi a b)
sub-phiʳ a b = s≤s (m≤n+m (size b) (size a))

sub-psiK : ∀ a → size a < sizeP (psiK a)
sub-psiK a = ≤-refl

sub-psiˡ : ∀ s a → size s < sizeP (psi s a)
sub-psiˡ s a = s≤s (m≤m+n (size s) (size a))

sub-psiʳ : ∀ s a → size a < sizeP (psi s a)
sub-psiʳ s a = s≤s (m≤n+m (size a) (size s))

sub-Omg : ∀ a → size a < sizeP (Omg a)
sub-Omg a = ≤-refl

sub-sumˡ : ∀ p q ps → sizeP p < size (sum p q ps)
sub-sumˡ p q ps = s≤s (≤-trans (m≤m+n (sizeP p) (sizeP q))
                               (m≤m+n (sizeP p + sizeP q) (sizeL ps)))

sub-sumʳ : ∀ p q ps → sizeP q < size (sum p q ps)
sub-sumʳ p q ps = s≤s (≤-trans (m≤n+m (sizeP q) (sizeP p))
                               (m≤m+n (sizeP p + sizeP q) (sizeL ps)))

sub-sumL : ∀ p q ps → sizeL ps < size (sum p q ps)
sub-sumL p q ps = s≤s (m≤n+m (sizeL ps) (sizeP p + sizeP q))
```

故"按 `size s + size t` 递归"这条定义方式在 `OTˣ` 上合法——与 Setzer 按 `length(a)+length(c)` 递归定义 `≺′`（§65.1 已核 Definition 3.3）是同一个办法，但测度是**配方产出的** `size`，不是 Setzer 随项定义的 `length`。

## 8. 结论与边界

CONTRACT §2 的"**总可计算的** λ[n]"在提取分支上化为一条：**`≺` 可判定**。这一条与良基性、线性无关，也与端点的序数值无关。

**本文件未覆盖**：`≺` 的定义本身（§116 给出其来源与递归测度）；`enumT` 的**无冗余**（表里会有重复项与非合式项，不影响正确性，只影响效率）；`OTˣ` 合式条件（Arai 条件 (9)）的判定——它同样归入"`≺` 可判定"这一条，因为 (9) 的两个合取项都是项比较。

`bound` 不是最优的：`3` 来自二元符号的最坏情形（`ExtOT` §8），实际项通常远小。CONTRACT 只要求界**可计算**，不要求紧。
