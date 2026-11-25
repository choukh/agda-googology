# 判据: 孩子单调

> 定稿后只增不改. 判据 (只导入标准库): 块, 折叠与读回填进 `KidFrame`. `KidMono D` 对量化域 D 陈述: 在有孩子的层号上, 若孩子 c′ 字面上高于 c (`c ⋖ c′`), 则 c′ 的 Ω 树嵌入后的值不低于 c 在 D 里的树嵌入后的值. D 也读层号, 证据与左边 x, 所以可以只取塔或规范读回域.
> 编译定理: c 在 D 上的值无界 (`Unb`) 时 `KidMono D` 不成立 (`unb→¬mono`); D 含某棵吸收右边的树的严格后继时也不成立 (`absorb→¬mono`), 无界时也不成立 (`strict→¬mono`). 所以 D 不能取一切树 (`All`).
> 前提可满足: 玩具实例 `toy` 上 `KidMono OnlyΩ` 成立, `Unb All` 也成立, 所以 `KidMono All` 不成立 (`toy-Ω`, `toy-unb`, `toy-¬all`). 规范域 `OnlyΩ` 上的判据没有否定. 精简块的实填与违反实例在 `YiKidRW`, 推广到一切塔项与后继孩子以及规范域的实例在 `YiKidGen`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKidCrit where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; <-irrefl; m≤n+m; +-mono-≤; +-monoʳ-≤; <⇒≤)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)
```

## 框架

`Kid ℓ`: 第 ℓ 层的孩子下标 (Ω 形状时是低层的树); `KT ℓ c`: 孩子 c 的层里可嵌入的树 (具体块里带 "非零"); `c ⋖ c′`: 字面可得的 "c′ 高于 c" (如孩子下标间的第一位置序), 不判等. `val ℓ o x`: 折叠到第 0 层再读回. `irr` 是值序的严格性: 后继不低于 v 且 v 不高于 u 时矛盾.

```agda
record KidFrame : Set₁ where
  infix 4 _≼_ _⋖_
  field
    Lv      : Set
    Ok      : Lv → Set
    Tr      : Lv → Set
    Kid     : Lv → Set
    KT      : (ℓ : Lv) → Kid ℓ → Set
    _⋖_     : ∀ {ℓ} → Kid ℓ → Kid ℓ → Set
    up      : ∀ {ℓ} → Tr ℓ → (c : Kid ℓ) → KT ℓ c → Tr ℓ
    ΩK      : (ℓ : Lv) (c : Kid ℓ) → KT ℓ c
    V       : Set
    _≼_     : V → V → Set
    ≼-trans : ∀ {u v w} → u ≼ v → v ≼ w → u ≼ w
    osuc    : V → V
    irr     : ∀ {u v} → osuc u ≼ v → v ≼ u → ⊥
    val     : (ℓ : Lv) → Ok ℓ → Tr ℓ → V
```

## 判据与量化域

```agda
module Crit (𝔽 : KidFrame) where
  open KidFrame 𝔽

  Dom : Set₁
  Dom = (ℓ : Lv) → Ok ℓ → Tr ℓ → (c : Kid ℓ) → KT ℓ c → Set

  KidMono : Dom → Set
  KidMono D = (ℓ : Lv) (o : Ok ℓ) (x : Tr ℓ) (c c′ : Kid ℓ) → c ⋖ c′ → (y : KT ℓ c) → D ℓ o x c y
    → val ℓ o (up x c y) ≼ val ℓ o (up x c′ (ΩK ℓ c′))

  All : Dom
  All _ _ _ _ _ = ⊤

  data OnlyΩ : (ℓ : Lv) → Ok ℓ → Tr ℓ → (c : Kid ℓ) → KT ℓ c → Set where
    isΩ : ∀ {ℓ o x c} → OnlyΩ ℓ o x c (ΩK ℓ c)
```

## 否定: 无界, 严格倒置, 吸收加严格后继

```agda
  Unb : Dom → (ℓ : Lv) → Ok ℓ → Tr ℓ → Kid ℓ → Set
  Unb D ℓ o x c = (t : Tr ℓ) → Σ (KT ℓ c) λ y → D ℓ o x c y × (osuc (val ℓ o t) ≼ val ℓ o (up x c y))

  Grow : (ℓ : Lv) → Ok ℓ → Tr ℓ → Kid ℓ → Set
  Grow ℓ o x c = (t : Tr ℓ) → Σ (KT ℓ c) λ y → osuc (val ℓ o t) ≼ val ℓ o (up x c y)

  grow→unb : ∀ {ℓ o x c} → Grow ℓ o x c → Unb All ℓ o x c
  grow→unb G t with G t
  ... | y , q = y , tt , q

  strict→¬mono : (D : Dom) (ℓ : Lv) (o : Ok ℓ) (x : Tr ℓ) (c c′ : Kid ℓ) → c ⋖ c′
    → (y : KT ℓ c) → D ℓ o x c y → osuc (val ℓ o (up x c′ (ΩK ℓ c′))) ≼ val ℓ o (up x c y)
    → KidMono D → ⊥
  strict→¬mono D ℓ o x c c′ r y d q M = irr q (M ℓ o x c c′ r y d)

  unb→¬mono : (D : Dom) (ℓ : Lv) (o : Ok ℓ) (x : Tr ℓ) (c c′ : Kid ℓ) → c ⋖ c′
    → Unb D ℓ o x c → KidMono D → ⊥
  unb→¬mono D ℓ o x c c′ r U M with U (up x c′ (ΩK ℓ c′))
  ... | y , d , q = strict→¬mono D ℓ o x c c′ r y d q M

  absorb→¬mono : (D : Dom) (ℓ : Lv) (o : Ok ℓ) (x : Tr ℓ) (c c′ : Kid ℓ) → c ⋖ c′
    → (y₀ y₁ : KT ℓ c) → D ℓ o x c y₁
    → val ℓ o (up x c′ (ΩK ℓ c′)) ≼ val ℓ o (up x c y₀)
    → osuc (val ℓ o (up x c y₀)) ≼ val ℓ o (up x c y₁)
    → KidMono D → ⊥
  absorb→¬mono D ℓ o x c c′ r y₀ y₁ d ab st M = irr (≼-trans st (M ℓ o x c c′ r y₁ d)) ab
```

## 前提可满足: 玩具实例

一层, 孩子与孩子的树都是自然数, 嵌入是相加, 孩子 c 的 Ω 树是 c, 值序是 `≤`. 规范域上的判据成立, 孩子的值无界, 所以一切树版不成立.

```agda
toy : KidFrame
toy = record
  { Lv = ⊤ ; Ok = λ _ → ⊤ ; Tr = λ _ → ℕ ; Kid = λ _ → ℕ ; KT = λ _ _ → ℕ
  ; _⋖_ = _<_ ; up = λ x c y → x + (c + y) ; ΩK = λ _ c → c
  ; V = ℕ ; _≼_ = _≤_ ; ≼-trans = ≤-trans ; osuc = suc
  ; irr = λ p q → <-irrefl refl (≤-trans p q)
  ; val = λ _ _ t → t }

module T = Crit toy

toy-Ω : T.KidMono T.OnlyΩ
toy-Ω ℓ o x c c′ r .c T.isΩ = +-monoʳ-≤ x (+-mono-≤ (<⇒≤ r) (<⇒≤ r))

toy-unb : (x c : ℕ) → T.Unb T.All tt tt x c
toy-unb x c = T.grow→unb λ t → suc t , ≤-trans (m≤n+m (suc t) c) (m≤n+m (c + suc t) x)

toy-¬all : T.KidMono T.All → ⊥
toy-¬all = T.unb→¬mono T.All tt tt 0 0 1 (s≤s z≤n) (toy-unb 0 0)
```
