# YiLv 接口：层号任意可数时的片段、位置与有界比较

**档位：定义、规范实例检查、一条编译定理 (`compare`)。没有折叠，没有值。** 构造路 (`YiLvFold*`) 与否定路
(`YiLvNeg*`) 共用本文件；定稿后只增不改。块是 [RR5IrrCore](RR5IrrCore.lagda.md)，读回与 Ω 在
[RR5IrrCheck](RR5IrrCheck.lagda.md)，第一位置与合法性在 [YiIrrIf](YiIrrIf.lagda.md)。
本文件钉住这一步的律的定义域：被比较的两个层号都是同一个字面层号 `K` 里的位置。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvIf where

open import Data.Nat.Base using (ℕ; zero; suc; _<′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (<-cmp; <⇒<′)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
```

## 1 片段：Ω 结点的层号里没有 Ω 结点

`Plain k`：层号 `k` 只由零、后继、ℕ 极限组成。`OnlyP x`：`x` 的每个 Ω 结点的层号都是这样的，
对第一支与分支遗传 (分支的守卫无关)。它含 `Only0` 与 `Only01` 两个旧片段。

```agda
Plain : LF → Set
Plain zero = ⊤
Plain (suc k) = Plain k
Plain (lim f) = ∀ n → Plain (f n)
Plain (lc k c w b t g) = ⊥

OnlyP : LF → Set
OnlyP zero = ⊤
OnlyP (suc x) = OnlyP x
OnlyP (lim f) = ∀ n → OnlyP (f n)
OnlyP (lc k c w b t g) =
  Plain k × OnlyP t × (∀ η .(e : Gd k c η) → OnlyP (g η e))
```

## 2 位置的层号

`Pre K` 的元素是 `K` 里的一个位置；`lev K r` 是这个位置上的层号，`Low K r` 就是它的 `Raw`。
对一切 `K` 定义，含 Ω 结点的层号 (下一步用)。

```agda
lev : (K : LF) → Pre K → LF
lev (suc k) (inj₁ _) = k
lev (suc k) (inj₂ r) = lev k r
lev (lim f) (n , r) = lev (f n) r
lev (lc k c w b t g) (inj₁ (inj₁ _)) = k
lev (lc k c w b t g) (inj₁ (inj₂ r)) = lev k r
lev (lc k c w b t g) (inj₂ (inj₁ r)) = lev t r
lev (lc k c w b t g) (inj₂ (inj₂ (η , e , r))) = lev (g η e) r

Low-lev : ∀ K r → Low K r ≡ Raw (lev K r)
Low-lev (suc k) (inj₁ _) = refl
Low-lev (suc k) (inj₂ r) = Low-lev k r
Low-lev (lim f) (n , r) = Low-lev (f n) r
Low-lev (lc k c w b t g) (inj₁ (inj₁ _)) = refl
Low-lev (lc k c w b t g) (inj₁ (inj₂ r)) = Low-lev k r
Low-lev (lc k c w b t g) (inj₂ (inj₁ r)) = Low-lev t r
Low-lev (lc k c w b t g) (inj₂ (inj₂ (η , e , r))) = Low-lev (g η e) r

lev-plain : ∀ K → Plain K → ∀ r → Plain (lev K r)
lev-plain (suc k) pl (inj₁ _) = pl
lev-plain (suc k) pl (inj₂ r) = lev-plain k pl r
lev-plain (lim f) pl (n , r) = lev-plain (f n) (pl n) r

-- 位置沿字面的第一位置路径搬运, 层号不变.
shift : ∀ {a b} → CP a b → (p : Pre a) → Σ (Pre b) λ p′ → lev b p′ ≡ lev a p
shift self p = p , refl
shift (suc q) p = inj₂ (proj₁ (shift q p)) , proj₂ (shift q p)
shift (lim n q) p = (n , proj₁ (shift q p)) , proj₂ (shift q p)
shift (fst q) p = inj₂ (inj₁ (proj₁ (shift q p))) , proj₂ (shift q p)
```

## 3 三路的陈述

`Tri i j`：目标层 `i` 与结点层 `j` 的关系，带数据。`below` 给出 `j` 在 `i` 里的槽位 (保留行要用它)；
`above` 给出 `i` 在 `j` 里的槽位；`same` 是层号树字面相等。两个层号都必须是同一个 `K` 里的位置，
见 `Compare` 的类型。不同位置可以是同一个层号，所以这不是值上的三歧。

```agda
data Tri (i j : LF) : Set where
  below : (s : Pre i) → lev i s ≡ j → Tri i j
  above : (s : Pre j) → lev j s ≡ i → Tri i j
  same  : i ≡ j → Tri i j

Compare : Set
Compare = ∀ K → Plain K → Legal K → (q q′ : Pre K) → Tri (lev K q) (lev K q′)

-- 同一陈述, 合法性只许无关地用. 折叠的证书若无关, 能交给比较的只有这个.
CompareIrr : Set
CompareIrr = ∀ K → Plain K → .(Legal K) → (q q′ : Pre K) → Tri (lev K q) (lev K q′)
```

## 4 有界比较：合法性作数据时成立

对 `K` 递归。ℕ 极限处两个位置在不同的分支，先比分支编号，再把编号小的那个位置沿合法性里的
第一位置路径搬到编号大的分支里；这一处读了合法性的数据。平行 `YiLevelCompare.compare`
与 BTBO 的 `<-dec`。

```agda
steps : ∀ {f : ℕ → LF} → (∀ n → CP (f n) (f (suc n))) →
  ∀ {n m} → n <′ m → CP (f n) (f m)
steps st ≤′-refl = st _
steps st (≤′-step p) = CP-tr (steps st p) (st _)

compare : Compare
compare zero pl lg () q′
compare (suc k) pl lg (inj₁ _) (inj₁ _) = same refl
compare (suc k) pl lg (inj₁ _) (inj₂ r′) = below r′ refl
compare (suc k) pl lg (inj₂ r) (inj₁ _) = above r refl
compare (suc k) pl lg (inj₂ r) (inj₂ r′) = compare k pl lg r r′
compare (lim f) pl (st , lg) (n , r) (m , r′) with <-cmp n m
... | tri< n<m _ _ =
  subst (λ z → Tri z (lev (f m) r′))
    (proj₂ (shift (steps st (<⇒<′ n<m)) r))
    (compare (f m) (pl m) (lg m) (proj₁ (shift (steps st (<⇒<′ n<m)) r)) r′)
... | tri≈ _ refl _ = compare (f n) (pl n) (lg n) r r′
... | tri> _ _ m<n =
  subst (λ z → Tri (lev (f n) r) z)
    (proj₂ (shift (steps st (<⇒<′ m<n)) r′))
    (compare (f n) (pl n) (lg n) r (proj₁ (shift (steps st (<⇒<′ m<n)) r′)))
```

## 5 保留结点的陈述

`Kept m k y`：目标层 `m` 的值 `y` 是一个保留结点，槽位上的层号是 `k`。从它能读出槽位这一份数据。

```agda
Kept : (m k : LF) → Raw m → Set
Kept m k y =
  Σ (Pre m) λ r → (lev m r ≡ k) ×
  Σ (Low m r) λ c → Σ (Raw m) λ t →
  Σ ((η : Low m r) → .(GdL m r c η) → Raw m) λ g → y ≡ G.lc r c t g
```

## 6 规范实例检查：塔的第 3 项在片段里

`tw 3` 是层号 0 的结点，第 `η` 支是 `Ω̂ (read0 η)`。读回 `read0 η` 是 `Plain` 的；
`Ω̂` 与一般读回 `up` 把 `Plain` 的层号送进片段。`tw 3` 的合法性与起点证据已有
(`YiIrrNegLegal.Legal-tw`, `YiIrrFoldSeed.seed-tw`)，这里不重复。

```agda
up0-plain : ∀ a .(nb : Nested zero a) → Plain (up zero a nb)
up0-plain G.zero nb = tt
up0-plain (G.suc a) nb = up0-plain a nb
up0-plain (G.lim f) nb = λ n → up0-plain (f n) (nb n)
up0-plain (G.lc () c t g) nb
up0-plain (G.em () a) nb
up0-plain G.top nb = tt

upN-onlyP : ∀ y → Plain y → (r : Pre y) (c : Low y r)
  .(l : LglLow y r c) .(b : NestedLow y r c) (t : LF)
  (g : (η : Low y r) → .(GdL y r c η) → LF) →
  OnlyP t → (∀ η .(e : GdL y r c η) → OnlyP (g η e)) →
  OnlyP (upN y r c l b t g)
upN-onlyP (suc k) pl (inj₁ _) c l b t g ot og = pl , ot , og
upN-onlyP (suc k) pl (inj₂ r) c l b t g ot og = upN-onlyP k pl r c l b t g ot og
upN-onlyP (lim f) pl (n , r) c l b t g ot og = upN-onlyP (f n) (pl n) r c l b t g ot og

up-onlyP : ∀ y → Plain y → ∀ a .(nb : Nested y a) → OnlyP (up y a nb)
upT-onlyP : ∀ y → Plain y → OnlyP (upT y)
upK-onlyP : ∀ y → Plain y → ∀ i (T : KidR y i) .(nb : NestedKid y i T) →
  OnlyP (upK y i T nb)

up-onlyP y pl G.zero nb = tt
up-onlyP y pl (G.suc a) nb = up-onlyP y pl a nb
up-onlyP y pl (G.lim f) nb = λ n → up-onlyP y pl (f n) (nb n)
up-onlyP y pl (G.lc r c t g) nb =
  upN-onlyP y pl r c (proj₁ nb) (proj₁ (proj₂ nb))
    (up y t (proj₁ (proj₂ (proj₂ nb))))
    (λ η e → up y (g η e) (proj₂ (proj₂ (proj₂ nb)) η e))
    (up-onlyP y pl t (proj₁ (proj₂ (proj₂ nb))))
    (λ η e → up-onlyP y pl (g η e) (proj₂ (proj₂ (proj₂ nb)) η e))
up-onlyP y pl (G.em i T) nb = upK-onlyP y pl i T nb
up-onlyP y pl G.top nb = upT-onlyP y pl

upK-onlyP (suc k) pl _ T nb = up-onlyP k pl T nb
upK-onlyP (lim f) pl n T nb = up-onlyP (f n) (pl n) T nb

upT-onlyP zero pl = tt
upT-onlyP (suc k) pl =
  pl , upT-onlyP k pl , (λ η e → up-onlyP k pl η (proj₂ (proj₂ e)))
upT-onlyP (lim f) pl = λ n → upT-onlyP (f n) (pl n)

tw2-onlyP : OnlyP (tw 2)
tw2-onlyP = upT-onlyP (suc zero) tt

tw3-onlyP : OnlyP (tw 3)
tw3-onlyP =
  tt , tw2-onlyP ,
  (λ η e → upT-onlyP (up zero η (proj₂ (proj₂ e))) (up0-plain η (proj₂ (proj₂ e))))
```

`compare` 说明带数据的合法性足以比较同一个层号里的两个位置。`CompareIrr` 没有在这里证，也没有否定。
