# YiRawFold：保留结点的目标上，各支折叠的极限不合法

**判决 (编译的否定定理，一个实例)：公共上界与目标都取 ω (接口的 `self` 派发，槽位取结点自己的位置)，`top` 在各支上的折叠 `side n` 排成的 ℕ 极限不合法 (`side-lim-illegal`)：
第 1 支的输出不是第 2 支的输出的第一位置。** 这是 [YiRawFold](YiRawFold.lagda.md) 在 `mix` 之下取部分和的依据。
只否定 "`self` 派发下取各支的极限" 这一种写法；不否定规范槽位的派发 (`at q`, `ownT`) 下取极限，那里没有证也没有否定。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawFoldNoLim where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (cO)
open import OCF.Align.YiLvFoldAdd
open import OCF.Align.YiLvFoldFin using (fin; ω)
open import OCF.Align.YiRawFoldUp using (side; branchOf; firstOf; one≢two)
```

## 1 不变量

`side 1` 是槽位 `(1 , 根)` 的结点，第一支是 ℕ 极限。`Free z`：`z` 的第一位置的脊上没有嵌入，脊上每个结点的第一支的头是后继或结点。
这样的 `z` 的第一位置里没有 `side 1`。

```agda
IsLc : Raw ω → Set
IsLc (G.lc _ _ _ _) = ⊤
IsLc _ = ⊥

Hd : Raw ω → Set
Hd (G.suc _) = ⊤
Hd (G.lc _ _ _ _) = ⊤
Hd _ = ⊥

Free : Raw ω → Set
Free G.zero = ⊤
Free (G.suc a) = Free a
Free (G.lim f) = ∀ n → Free (f n)
Free (G.lc r c t g) = Hd t × Free t
Free (G.em i T) = ⊥
Free G.top = ⊤

no-below : ∀ z → Free z → Cp ω (side 1) z → ⊥
no-below (G.lc r c t g) fr (inj₁ e) = subst (λ w → Hd (firstOf w)) (sym e) (proj₁ fr)
no-below G.zero fr (inj₁ e) = subst IsLc e tt
no-below (G.suc a) fr (inj₁ e) = subst IsLc e tt
no-below (G.lim f) fr (inj₁ e) = subst IsLc e tt
no-below G.top fr (inj₁ e) = subst IsLc e tt
no-below (G.suc a) fr (inj₂ p) = no-below a fr p
no-below (G.lim f) fr (inj₂ (n , p)) = no-below (f n) (fr n) p
no-below (G.lc r c t g) fr (inj₂ p) = no-below t (proj₂ fr) p
```

## 2 `top` 的各份拷贝满足不变量

`side 2` 的脊走到 `successor ω top`，它的各项是 `copies ω top j`，由加法造出。加法经值域接口 `Alg` 进到低层，
所以不变量也写成 `Alg` 上的一份 (`FA`)，对 `shS`, `shL` 不变。

```agda
record FA {k} (B : Alg k) : Set₁ where
  field
    Fr Hdᵀ : Alg.T B → Set
    frS : ∀ {y} → Fr y → Fr (Alg.sT B y)
    hdS : ∀ {y} → Hdᵀ (Alg.sT B y)
    hdN : ∀ r c t g → Hdᵀ (Alg.nT B r c t g)
    frN : ∀ r c t g → Hdᵀ t → Fr t → Fr (Alg.nT B r c t g)

faS : ∀ {k} {B : Alg (suc k)} → FA B → FA (shS B)
faS F = record
  { Fr = Fr; Hdᵀ = Hdᵀ; frS = frS; hdS = hdS
  ; hdN = λ r → hdN (inj₂ r); frN = λ r → frN (inj₂ r) }
  where open FA F

faL : ∀ {f} {B : Alg (lim f)} → FA B → ∀ n → FA (shL B n)
faL F n = record
  { Fr = Fr; Hdᵀ = Hdᵀ; frS = frS; hdS = hdS
  ; hdN = λ r → hdN (n , r); frN = λ r → frN (n , r) }
  where open FA F

faω : FA (rawAlg ω)
faω = record
  { Fr = Free; Hdᵀ = Hd; frS = λ fr → fr; hdS = tt
  ; hdN = λ r c t g → tt; frN = λ r c t g h fr → h , fr }

free-cO : ∀ j (B : Alg (fin j)) (F : FA B) y → FA.Fr F y →
  FA.Hdᵀ F (add (fin j) B y (cO (fin j))) × FA.Fr F (add (fin j) B y (cO (fin j)))
free-cO zero B F y fr = FA.hdS F , FA.frS F fr
free-cO (suc j) B F y fr =
  FA.hdN F (inj₁ tt) (cO (fin j)) _ _ ,
  FA.frN F (inj₁ tt) (cO (fin j)) _ _
    (proj₁ (free-cO j (shS B) (faS F) y fr)) (proj₂ (free-cO j (shS B) (faS F) y fr))

free-top : ∀ n y → Free y → Free (add (fin n) (shL (rawAlg ω) n) y G.top)
free-top zero y fr = fr
free-top (suc n) y fr =
  free-cO n (shS (shL (rawAlg ω) (suc n))) (faS (faL faω (suc n))) y fr

hd-add : ∀ t → Hd t → Hd (plus ω G.top t)
hd-add (G.suc a) h = tt
hd-add (G.lc r c t g) h = tt

free-add : ∀ z → Free z → Free (plus ω G.top z)
free-add G.zero fr = tt
free-add (G.suc a) fr = free-add a fr
free-add (G.lim f) fr = λ n → free-add (f n) (fr n)
free-add (G.lc r c t g) (h , fr) = hd-add t h , free-add t fr
free-add G.top fr =
  cum-ind Free (λ n y → add (fin n) (shL (rawAlg ω) n) y G.top) free-top G.top tt

free-copies : ∀ j → Free (copies ω G.top j)
free-copies zero = tt
free-copies (suc j) = free-add (copies ω G.top j) (free-copies j)
```

## 3 否定

`side 2` 是槽位 `(2 , 根)` 的结点，第一支是槽位 `(2 , 根下一格)` 的结点，再往下的第一支是 `successor ω top`。
`side 1` 等于前两个要 `1 ≡ 2`，等于第三个要结点等于极限，在第三个之下被第 1, 2 节排除。

```agda
side-not-below : Cp ω (side 1) (side 2) → ⊥
side-not-below (inj₁ e) = one≢two (cong branchOf e)
side-not-below (inj₂ (inj₁ e)) = one≢two (cong branchOf e)
side-not-below (inj₂ (inj₂ (inj₁ e))) = subst IsLc e tt
side-not-below (inj₂ (inj₂ (inj₂ (j , q)))) =
  no-below (copies ω G.top j) (free-copies j) q

side-lim-illegal : Lgl ω (G.lim side) → ⊥
side-lim-illegal l = side-not-below (proj₁ l 1)
```
