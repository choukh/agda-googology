# YiPsumOrig (条件)：原来的规范槽位派发 `ownT ω` 之下，各支输出之间的第一位置

**判决 (编译定理加一条条件定理)：公共上界与目标都取 ω，派发取 `YiRawFold.ownT ω` (`ccompare` 的规范槽位，不先过 `YiPsumBase.pre`)。第 0, 1, 2 支的输出依次是字面的第一位置 (`step₀₁`, `step₁₂`，有限测试)。
第 2 支是第 3 支的第一位置，当且仅当第 2 支字面等于第 3 支的第一支 (`step₂₃-only`, `step₂₃-if`)；这个等式由两个派发函数相等推出，那两个函数逐点相等 (`pointwise`)，所以在 `Funext` 下成立 (`step₂₃-funext`)。**
没有的：不带 `Funext` 的证明 (`refl` 被检查器拒绝，是临时目录里的试验)，也没有否定。不否定逐项的写法：派发先过 `pre` 时同一处对一切 `n` 成立，不用 `Funext` (`YiPsumInst.sideᶜ-step`)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiPsumOrig where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (cO)
open import OCF.Align.YiLvIf using (lev; Plain)
open import OCF.Align.YiLvFoldAdd
open import OCF.Align.YiLvFoldBase using (Way)
open import OCF.Align.YiLvFoldFin using (fin; ω; ω-plain; ω-legal; fin-plain; fin-legal)
open import OCF.Align.YiRawFoldBase
open import OCF.Align.YiRawFold using (Ψ; ownT)
open import OCF.Align.YiRawFoldUp using (firstOf; branchOf)
open import OCF.Align.YiRawFoldNoLim using (IsLc)
open import OCF.Align.YiIrrIf using (Legal)
open import OCF.Align.YiPsumBase using (CohX; orig)
open import OCF.Align.YiPsumFold using (module Termwise)

Funext : Set₁
Funext = ∀ {A : Set} {P : A → Set} {f g : (x : A) → P x} → (∀ x → f x ≡ g x) → f ≡ g
```

## 0 原方案下的逐项折叠：条件定理

`YiPsumFold.Termwise` 取方案 `orig` 就是 `YiRawFold.Ψ` 只改那一行。它的合法性定理原样成立，前提 `O.Dm` 里的 `CohS` 是 `own`, `ownT` 的一致；
下面三节说这个前提在 ω 上的第 2 条方程是什么。

```agda
module O = Termwise orig

orig-termwise-legal : ∀ m → Plain m → ∀ k pl L (D : O.Dm k pl L) (x : Ext m k) → CohX k L x →
  ∀ ξ (l : Lgl k ξ) (nb : Nested k ξ) → Lgl m (O.Ψᵗ m k pl L D x ξ l nb)
orig-termwise-legal = O.Ψᵗ-legal
```

## 1 前三支

`sideᵒ n` 是 `top` 在第 `n` 支上的折叠，派发是 `ownT ω` 限制到第 `n` 支。它是 `YiRawFoldInst.ω+1-body₀` 里求部分和的那一列。

```agda
sideᵒ : ℕ → Raw ω
sideᵒ n = Ψ ω (fin n) (fin-plain n) (fin-legal n) (inL (ownT ω ω-plain ω-legal) n) G.top tt tt

step₀₁ : Cp ω (sideᵒ 0) (sideᵒ 1)
step₀₁ = inj₂ (inj₁ refl)

step₁₂ : Cp ω (sideᵒ 1) (sideᵒ 2)
step₁₂ = inj₂ (inj₁ refl)

slot₂ : branchOf (sideᵒ 2) ≡ 2
slot₂ = refl

slot₃-first : branchOf (firstOf (sideᵒ 3)) ≡ 2
slot₃-first = refl
```

## 2 第 2 支与第 3 支：归到两个派发函数的相等

第 3 支的第一支是同一棵 `top` 在层号 2 上的折叠，派发是 `ownT ω` 先限制到第 3 支再限制一步 (`u₃`)；第 2 支用的是直接限制到第 2 支 (`u₂`)。
两个函数在 `Pre (fin 2)` 的两个位置上都相等，是 `refl`；作为函数不是定义性相等 (`ccompare` 的有界搜索卡在变量位置上，两边的搜索上界不同)。

```agda
u₂ u₃ : (r : Pre (fin 2)) → Way ω (lev (fin 2) r)
u₂ r = wayOf (inL (ownT ω ω-plain ω-legal) 2) r
u₃ r = wayOf (inS (inL (ownT ω ω-plain ω-legal) 3)) r

pointwise : ∀ r → u₂ r ≡ u₃ r
pointwise (inj₁ tt) = refl
pointwise (inj₂ (inj₁ tt)) = refl

first₃ : firstOf (sideᵒ 3) ≡ Ψ ω (fin 2) (fin-plain 2) (fin-legal 2) (mix u₃) G.top tt tt
first₃ = refl

step₂₃-if : sideᵒ 2 ≡ firstOf (sideᵒ 3) → Cp ω (sideᵒ 2) (sideᵒ 3)
step₂₃-if e = inj₂ (inj₁ e)

step₂₃-from-eq : u₂ ≡ u₃ → Cp ω (sideᵒ 2) (sideᵒ 3)
step₂₃-from-eq e = step₂₃-if
  (cong (λ v → Ψ ω (fin 2) (fin-plain 2) (fin-legal 2) (mix v) G.top tt tt) e)

step₂₃-funext : Funext → Cp ω (sideᵒ 2) (sideᵒ 3)
step₂₃-funext fe = step₂₃-from-eq (fe pointwise)

-- YiPsumBase.CohX 在 ω 上的第 2 条方程正是它 (方向相反).
step₂₃-cohX : CohX ω ω-legal (ownT ω ω-plain ω-legal) → Cp ω (sideᵒ 2) (sideᵒ 3)
step₂₃-cohX h = step₂₃-if
  (cong (λ x → Ψ ω (fin 2) (fin-plain 2) (fin-legal 2) x G.top tt tt) (sym (proj₁ h 2)))
```

## 3 反过来：第一位置只能是 "第 2 支等于第 3 支的第一支"

第 3 支的第一位置的脊：它自己 (槽位在第 3 支)，第一支 (槽位 `(2 , 根)`)，再下去是槽位 `(1 , 根)` 的结点，然后是 `successor ω top`。
第 2 支的槽位在第 2 支，第一支的槽位在第 1 支。`Free₂ z`：`z` 的脊上每个结点的第一支的头是后继，或是槽位不在第 1 支的结点。
`top` 的各份拷贝满足它 (加法造的结点，第一支与自己同在一支里)，所以里面没有第 2 支。写法平行 `YiRawFoldNoLim`。

```agda
NotOne : ℕ → Set
NotOne (suc zero) = ⊥
NotOne _ = ⊤

Hd₂ : Raw ω → Set
Hd₂ (G.suc _) = ⊤
Hd₂ (G.lc (n , _) _ _ _) = NotOne n
Hd₂ _ = ⊥

Free₂ : Raw ω → Set
Free₂ G.zero = ⊤
Free₂ (G.suc a) = Free₂ a
Free₂ (G.lim f) = ∀ n → Free₂ (f n)
Free₂ (G.lc r c t g) = Hd₂ t × Free₂ t
Free₂ (G.em i T) = ⊥
Free₂ G.top = ⊤

no-below₂ : ∀ z → Free₂ z → Cp ω (sideᵒ 2) z → ⊥
no-below₂ (G.lc r c t g) fr (inj₁ e) = subst (λ w → Hd₂ (firstOf w)) (sym e) (proj₁ fr)
no-below₂ G.zero fr (inj₁ e) = subst IsLc e tt
no-below₂ (G.suc a) fr (inj₁ e) = subst IsLc e tt
no-below₂ (G.lim f) fr (inj₁ e) = subst IsLc e tt
no-below₂ G.top fr (inj₁ e) = subst IsLc e tt
no-below₂ (G.suc a) fr (inj₂ p) = no-below₂ a fr p
no-below₂ (G.lim f) fr (inj₂ (n , p)) = no-below₂ (f n) (fr n) p
no-below₂ (G.lc r c t g) fr (inj₂ p) = no-below₂ t (proj₂ fr) p

record FA {k} (B : Alg k) : Set₁ where
  field
    Fr Hdᵀ : Alg.T B → Set
    Ok : Set
    frS : ∀ {y} → Fr y → Fr (Alg.sT B y)
    hdS : ∀ {y} → Hdᵀ (Alg.sT B y)
    hdN : Ok → ∀ r c t g → Hdᵀ (Alg.nT B r c t g)
    frN : ∀ r c t g → Hdᵀ t → Fr t → Fr (Alg.nT B r c t g)

faS : ∀ {k} {B : Alg (suc k)} → FA B → FA (shS B)
faS F = record
  { Fr = Fr; Hdᵀ = Hdᵀ; Ok = Ok; frS = frS; hdS = hdS
  ; hdN = λ ok r → hdN ok (inj₂ r); frN = λ r → frN (inj₂ r) }
  where open FA F

-- 第 n 支里造出的结点, 槽位都在第 n 支; n 不是 1 时它们可以作第一支的头.
faω : ∀ n → FA (shL (rawAlg ω) n)
faω n = record
  { Fr = Free₂; Hdᵀ = Hd₂; Ok = NotOne n; frS = λ fr → fr; hdS = tt
  ; hdN = λ ok r c t g → ok; frN = λ r c t g h fr → h , fr }

OkAt : ∀ j {B : Alg (fin j)} → FA B → Set
OkAt zero F = ⊤
OkAt (suc j) F = FA.Ok F

ok-down : ∀ j {B : Alg (fin (suc j))} (F : FA B) → FA.Ok F → OkAt j (faS F)
ok-down zero F ok = tt
ok-down (suc j) F ok = ok

free-cO : ∀ j (B : Alg (fin j)) (F : FA B) → OkAt j F → ∀ y → FA.Fr F y →
  FA.Hdᵀ F (add (fin j) B y (cO (fin j))) × FA.Fr F (add (fin j) B y (cO (fin j)))
free-cO zero B F ok y fr = FA.hdS F , FA.frS F fr
free-cO (suc j) B F ok y fr =
  FA.hdN F ok (inj₁ tt) (cO (fin j)) _ _ ,
  FA.frN F (inj₁ tt) (cO (fin j)) _ _
    (proj₁ (free-cO j (shS B) (faS F) (ok-down j F ok) y fr))
    (proj₂ (free-cO j (shS B) (faS F) (ok-down j F ok) y fr))

ok-top : ∀ n → OkAt n (faS (faω (suc n)))
ok-top zero = tt
ok-top (suc n) = tt

free-top : ∀ n y → Free₂ y → Free₂ (add (fin n) (shL (rawAlg ω) n) y G.top)
free-top zero y fr = fr
free-top (suc n) y fr =
  free-cO n (shS (shL (rawAlg ω) (suc n))) (faS (faω (suc n))) (ok-top n) y fr

hd-add : ∀ t → Hd₂ t → Hd₂ (plus ω G.top t)
hd-add (G.suc a) h = tt
hd-add (G.lc r c t g) h = h

free-add : ∀ z → Free₂ z → Free₂ (plus ω G.top z)
free-add G.zero fr = tt
free-add (G.suc a) fr = free-add a fr
free-add (G.lim f) fr = λ n → free-add (f n) (fr n)
free-add (G.lc r c t g) (h , fr) = hd-add t h , free-add t fr
free-add G.top fr =
  cum-ind Free₂ (λ n y → add (fin n) (shL (rawAlg ω) n) y G.top) free-top G.top tt

free-copies : ∀ j → Free₂ (copies ω G.top j)
free-copies zero = tt
free-copies (suc j) = free-add (copies ω G.top j) (free-copies j)

two≢three : 2 ≡ 3 → ⊥
two≢three ()

two≢one : 2 ≡ 1 → ⊥
two≢one ()

step₂₃-only : Cp ω (sideᵒ 2) (sideᵒ 3) → sideᵒ 2 ≡ firstOf (sideᵒ 3)
step₂₃-only (inj₁ e) = ⊥-elim (two≢three (cong branchOf e))
step₂₃-only (inj₂ (inj₁ e)) = e
step₂₃-only (inj₂ (inj₂ (inj₁ e))) = ⊥-elim (two≢one (cong branchOf e))
step₂₃-only (inj₂ (inj₂ (inj₂ (inj₁ e)))) = ⊥-elim (subst IsLc e tt)
step₂₃-only (inj₂ (inj₂ (inj₂ (inj₂ (j , q))))) =
  ⊥-elim (no-below₂ (copies ω G.top j) (free-copies j) q)
```
