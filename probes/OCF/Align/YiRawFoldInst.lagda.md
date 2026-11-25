# YiRawFold 实例：ω+1, ω+2, ω·2+1；与只读裸层号的折叠不同的两处

**判决 (编译定理)：三个公共上界上闭项 `Φ K … base top` 合法，`CohP` 由 `refl` 填上。在 ω+2 上，链的第 0 点 `top` 处，
结点自己那一层 (ω+1) 的折叠把层号 ω 的结点保留在根槽位 (`new-keeps`)；上一轮的 `wayᵇ` 在同一处折掉 (`old-folds`)。**
在 ω+1 上派发与上一轮相同 (有限测试)，不同的是 `top` 处推进用的输出取部分和 (`ω+1-body₀`)。读法 ψ₀(Ω_{ω+1}), ψ₀(Ω_{ω+2}), ψ₀(Ω_{ω·2+1})，没有值定理。
与 `foldᶠ` 只比了 `n = 0` 与 `n = 1` 的第 0 项。折叠在 [YiRawFold](YiRawFold.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawFoldInst where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (Ω̂; cO; cO-Lgl; cO-Nested)
open import OCF.Align.YiIrrIf using (R; CP; self; suc; lim; Legal; iterate)
open import OCF.Align.YiIrrFbIf using (Pt; pt) renaming (at to atᵖ)
open import OCF.Align.YiLvIf using (Plain; lev; Kept)
open import OCF.Align.YiLvFoldAdd using (plus; successor)
open import OCF.Align.YiLvFoldBase using (Way; keep; fold; startᴸ)
import OCF.Align.YiLvFoldFin as F
open import OCF.Align.YiLvFoldFin
  using (fin; ω; ω-plain; ω-legal; fin-plain; fin-legal; IsKeep; wayᵇ; foldᶠ)
open import OCF.Align.YiLvFoldLim using (dom-Ωω1)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiRawIf
open import OCF.Align.YiRawFoldBase
open import OCF.Align.YiRawFold
```

## 1 闭项与它的行

`closed K pl L` 读作 ψ₀(Ω_K) (读法)。在后继层号 `suc k` 上它是链行：链在 `Raw k` 里，起点 `cO k`，
下一点是这一点加上目标 `k` 的折叠 (`ownT`：根位置的规范派发限制到 `k`) 在这一点的输出，观察是目标第 0 层的折叠。

```agda
closed : ∀ K → Plain K → Legal K → R
closed K pl L = Φ K pl L base G.top tt tt

closed-legal : ∀ K pl L → CohP K pl L → Lgl zero (closed K pl L)
closed-legal K pl L h = Φ-legal K pl L base h G.top tt tt

closed-nested : ∀ K pl L → Nested zero (closed K pl L)
closed-nested K pl L = Φ-nested K pl L base G.top tt tt

-- 不要前提的那一版: 极限层号上 top 取部分和.
closedᵐ : ∀ K → Plain K → Legal K → R
closedᵐ K pl L = Φᵐ K pl L base G.top tt tt

closedᵐ-legal : ∀ K pl L → Lgl zero (closedᵐ K pl L)
closedᵐ-legal K pl L = RawFold.legal rawFold K pl L base G.top tt tt

rootN : ∀ k (pl : Plain k) (L : Legal k) → NdR zero k
rootN k pl L = ndT zero k pl L low

points : ∀ k (pl : Plain k) (L : Legal k) → ℕ → Pt k (cO k)
points k pl L = iterate (nextᴿ pl (rootN k pl L)) (startᴿ (rootN k pl L))

closed-row : ∀ k pl L → closed (suc k) pl L ≡
  G.lim (λ n → obsᴿ (rootN k pl L) (points k pl L n))
closed-row k pl L = refl

closed-start : ∀ k pl L → atᵖ (points k pl L 0) ≡ cO k
closed-start k pl L = refl

closed-body : ∀ k pl L η .(e : Gd k (cO k) η) →
  bodyᴿ (rootN k pl L) (pt η e) ≡
  Ψ k k pl L (ownT k pl L) η (proj₁ (proj₂ e)) (proj₂ (proj₂ e))
closed-body k pl L η e = refl

closed-obs : ∀ k pl L η .(e : Gd k (cO k) η) →
  obsᴿ (rootN k pl L) (pt η e) ≡ Ψ zero k pl L low η (proj₁ (proj₂ e)) (proj₂ (proj₂ e))
closed-obs k pl L η e = refl

closed-feedback : ∀ k pl L n → atᵖ (points k pl L (suc n)) ≡
  plus k (atᵖ (points k pl L n)) (bodyᴿ (rootN k pl L) (points k pl L n))
closed-feedback k pl L n = refl

closed-zero : ∀ pl L → closed zero pl L ≡ successor zero (cO zero)
closed-zero pl L = refl

closed-lim : ∀ f pl L → closed (lim f) pl L ≡ G.lim (λ n → closed (f n) (pl n) (proj₂ L n))
closed-lim f pl L = refl
```

## 2 三个公共上界

`ω = lim fin`，路径是一步后继；`ω·2 = lim (ω+n)`。一致性的方程两边定义性相等。

```agda
fin-coh : ∀ n → CohP (fin n) (fin-plain n) (fin-legal n)
fin-coh zero = tt
fin-coh (suc n) = fin-coh n

ω-coh : CohP ω ω-plain ω-legal
ω-coh = (λ n → refl) , fin-coh

ω+ : ℕ → LF
ω+ zero = ω
ω+ (suc n) = suc (ω+ n)

ω+-plain : ∀ n → Plain (ω+ n)
ω+-plain zero = ω-plain
ω+-plain (suc n) = ω+-plain n

ω+-legal : ∀ n → Legal (ω+ n)
ω+-legal zero = ω-legal
ω+-legal (suc n) = ω+-legal n

ω+-coh : ∀ n → CohP (ω+ n) (ω+-plain n) (ω+-legal n)
ω+-coh zero = ω-coh
ω+-coh (suc n) = ω+-coh n

Ωω+1 Ωω+2 : R
Ωω+1 = closed (ω+ 1) ω-plain ω-legal
Ωω+2 = closed (ω+ 2) ω-plain ω-legal

Ωω+1-legal : Lgl zero Ωω+1
Ωω+1-legal = closed-legal (ω+ 1) ω-plain ω-legal ω-coh

Ωω+2-legal : Lgl zero Ωω+2
Ωω+2-legal = closed-legal (ω+ 2) ω-plain ω-legal ω-coh

ω2 : LF
ω2 = lim ω+

ω2-plain : Plain ω2
ω2-plain = ω+-plain

ω2-legal : Legal ω2
ω2-legal = (λ n → suc self) , ω+-legal

ω2-coh : CohP ω2 ω2-plain ω2-legal
ω2-coh = (λ n → refl) , ω+-coh

Ωω2+1 : R
Ωω2+1 = closed (suc ω2) ω2-plain ω2-legal

Ωω2+1-legal : Lgl zero Ωω2+1
Ωω2+1-legal = closed-legal (suc ω2) ω2-plain ω2-legal ω2-coh
```

## 3 ω+2：新折叠保留而 `wayᵇ` 折掉的那一点

`Ωω+2` 的链在 `Raw (ω+1)` 里，第 0 点是 `top`。推进用的是目标 ω+1 的折叠在 `top` 上的输出；`top` 在 ω+1 里是根位置的结点，层号 ω。
新折叠问 `dispatch (ω+2) … (at 根) (根下一格)`，得到 "保留在根槽位" (`YiRawIf.test-keep-ω`)，输出是结点。
上一轮同一处是 `ψ (ω+1) (Ω̂ (ω+1))`，`wayᵇ (ω+1) ω = fold`，输出是 ℕ 极限。

```agda
body₀ : Raw (ω+ 1)
body₀ = bodyᴿ (rootN (ω+ 1) ω-plain ω-legal) (points (ω+ 1) ω-plain ω-legal 0)

new-way : wayOf (ownT (ω+ 1) ω-plain ω-legal) (inj₁ tt) ≡ keep (inj₁ tt) refl
new-way = refl

new-keeps : body₀ ≡
  G.lc (inj₁ tt) G.top
    (Ψ (ω+ 1) ω ω-plain ω-legal (inS (ownT (ω+ 1) ω-plain ω-legal)) G.top tt tt)
    (λ η e → Ψ (ω+ 1) ω ω-plain ω-legal (inS (ownT (ω+ 1) ω-plain ω-legal)) η
      (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
new-keeps = refl

new-kept : Kept (ω+ 1) ω body₀
new-kept = inj₁ tt , refl , G.top , _ , _ , new-keeps

old-way : wayᵇ (ω+ 1) ω ≡ fold
old-way = refl

old-folds : IsLim (F.ψ (ω+ 1) (Ω̂ (ω+ 1)) dom-Ωω1)
old-folds = tt

-- 下一个链点因此不同: 新的是 top 加上一个层号 ω 的结点.
new-point₁ : atᵖ (points (ω+ 1) ω-plain ω-legal 1) ≡ plus (ω+ 1) G.top body₀
new-point₁ = refl
```

`top` 之下的层号 (有限层号) 在目标 ω+1 上也保留：`inS (ownT (ω+1))` 在位置 `(n , r)` 上问的是
`dispatch (ω+2) … (at 根) (根下两格里的位置)`，完全性由 `YiRawFold.complete-ownT` 与 `complete-S` 给出。

```agda
below-ω-kept : ∀ (r : Pre ω) → IsKeep (wayOf (inS (ownT (ω+ 1) ω-plain ω-legal)) r)
below-ω-kept r =
  complete-S (ownT (ω+ 1) ω-plain ω-legal) (complete-ownT (ω+ 1) ω-plain ω-legal) r
    (inj₂ r , refl)
```

## 4 ω+1：派发与上一轮相同，`top` 的行不同

`Ωω+1` 的链在 `Raw ω` 里。有限层号的结点保留在规范槽位，与上一轮的 `way-ω` 是同一个槽位 (有限测试)。
不同的是第 0 点 `top` 处推进用的输出：这里是各支折叠的部分和，上一轮是各项的极限 `ψ ω (Ω̂ ω)`。

```agda
test-slot-ω : wayOf (ownT ω ω-plain ω-legal) (3 , inj₂ (inj₁ tt)) ≡ keep (2 , inj₁ tt) refl
test-slot-ω = refl

ω+1-body₀ : bodyᴿ (rootN ω ω-plain ω-legal) (points ω ω-plain ω-legal 0) ≡
  G.lim (psum ω (λ n → Ψ ω (fin n) (fin-plain n) (fin-legal n)
    (inL (ownT ω ω-plain ω-legal) n) G.top tt tt))
ω+1-body₀ = refl
```

## 5 与上一轮有限层号的闭项 `foldᶠ`

`n = 0` 字面相等。`n ≥ 1` 两边都是 `Raw (fin (n-1))` 里的链，起点相同；分支函数一边是 `ψ` 复合读回，一边是 `Ψ`，
是两个递归定义，极限之下的逐字相等要函数外延，没有比。这里只核对 `n = 1` 的第 0 项。

```agda
fin-zero : closed (fin 0) tt tt ≡ foldᶠ 0
fin-zero = refl

fin-one-term₀ : obsᴿ (rootN (fin 0) tt tt) (points (fin 0) tt tt 0) ≡
  F.out zero (fin 0) (cO (fin 0)) tt tt (Ω̂ (fin 0)) (F.Ωᶠ-branch 0) (F.dom-Ωᶠ 1)
    (startᴸ (fin 0) (cO (fin 0)) tt tt)
fin-one-term₀ = refl
```
