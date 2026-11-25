# YiRead 块：YiNextCore 的可读重写

**非验收文件。判决：定义 (第 1 层)，没有定理。** 与 [YiNextCore](YiNextCore.lagda.md) 定义上一一对应 (同样的构造子、子句与归纳递归结构)，只改命名与排版 (另加两个定义性缩写 `PositionTree`、`ChildTree`)，不加不删数学内容。
命名用英文全词；按惯例 `zero`、`suc`、`lim` 保留缩写 (作者 2026-11-12)，`Λ` 照旧。这里不说明任何关于值或合法性的事。
与旧块的对应 (塔与 `Λ`) 在 [YiReadCheck](YiReadCheck.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiReadCore where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## 1 块

`Raw.Tree` 是一层的树，四个参数由层号算出 (`RawTree`)；`layerLimit` 是 Ω 结点，`top` 是这一层的 Ω。
`Layer` 把一层打成一包，使位置与孩子上的一层各只用一次分派。Ω 结点层号的位置与孩子只取合法的分支下标，
读回的层号合法才有依据。

```agda
module Raw (Position : Set) (PositionTree : Position → Set)
           (Child : Set) (ChildTree : Child → Set) where
  data Tree : Set where
    zero       : Tree
    suc        : Tree → Tree
    lim        : (ℕ → Tree) → Tree
    layerLimit : (position : Position) (branch : PositionTree position → Tree) → Tree
    embed      : (child : Child) → ChildTree child → Tree
    top        : Tree

data Level : Set

record Layer : Set₁ where
  constructor makeLayer
  field
    Carrier       : Set
    strictlyBelow : Carrier → Carrier → Set
    legal         : Carrier → Set
    top           : Carrier
    readBack      : Carrier → Level

Position : Level → Set
positionLayer : (level : Level) → Position level → Layer
PositionTree : (level : Level) → Position level → Set
Child : Level → Set
childLayer : (level : Level) → Child level → Layer
ChildTree : (level : Level) → Child level → Set
RawTree : Level → Set
layerOf : Level → Layer
StrictlyBelow : (level : Level) → RawTree level → RawTree level → Set
StrictlyBelowWithinChild : (level : Level) (child child′ : Child level) → child ≡ child′ →
  ChildTree level child → ChildTree level child′ → Set
Legal : (level : Level) → RawTree level → Set
readBack : (level : Level) → RawTree level → Level
readBackLayerLimit : (level : Level) (position : Position level) →
  (PositionTree level position → Level) → Level
readBackTop : Level → Level

data Level where
  zero       : Level
  suc        : Level → Level
  lim        : (ℕ → Level) → Level
  layerLimit : (indexLevel : Level) (branchLevel : RawTree indexLevel → Level) → Level

PositionTree level position = Layer.Carrier (positionLayer level position)

ChildTree level child = Layer.Carrier (childLayer level child)

RawTree level = Raw.Tree (Position level) (PositionTree level) (Child level) (ChildTree level)

layerOf level = makeLayer (RawTree level) (StrictlyBelow level) (Legal level) Raw.top (readBack level)

Position zero = ⊥
Position (suc predecessor) = ⊤ ⊎ Position predecessor
Position (lim sequence) = Σ ℕ λ n → Position (sequence n)
Position (layerLimit indexLevel branchLevel) =
  Σ (RawTree indexLevel) λ index → Legal indexLevel index × Position (branchLevel index)

positionLayer zero ()
positionLayer (suc predecessor) (inj₁ _) = layerOf predecessor
positionLayer (suc predecessor) (inj₂ position) = positionLayer predecessor position
positionLayer (lim sequence) (n , position) = positionLayer (sequence n) position
positionLayer (layerLimit indexLevel branchLevel) (index , _ , position) =
  positionLayer (branchLevel index) position

Child zero = ⊥
Child (suc predecessor) = ⊤
Child (lim sequence) = ℕ
Child (layerLimit indexLevel branchLevel) = Σ (RawTree indexLevel) (Legal indexLevel)

childLayer zero ()
childLayer (suc predecessor) _ = layerOf predecessor
childLayer (lim sequence) n = layerOf (sequence n)
childLayer (layerLimit indexLevel branchLevel) (index , _) = layerOf (branchLevel index)
```

`StrictlyBelow` 是一层里的严格第一位置序，`AtOrBelow` 是相等或严格。结点的严格第一位置经过 `top` 那一支；嵌入之间要孩子相同。
合法：ℕ 极限逐项是第一位置；结点在合法的分支下标上分支合法，并且对下标单调。

```agda
AtOrBelowIn : (layer : Layer) → Layer.Carrier layer → Layer.Carrier layer → Set
AtOrBelowIn layer lower upper = (lower ≡ upper) ⊎ Layer.strictlyBelow layer lower upper

AtOrBelow : (level : Level) → RawTree level → RawTree level → Set
AtOrBelow level lower upper = (lower ≡ upper) ⊎ StrictlyBelow level lower upper

StrictlyBelow level lower Raw.zero = ⊥
StrictlyBelow level lower (Raw.suc upper) = AtOrBelow level lower upper
StrictlyBelow level lower (Raw.lim sequence) = Σ ℕ λ n → AtOrBelow level lower (sequence n)
StrictlyBelow level lower (Raw.layerLimit position branch) =
  AtOrBelow level lower (branch (Layer.top (positionLayer level position)))
StrictlyBelow level (Raw.embed child lower) (Raw.embed child′ upper) =
  Σ (child ≡ child′) λ same → StrictlyBelowWithinChild level child child′ same lower upper
StrictlyBelow level lower (Raw.embed child′ upper) = ⊥
StrictlyBelow level lower Raw.top = ⊥

StrictlyBelowWithinChild level child .child refl lower upper =
  Layer.strictlyBelow (childLayer level child) lower upper

Legal level Raw.zero = ⊤
Legal level (Raw.suc tree) = Legal level tree
Legal level (Raw.lim sequence) =
  (∀ n → AtOrBelow level (sequence n) (sequence (suc n))) × (∀ n → Legal level (sequence n))
Legal level (Raw.layerLimit position branch) =
  (∀ index → Layer.legal (positionLayer level position) index → Legal level (branch index)) ×
  (∀ index index′ →
     Layer.legal (positionLayer level position) index →
     AtOrBelowIn (positionLayer level position) index index′ →
     Layer.legal (positionLayer level position) index′ →
     AtOrBelow level (branch index) (branch index′))
Legal level (Raw.embed child tree) = Layer.legal (childLayer level child) tree
Legal level Raw.top = ⊤
```

## 2 读回与塔

`top` 读成 `readBackTop level`，即 Ω̂ level。

```agda
readBack level Raw.zero = zero
readBack level (Raw.suc tree) = suc (readBack level tree)
readBack level (Raw.lim sequence) = lim (λ n → readBack level (sequence n))
readBack level (Raw.layerLimit position branch) =
  readBackLayerLimit level position (λ index → readBack level (branch index))
readBack level (Raw.embed child tree) = Layer.readBack (childLayer level child) tree
readBack level Raw.top = readBackTop level

readBackLayerLimit zero ()
readBackLayerLimit (suc predecessor) (inj₁ _) branch = layerLimit predecessor branch
readBackLayerLimit (suc predecessor) (inj₂ position) branch =
  readBackLayerLimit predecessor position branch
readBackLayerLimit (lim sequence) (n , position) branch =
  readBackLayerLimit (sequence n) position branch
readBackLayerLimit (layerLimit indexLevel branchLevel) (index , _ , position) branch =
  readBackLayerLimit (branchLevel index) position branch

readBackTop zero = suc zero
readBackTop (suc predecessor) = layerLimit predecessor (readBack predecessor)
readBackTop (lim sequence) = lim (λ n → readBackTop (sequence n))
readBackTop (layerLimit indexLevel branchLevel) =
  layerLimit indexLevel (λ index → readBackTop (branchLevel index))

tower : ℕ → Level
tower zero = zero
tower (suc n) = readBackTop (tower n)

Λ : Level
Λ = lim tower
```

## 3 一般层的加法

`NodeBuilder target source`：在 `source` 层的位置上造 `target` 层的结点。进孩子时位置前面添一段，`positionLayer` 定义性不变，
所以把造结点的办法传下去，不搬运。`left + top`：后继层号上是根位置的结点；极限层号上各支的 `top` 互不为第一位置，
取逐项累加。

```agda
accumulate : ∀ {Value : Set} → (ℕ → Value → Value) → Value → ℕ → Value
accumulate step start zero = start
accumulate step start (suc n) = step n (accumulate step start n)

NodeBuilder : Level → Level → Set
NodeBuilder target source =
  (position : Position source) → (PositionTree source position → RawTree target) → RawTree target

addWithBuilder : ∀ {target} source → NodeBuilder target source →
  RawTree target → RawTree source → RawTree target
addWithBuilder source build left Raw.zero = left
addWithBuilder source build left (Raw.suc right) =
  Raw.suc (addWithBuilder source build left right)
addWithBuilder source build left (Raw.lim sequence) =
  Raw.lim (λ n → addWithBuilder source build left (sequence n))
addWithBuilder source build left (Raw.layerLimit position branch) =
  build position (λ index → addWithBuilder source build left (branch index))
addWithBuilder zero build left (Raw.embed () right)
addWithBuilder (suc predecessor) build left (Raw.embed _ right) =
  addWithBuilder predecessor (λ position → build (inj₂ position)) left right
addWithBuilder (lim sequence) build left (Raw.embed n right) =
  addWithBuilder (sequence n) (λ position → build (n , position)) left right
addWithBuilder (layerLimit indexLevel branchLevel) build left (Raw.embed (index , legal) right) =
  addWithBuilder (branchLevel index) (λ position → build (index , legal , position)) left right
addWithBuilder zero build left Raw.top = Raw.suc left
addWithBuilder (suc predecessor) build left Raw.top =
  build (inj₁ tt) (λ index → addWithBuilder predecessor (λ position → build (inj₂ position)) left index)
addWithBuilder (lim sequence) build left Raw.top =
  Raw.lim (λ n → accumulate
    (λ stage partial → addWithBuilder (sequence stage) (λ position → build (stage , position)) partial Raw.top)
    left (suc n))
addWithBuilder (layerLimit indexLevel branchLevel) build left Raw.top = Raw.suc left

plus : ∀ level → RawTree level → RawTree level → RawTree level
plus level = addWithBuilder level Raw.layerLimit
```
