# YiRead 与 YiNext 的对应

**非验收文件。判决：编译定理 `towerCorresponds`、`ΛCorresponds`，无前提。** 新块 [YiReadCore](YiReadCore.lagda.md) 的塔与 `Λ` 跟旧块 [YiNextCore](YiNextCore.lagda.md) 的 `tw`、`Λ` 处在结构对应 `Corresponds` 里。
`Corresponds` 是两边层号之间的逐构造子关系，Ω 结点要求在对应的分支下标上分支对应；树、位置、孩子的对应随它一起递归定义。
不是相等，也不是翻译函数：翻译函数在 Ω 结点的孩子上要来回复原 (如 `lim (λ n → from (to (f n))) ≡ lim f`)，判断：不用函数外延做不到。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiReadCheck where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import OCF.Lean.YiNextCore as Old
import OCF.Lean.YiReadCore as New
```

## 1 对应关系

旧侧的树、位置、孩子用等式 `old ≡ 构造子 …` 给出形状，证明里匹配 `refl` 即可，不必逐对列出构造子不符的情形。
位置与孩子里的合法性证明不参与对应。

```agda
data Corresponds : New.Level → Old.LF → Set
TreeCorresponds : ∀ {level oldLevel} → Corresponds level oldLevel →
  New.RawTree level → Old.Raw oldLevel → Set
PositionCorresponds : ∀ {level oldLevel} → Corresponds level oldLevel →
  New.Position level → Old.Pre oldLevel → Set
PositionTreeCorresponds : ∀ {level oldLevel} (same : Corresponds level oldLevel)
  {position oldPosition} → PositionCorresponds same position oldPosition →
  New.PositionTree level position → Old.Lay.A (Old.Lo oldLevel oldPosition) → Set
ChildCorresponds : ∀ {level oldLevel} → Corresponds level oldLevel →
  New.Child level → Old.Kid oldLevel → Set
ChildTreeCorresponds : ∀ {level oldLevel} (same : Corresponds level oldLevel)
  {child oldChild} → ChildCorresponds same child oldChild →
  New.ChildTree level child → Old.Lay.A (Old.KS oldLevel oldChild) → Set

data Corresponds where
  zero : Corresponds New.zero Old.zero
  suc : ∀ {level oldLevel} → Corresponds level oldLevel →
    Corresponds (New.suc level) (Old.suc oldLevel)
  lim : ∀ {sequence oldSequence} → (∀ n → Corresponds (sequence n) (oldSequence n)) →
    Corresponds (New.lim sequence) (Old.lim oldSequence)
  layerLimit : ∀ {indexLevel oldIndexLevel branchLevel oldBranchLevel}
    (sameIndexLevel : Corresponds indexLevel oldIndexLevel) →
    (∀ index oldIndex → TreeCorresponds sameIndexLevel index oldIndex →
       Corresponds (branchLevel index) (oldBranchLevel oldIndex)) →
    Corresponds (New.layerLimit indexLevel branchLevel) (Old.lc oldIndexLevel oldBranchLevel)

TreeCorresponds same New.Raw.zero oldTree = oldTree ≡ Old.G.zero
TreeCorresponds {oldLevel = oldLevel} same (New.Raw.suc tree) oldTree =
  Σ (Old.Raw oldLevel) λ oldSubtree →
  (oldTree ≡ Old.G.suc oldSubtree) × TreeCorresponds same tree oldSubtree
TreeCorresponds {oldLevel = oldLevel} same (New.Raw.lim sequence) oldTree =
  Σ (ℕ → Old.Raw oldLevel) λ oldSequence →
  (oldTree ≡ Old.G.lim oldSequence) × (∀ n → TreeCorresponds same (sequence n) (oldSequence n))
TreeCorresponds {oldLevel = oldLevel} same (New.Raw.layerLimit position branch) oldTree =
  Σ (Old.Pre oldLevel) λ oldPosition →
  Σ (Old.Lay.A (Old.Lo oldLevel oldPosition) → Old.Raw oldLevel) λ oldBranch →
  (oldTree ≡ Old.G.lc oldPosition oldBranch) ×
  Σ (PositionCorresponds same position oldPosition) λ samePosition →
    ∀ index oldIndex → PositionTreeCorresponds same samePosition index oldIndex →
      TreeCorresponds same (branch index) (oldBranch oldIndex)
TreeCorresponds {oldLevel = oldLevel} same (New.Raw.embed child tree) oldTree =
  Σ (Old.Kid oldLevel) λ oldChild →
  Σ (Old.Lay.A (Old.KS oldLevel oldChild)) λ oldSubtree →
  (oldTree ≡ Old.G.em oldChild oldSubtree) ×
  Σ (ChildCorresponds same child oldChild) λ sameChild →
    ChildTreeCorresponds same sameChild tree oldSubtree
TreeCorresponds same New.Raw.top oldTree = oldTree ≡ Old.G.top

PositionCorresponds zero () oldPosition
PositionCorresponds (suc same) (inj₁ root) oldPosition = oldPosition ≡ inj₁ root
PositionCorresponds (suc {oldLevel = oldLevel} same) (inj₂ position) oldPosition =
  Σ (Old.Pre oldLevel) λ oldRest →
  (oldPosition ≡ inj₂ oldRest) × PositionCorresponds same position oldRest
PositionCorresponds (lim {oldSequence = oldSequence} same) (n , position) oldPosition =
  Σ (Old.Pre (oldSequence n)) λ oldRest →
  (oldPosition ≡ (n , oldRest)) × PositionCorresponds (same n) position oldRest
PositionCorresponds (layerLimit {oldIndexLevel = oldIndexLevel} {oldBranchLevel = oldBranchLevel}
    sameIndexLevel sameBranchLevel) (headIndex , _ , position) oldPosition =
  Σ (Old.Raw oldIndexLevel) λ oldHeadIndex →
  Σ (Old.Lgl oldIndexLevel oldHeadIndex) λ oldHeadLegal →
  Σ (Old.Pre (oldBranchLevel oldHeadIndex)) λ oldRest →
  (oldPosition ≡ (oldHeadIndex , oldHeadLegal , oldRest)) ×
  Σ (TreeCorresponds sameIndexLevel headIndex oldHeadIndex) λ sameHead →
    PositionCorresponds (sameBranchLevel headIndex oldHeadIndex sameHead) position oldRest

PositionTreeCorresponds zero {()} _ _ _
PositionTreeCorresponds (suc same) {inj₁ root} refl index oldIndex =
  TreeCorresponds same index oldIndex
PositionTreeCorresponds (suc same) {inj₂ position} (oldRest , refl , samePosition) index oldIndex =
  PositionTreeCorresponds same samePosition index oldIndex
PositionTreeCorresponds (lim same) {n , position} (oldRest , refl , samePosition) index oldIndex =
  PositionTreeCorresponds (same n) samePosition index oldIndex
PositionTreeCorresponds (layerLimit sameIndexLevel sameBranchLevel) {headIndex , _ , position}
    (oldHeadIndex , oldHeadLegal , oldRest , refl , sameHead , samePosition) index oldIndex =
  PositionTreeCorresponds (sameBranchLevel headIndex oldHeadIndex sameHead) samePosition index oldIndex

ChildCorresponds zero () oldChild
ChildCorresponds (suc same) _ _ = ⊤
ChildCorresponds (lim same) n oldChild = oldChild ≡ n
ChildCorresponds (layerLimit {oldIndexLevel = oldIndexLevel} sameIndexLevel sameBranchLevel)
    (index , _) oldChild =
  Σ (Old.Raw oldIndexLevel) λ oldIndex → Σ (Old.Lgl oldIndexLevel oldIndex) λ oldLegal →
  (oldChild ≡ (oldIndex , oldLegal)) × TreeCorresponds sameIndexLevel index oldIndex

ChildTreeCorresponds zero {()} _ _ _
ChildTreeCorresponds (suc same) _ tree oldTree = TreeCorresponds same tree oldTree
ChildTreeCorresponds (lim same) {child = n} refl tree oldTree = TreeCorresponds (same n) tree oldTree
ChildTreeCorresponds (layerLimit sameIndexLevel sameBranchLevel) {index , _}
    (oldIndex , oldLegal , refl , sameIndex) tree oldTree =
  TreeCorresponds (sameBranchLevel index oldIndex sameIndex) tree oldTree
```

## 2 读回保持对应；塔与 Λ

```agda
readBackCorresponds : ∀ {level oldLevel} (same : Corresponds level oldLevel) tree oldTree →
  TreeCorresponds same tree oldTree → Corresponds (New.readBack level tree) (Old.up oldLevel oldTree)
readBackLayerLimitCorresponds : ∀ {level oldLevel} (same : Corresponds level oldLevel)
  {position oldPosition} (samePosition : PositionCorresponds same position oldPosition) branch oldBranch →
  (∀ index oldIndex → PositionTreeCorresponds same samePosition index oldIndex →
     Corresponds (branch index) (oldBranch oldIndex)) →
  Corresponds (New.readBackLayerLimit level position branch) (Old.upN oldLevel oldPosition oldBranch)
childReadBackCorresponds : ∀ {level oldLevel} (same : Corresponds level oldLevel)
  {child oldChild} (sameChild : ChildCorresponds same child oldChild) tree oldTree →
  ChildTreeCorresponds same sameChild tree oldTree →
  Corresponds (New.Layer.readBack (New.childLayer level child) tree)
              (Old.Lay.rd (Old.KS oldLevel oldChild) oldTree)
readBackTopCorresponds : ∀ {level oldLevel} → Corresponds level oldLevel →
  Corresponds (New.readBackTop level) (Old.upT oldLevel)

readBackCorresponds same New.Raw.zero _ refl = zero
readBackCorresponds same (New.Raw.suc tree) _ (oldSubtree , refl , sameSubtree) =
  suc (readBackCorresponds same tree oldSubtree sameSubtree)
readBackCorresponds same (New.Raw.lim sequence) _ (oldSequence , refl , sameSequence) =
  lim (λ n → readBackCorresponds same (sequence n) (oldSequence n) (sameSequence n))
readBackCorresponds {level} {oldLevel} same (New.Raw.layerLimit position branch) _
    (oldPosition , oldBranch , refl , samePosition , sameBranch) =
  readBackLayerLimitCorresponds same samePosition
    (λ index → New.readBack level (branch index)) (λ oldIndex → Old.up oldLevel (oldBranch oldIndex))
    (λ index oldIndex sameIndex →
       readBackCorresponds same (branch index) (oldBranch oldIndex) (sameBranch index oldIndex sameIndex))
readBackCorresponds same (New.Raw.embed child tree) _ (oldChild , oldSubtree , refl , sameChild , sameSubtree) =
  childReadBackCorresponds same sameChild tree oldSubtree sameSubtree
readBackCorresponds same New.Raw.top _ refl = readBackTopCorresponds same

readBackLayerLimitCorresponds zero {()} _ _ _ _
readBackLayerLimitCorresponds (suc same) {inj₁ root} refl branch oldBranch sameBranch =
  layerLimit same sameBranch
readBackLayerLimitCorresponds (suc same) {inj₂ position} (oldRest , refl , samePosition)
    branch oldBranch sameBranch =
  readBackLayerLimitCorresponds same samePosition branch oldBranch sameBranch
readBackLayerLimitCorresponds (lim same) {n , position} (oldRest , refl , samePosition)
    branch oldBranch sameBranch =
  readBackLayerLimitCorresponds (same n) samePosition branch oldBranch sameBranch
readBackLayerLimitCorresponds (layerLimit sameIndexLevel sameBranchLevel) {headIndex , _ , position}
    (oldHeadIndex , oldHeadLegal , oldRest , refl , sameHead , samePosition) branch oldBranch sameBranch =
  readBackLayerLimitCorresponds (sameBranchLevel headIndex oldHeadIndex sameHead) samePosition
    branch oldBranch sameBranch

childReadBackCorresponds zero {()} _ _ _ _
childReadBackCorresponds (suc same) _ tree oldTree sameTree =
  readBackCorresponds same tree oldTree sameTree
childReadBackCorresponds (lim same) {child = n} refl tree oldTree sameTree =
  readBackCorresponds (same n) tree oldTree sameTree
childReadBackCorresponds (layerLimit sameIndexLevel sameBranchLevel) {index , _}
    (oldIndex , oldLegal , refl , sameIndex) tree oldTree sameTree =
  readBackCorresponds (sameBranchLevel index oldIndex sameIndex) tree oldTree sameTree

readBackTopCorresponds zero = suc zero
readBackTopCorresponds (suc same) = layerLimit same (readBackCorresponds same)
readBackTopCorresponds (lim same) = lim (λ n → readBackTopCorresponds (same n))
readBackTopCorresponds (layerLimit sameIndexLevel sameBranchLevel) =
  layerLimit sameIndexLevel (λ index oldIndex sameIndex →
    readBackTopCorresponds (sameBranchLevel index oldIndex sameIndex))

towerCorresponds : ∀ n → Corresponds (New.tower n) (Old.tw n)
towerCorresponds zero = zero
towerCorresponds (suc n) = readBackTopCorresponds (towerCorresponds n)

ΛCorresponds : Corresponds New.Λ Old.Λ
ΛCorresponds = lim towerCorresponds
```

对照：关系不是处处成立的，构造子不符的层号没有对应。

```agda
zeroNotSuccessor : Corresponds New.zero (Old.suc Old.zero) → ⊥
zeroNotSuccessor ()
```
