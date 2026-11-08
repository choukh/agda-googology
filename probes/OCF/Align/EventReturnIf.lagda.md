# 事件读回与迁回：原运行器的最小合同

本接口固定原 `EvFold` 的两种事件、数据树与读回，并不另造运行器。
迁回只发生在事件自己的读回层及以下。读回层、当前目标都携带
同一最高层 Λ 内的字面位置；历史表改变不被误写成坐标下标判等。
结构迁回与值保持分开：后者尚须检验高阶分支对输入数据的相容。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnIf where

open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.CumReadCF using (A)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead using (RLay; RB; evRB)

-- κ 本身就是 (c , c ⊲[azero] b₁)，不用另加裸种类比较。
record ReturnAt (κ : Kᵉ) : Set₁ where
  field
    read : ∀ {W} → LgWε W → D (RLay κ) W →
           Σ (HB (Lev (proj₁ κ))) LgB
    read-exact : ∀ {W} (lW : LgWε W) x → read lW x ≡ RB κ lW x
    event : ∀ {W} → LgWε W → D (RLay κ) W → Ev
    event-exact : ∀ {W} (lW : LgWε W) x → event lW x ≡ evRB κ lW x
    move : ∀ {a : A} {H H′ : Hist} {Λ t} →
           LgB Λ → RLay κ ⊲[ a , H ] Λ → t ⊲[ a , H ] Λ →
           t ⊲[ a , H ] RLay κ → D t (a , H) → D t (a , H′)
```

`read-exact/event-exact` 排除以预给地板替代运行输出。
这份记录不包含“任意输出迁回后读回不变”，也不把它的实例当新强度。
两种旧事件的实例只是下一步推广的合同校准。
