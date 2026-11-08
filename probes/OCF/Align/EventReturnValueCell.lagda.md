# 真实 κ₁ 首格中的 κ₀ 闭包迁回

只校准原运行器的一个结构化实例：κ₁ 分支是 κ₀ 闭包，后者的
分支为零。初状态含原 `Stp`，不是把事件增量手设为零。
这不是任意 `D₂` 的自然性，也不涵盖读取坐标或历史的任意函数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnValueCell where

open import Data.Nat using (zero)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead
import OCF.Align.EvFoldClosed as Closed
import OCF.Align.EvFoldNew as New
open import OCF.Align.EventReturnIf using (ReturnAt)
import OCF.Align.EventReturnBuild as Return

module R = Closed.At Closed.three tt (hsuc (hsuc hself)) (hsuc hself)
open R

branch : Bu Closed.three Closed.W₁
branch q l = nε κ₀ tt (λ _ _ → n0)

state : St Closed.W₁
state = Y₀ ⊕⟨ (tt , tt) ⟩ Stp Y₀

cell : Clε Closed.W₁ Closed.W₁ Closed.three
cell = κcε accᴸ κ₁ branch ≤rf (tt , tt) hself Act n0 state zero

output : D₂ (Closed.one , hc cell)
output = yc (κΔε accᴸ branch ≤rf (tt , tt) hself Act cell) (τ₂ (tt , tt))

model : ∀ {W} → D₂ W
model = n0 ⨾ ((n0 ⨾ n0) ⨾ nε κ₀ tt (λ _ _ → n0))

output-shape : output ≡ model
output-shape = refl

returned-read : ∀ b →
  rd₂ (tt , tt) b output ≡
  rd₂ {Closed.W₁} (tt , tt) b (drp₂ output)
returned-read b = refl
```

初次 κ₁ 增量确实含 σH 节点；这项使用旧 `first-new` 的实际状态
实例，而不是用新模型推断原运行。读回迁移前后相等给出全部分支
及基本列一致，仍不提供任意高层上下文的观察同余。

```agda
module N = New.Top Closed.three tt (hsuc (hsuc hself)) (hsuc hself)

event-nontrivial : New.HasH (proj₁ (RB κ₁ (tt , tt) (zRL κ₁ state)))
event-nontrivial = N.first-new (tt , tt) Y₀ Y₀

returned : D₂ Closed.W₁
returned = ReturnAt.move (Return.actual κ₁) tt (hsuc hself)
  (hsuc hself) hself output

contract-read : ∀ b → rd₂ (tt , tt) b output ≡ rd₂ (tt , tt) b returned
contract-read = returned-read
```
