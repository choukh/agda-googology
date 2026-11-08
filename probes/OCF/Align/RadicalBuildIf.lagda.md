# 单字段标记：先隔离可执行读法合同

这是替换原 Up 的第一切口，不是完整的新 Q 容器。mark 只存低层坐标，
不存 ι 生成的第二棵树。上下文执行合同暂不声称消除运行中的 ι：旧 sh
在普通分支产生 pι，而旧 runᶜ 会在那里重建 ι；这一点必须如实记账。
完整生成域与自产闭项证书尚不包含在本合同中，不能据此宣称压缩成功。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.RadicalBuildIf (𝕊 : HtB) where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Free.Floor using (Flr)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ordˢ)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdCx 𝕊
open import OCF.Align.LadderOrdStrict 𝕊 using (Up)

record Mark (m : Ht) {k ℓ : Ordᴵ} (r : k ◃₁ ℓ) (φ : Flr) (χ : Fv) : Set where
  constructor mark
  field
    coordinate : Q m k φ χ
open Mark public

record MarkExecution : Set where
  field
    execute : ∀ {m k ℓ φ χ} {r : k ◃₁ ℓ} → Cx m ℓ φ χ → Mark m r φ χ → Ordˢ zero
    exact : ∀ {m k ℓ φ χ} (r : k ◃₁ ℓ) (C : Cx m ℓ φ χ) (z : Q m k φ χ) →
      execute {r = r} C (mark z) ≡ runᶜ C (Up r z)
```
