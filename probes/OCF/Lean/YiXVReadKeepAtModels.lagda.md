# YiXVReadKeepAtModels
> 验收文件。档位：编译定理。同一下标在自然极限的不同字面路径上的完整参照节点实例。
> 从 YiXVSourceAffine*、ReadFamily 与原 Level 推广，参照侧重用 CountableFold/Retain；未交完整世界 up/node 输出、外层 n≥2 界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadKeepAtModels where
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
q : L.zero L.<ᴵ L.ωᴵ
q = L.lim 1 L.zero
r : L.zero L.<ᴵ L.ωᴵ
r = L.lim 2 (L.suc L.zero)
σ : L.Simᴵ (L.suc L.zero) L.ωᴵ
σ L.zero = q
σ (L.suc ())
f : L.U L.zero (L.<→◃ q) → L.Ordᶜ L.ωᴵ
f u = L.add L.zero (λ t → σ (L.suc t)) (L.out (L.<→◃ q) u)
actual : A.Gd (L.limᵢ q f)
actual = Add.good {σ = σ} A.Layer.gz A.oneΩ
```
