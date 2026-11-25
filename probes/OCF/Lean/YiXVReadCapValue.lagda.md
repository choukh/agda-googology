# YiXVReadCapValue
> 验收文件。档位：编译定理。每个实际源 x 的 ψ⁰(cap x) 值上界，出口为 ReadCapBound.upper；不是 G x 的上界。
> 复用 Level、CountableFold/MapCompare 与 ReadOmega 的构造，完整实例见代码；未接实际源世界或原外层 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadCapValue where
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiXVLvlSteps using (read-strong)
import OCF.Lean.YiXVReadOmega as O
import OCF.Lean.YiXVCountableZeroRead as Z
import OCF.Lean.YiXVReadCapBound as B
import OCF.Lean.YiXVReadEnv as E
value : ∀ x → L.ψ⁰ (O.cap x) ≼ L.ψ⁰ (B.upper x)
value x = Z.mono {κ = T.lvl x} {a = L.suc (T.lvl x)}
  (read-strong x) (read-strong x) (E.zero-bound x) (λ q → L.suc q) (B.bound x)
actual : L.ψ⁰ (O.cap (S.suc S.zero)) ≼ L.ψ⁰ (B.upper (S.suc S.zero))
actual = value (S.suc S.zero)
```
