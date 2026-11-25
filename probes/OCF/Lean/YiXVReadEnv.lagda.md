# YiXVReadEnv
> 验收文件。档位：编译定理。实际读回层号的后继是零下标的显式公共界，极限处复用原 sim-s。
> 复用 Level、CountableFold/MapCompare 与 ReadOmega 的构造，完整实例见代码；未接实际源世界或原外层 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadEnv where
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLSTw1 as T
import OCF.Lean.YiXVLvlLiteral as P
import OCF.Align.Level as L
zero-bound : ∀ x → L.zero L.<ᴵ L.suc (T.lvl x)
zero-bound S.zero = L.zero
zero-bound (S.suc x) = L.suc (zero-bound x)
zero-bound (S.lim f a) = L.suc (L.lim 1 (L.sim-s (P.step (a 0)) (zero-bound (f 0))))
zero-bound (S.Ω () g)
zero-bound (S.up x () y e)
actual : L.zero L.<ᴵ L.suc (T.lvl (S.suc S.zero))
actual = zero-bound (S.suc S.zero)
```
