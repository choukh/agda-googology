# 第一档成品候选的完整接口
> 成品候选入口：在三项最小入口上补充塔项、View 部分递归、对象步进、值合法性与 FGH 值一致性。
> 本入口不新增数学内容，不作 EBO 序数值或增长率的验收。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPXFull where

open import OCF.Lean.YiPXEntry public
open import OCF.Lean.YiMTTab public using (twᶻ)
open import OCF.Lean.YiVWWf public using (wf; vrec; objStep)
open import OCF.Lean.YiVWVal public using (val-leg)
open import OCF.Lean.YiVWFGH public using (FGH-val)
```
