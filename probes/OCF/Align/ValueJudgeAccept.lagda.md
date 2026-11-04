# 值判据 (十三): 对照标签 (导入闭包不干净)

> **判决: HOLDS (只有再导出, 不干净).** 底座. 结论写在 [ValueJudge](ValueJudge.lagda.md). **这个文件读记号, 不进判据.** 只把现成的标签定理放在一起, 说明下界那一侧确实带标签: `T₀∞` 对应 `label-∞0` ($\psi_0(\Omega_{\psi_1(1)})$), 有限高度的第 0 行对应 `label-fin`. 判据的定义和定理都不依赖本文件. 标签在克隆世界 (`LadderInfW*`), 与主线的联系是代码逐字相同和有限测试, 这一点不变.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValueJudgeAccept where

open import OCF.Align.LadderInfAccept public using (label-∞0; label-fin)
```
