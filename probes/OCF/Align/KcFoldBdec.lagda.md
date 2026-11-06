# 种类塔上的一级折叠 (四): 接口 §2 的实例 (导入否定一路的正面定理)

> 不含记号. 入口 [KcFold](KcFold.lagda.md), 接口 [KcFoldIf](KcFoldIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 否定一路 (前缀 `NegKcFold`, 主审已复核) 对同一接口证了可入判定在一切站, 一切 `Lev c`, 极限 `KΛc` 上的实例 (`NegKcFoldDec.bdecTower`, `bdecΛ`, `bdecLev`; 核心 `Shr.shr`, 判据 `TopK`: 每个种类在每个世界里的顶坐标就是界本身). 本篇只导入, 不重写. 本路的塔与闭项**不用**可入判定 (级顶读回不读外层世界), 所以这一条只说明接口 §2 的前提在一切站可满足, 不进闭项.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KcFoldBdec where

open import OCF.Align.HtTowerTy
open import OCF.Align.LvKtIf using (KΛc)
open import OCF.Align.KcFoldIf
open import OCF.Align.NegKcFoldDec using (bdecTower; bdecΛ; bdecLev)

bdecT : BDecTower
bdecT = bdecTower

bdecL : BDecK KΛc
bdecL = bdecΛ

bdecLv : ∀ {S : KS} (x : HB S) → BDecK (Lev x)
bdecLv = bdecLev
```
