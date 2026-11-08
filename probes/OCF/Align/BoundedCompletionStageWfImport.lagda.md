# WfFsn导入基线

编译实验：空导入在 6G 下退出 0。仅用于定位堆耗尽是否由空导入触发，没有数学或值验收结论，不计数学成果。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionStageWfImport where
import OCF.Align.WfFsn
```
