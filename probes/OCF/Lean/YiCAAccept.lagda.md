# 后续链点推进到第 0 行的末端接线
验收文件；条件定理：`YiCAStep.At.StepChain` 在 YiTZAccept 所用的颈结点证书 `CR.o-neck` 上成立，则 `UL.FirstRow`（`first-row`）；记号只在末端经 `YiTZAccept.from-cover` 读一次。
前提的证书是 `CR.o-neck`；它与 `YiTZLocal.o-neck` 不是定义相等（`refl` 检查不过，命题相等未判定），所以 Canonical 上已有的链点结果（`YiPTAll.advance`、`YiTNShift`）不能直接代入。
不否定什么；本件导入闭包含记号，不导入树侧证明。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCAAccept where
import OCF.Lean.YiC0Reduce as CR
import OCF.Lean.YiUTTwoLocal as UL
import OCF.Lean.YiTZAccept as Z
import OCF.Lean.YiCAStep as S

first-row : S.At.StepChain CR.o-neck → UL.FirstRow
first-row s = Z.from-cover (S.At.cover CR.o-neck s)
```
