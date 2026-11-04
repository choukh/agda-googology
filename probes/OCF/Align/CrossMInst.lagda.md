# 跨段 (四): 塔的实例

> 入口 [CrossM](CrossM.lagda.md). **判决: HOLDS (编译过, 无条件).** `𝒯 : Node`: 分支对一切 $M$ 是 `Tᵒ M 0`; 单调性由 `step≺` (上移加严格增长) 给出; `val≼T`: 第 0 行的值不低于高度的值 (`grow` 加 `rk≼`). 全部不按 $M$ 定制.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossMInst where

open import OCF.Free.Level hiding (up)
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Force using (forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode
open import OCF.Align.LadderOrdCert using (ev₀; Tᵖ; Gᵖ; growᵖ)
open import OCF.Align.CrossMUpTree
open import OCF.Align.CrossMNode
```

全部写成 `Gᵖ M end zero` 的字面形式. 这不是风格: 检查器比较 `lvG` 或 `forceᴺ` 的两个不同写法时要先化简证书项, 那是整条闭包定理, `Gᵒ` 的版本 5 分钟超过 25G 没有结果.

```agda
𝒯 : Node
𝒯 = node (λ M → toZ (Tᵖ M end zero ev₀ zero)) (λ M → Gᵖ M end zero) (λ M N → ≺→⊑ (step≺ M N))

val≼T : ∀ M → val M ≼ lvG (Gᵖ M end zero)
val≼T M = rk≼ M zero (λ p → lvG (Gᵖ M p zero))
  (λ p q r → toLevel-≺ (forceᴺ-HS _ (Gᵖ M p zero)) (forceᴺ-HS _ (Gᵖ M q zero)) (growᵖ M {p} {q} r))
  (λ x → z≼) end

module Fixᵗ = Fix (λ M → toZ (Tᵖ M end zero ev₀ zero)) (λ M → Gᵖ M end zero) step≺ val≼T
```
