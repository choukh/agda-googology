# 第 2 站保底成品入口
> 成品入口，只有导入与两个别名，不新增数学；导入闭包不含记号。汇出层号 `L` 与各层的树 `Tr`，折叠 `ψ` 配表 `rbᶻ`，终点闭项 `endᶻ`（定义上就是 `YiMTTab.EBOᶻ`），层号证据 `Ok-tw`、`Ok-Λ` 与折叠的单调 `mono`，内部 View，FGH 与大数 `bigᶻ`。
> 读法 ψ₀(Λ) 只是读法，不是成品的声称。成品不声称到 EBO，不声称 ψ₀(Ω_{Ω₂}) 或第 3 站 ψ₀(Ω_{Ω_Ω})。
> 值的下界（读记号的验收）见 [YiSHAccept](YiSHAccept.lagda.md)。起点是 [YiPXFull](YiPXFull.lagda.md)；这里另补层号与树的类型、折叠、表、层号证据、FGH 本身与大数，并不再汇出 `EBOᶻ` 这个名字。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSHEntry where

open import Data.Nat using (ℕ)
open import OCF.Lean.YiRWBlock public
  using (Sg; T; Lt; _⊢_◃_; L; Sh; Ch; Sig; Tr; zero; suc; lim; Ω; up; nd; sS; sL; sΩ; _⊕_; ↑; tw; Λ)
open import OCF.Lean.YiRWOps public using (T⁺; Tr⁺; Ωt)
open import OCF.Lean.YiRWPath public using (Pth; _≤_; z≤; Ok; OkS; Ok-tw; Ok-Λ)
open import OCF.Lean.YiRWFold public using (Base; B₀)
open import OCF.Lean.YiTBRow public using (RbS; Rb; ψ; mono)
open import OCF.Lean.YiMTTab public using (rbᶻ; ψ₀ᶻ; twᶻ)
open import OCF.Lean.YiMTTab using (EBOᶻ)
open import OCF.Lean.YiVWVal public using (V; val; _≼_; LegV; val-leg)
open import OCF.Align.BrwViewDef public using (BrwView)
open import OCF.Lean.YiVWView public using (SigY; VW; view; brwView)
open import OCF.Lean.YiVWWf public using (Part; Pt; Acc; wf; vrec; ObjStep; objStep)
open import OCF.Lean.YiVWFGH public using (FGH; FGHᵥ; FGH-val; fghᶻ)

endᶻ : Tr zero
endᶻ = EBOᶻ

bigᶻ : ℕ
bigᶻ = FGH endᶻ 99
```
