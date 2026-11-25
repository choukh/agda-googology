# `SumOne.T₁` 的上界: 入口

> **验收文件. 判决: PARTIAL.** 对象 `SumOneClosed.T₁`, 参照 `fr CtxMonoAccept.Ref` (标签 $\psi_0(\Omega_{\Omega+1})$). 不改 `SumOne*` 的定义.
>
> - **定理 (序数值验收, 两站):** `Sω-vlab`: 第一次 `Step` 之后的位置的值是 $\psi_0(\Omega_\Omega+1)$; `S¹-vlab`: 第一个带上下文的回灌里走完第 0 层的位置的值是 $\psi_0(\Omega_\Omega+\Omega_1)$. 两站都是 `T₁` 的位置, 都在参照之下; 下界 `low¹-T₁`.
> - **定理 (参照侧):** `lab-mono`: 标准形的带标签的树按记号的序排列.
> - **条件定理:** `upper-lab : StageBelow → Upper` (每一段被某个小于 $\psi_0(\Omega_{\Omega+1})$ 的标准形的带标签的树压住, 则上界成立); `fb-upper : CellStep → trA Fb₁ ≼ T2ᴸ`.
> - **未走通, 不是否定:** `T₁ ≼ 参照`. 第一个未定的位置是 `S²` (第 0 格走完第 1 层); `upper→Open₂` 说上界成立时它必须在参照之下. 没有超值或掉值的见证.
>
> 全部 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumOneUp where

open import OCF.Align.SumOneUpStation using (Sω; Sω≈; Sω-vlab; Sω≤T₁; low-T₁) public
open import OCF.Align.SumOneUpCell using (Cκ; Fb₁; v₀≡; Fb₁≤T₁; cell≼T₁) public
open import OCF.Align.SumOneUpChain using (G; G-mono; module Run₀; S¹; S¹≈; S¹-vlab; S¹≤T₁; low¹-T₁) public
open import OCF.Align.SumOneUpRed using (Ref₁; T2≼Ref; Sω≼Ref; S¹≼Ref; CellStep; cell₀; fb-upper; fb-ref; S²; Open₂; upper→Open₂; StageUp; upper; T₁≇) public
open import OCF.Align.SumOneUpMono using (lab-mono; Below; below→ref; StageBelow; upper-lab; Sω-below; S¹-below; S²-target; S²-target→) public
```
