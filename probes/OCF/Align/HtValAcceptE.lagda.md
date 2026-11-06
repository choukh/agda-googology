# `T-Ω` 的值: 验收, 经桥 `⟪_⟫`

> **验收文件.** 读 `EndLowAccept` (记号, 参照树 `treeE`). 入口 [HtVal](HtVal.lagda.md). 只是把 [HtValAccept](HtValAccept.lagda.md) 的条件定理经 `EndLowAccept.⟪⟫≅trA` 搬到桥 `⟪_⟫` 上, 并对上参照树 `treeE 2` (`treeE2≅ : treeE 2 ≅ BTBOᴵ`). 档与前提同 `HtValAccept`: 条件定理.
>
> 编译要归档拷贝 (同 [EndLow](EndLow.lagda.md) 文末).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtValAcceptE where

open import Data.Product using (_,_)
open import OCF.Align.Level using (≅-sym)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≅→≼)
open import OCF.Align.NoCumsum using (BTBOᴵ)
open import OCF.Align.EndLowAccept using (⟪_⟫; ⟪⟫≅trA; treeE; treeE2≅)
open import OCF.Align.HtFeedClosed using (T-Ω)
open import OCF.Align.HtValAccept using (PortLo; PortHi; SwapLo; SwapHi; lo; hi)

loᴱ : PortLo → SwapLo → treeE 2 ≼ ⟪ T-Ω ⟫
loᴱ pl sl = ≼-trans (≅→≼ treeE2≅) (≼-trans (lo pl sl) (≅→≼ (≅-sym (⟪⟫≅trA T-Ω))))

hiᴱ : PortHi → SwapHi → ⟪ T-Ω ⟫ ≼ treeE 2
hiᴱ ph sh = ≼-trans (≅→≼ (⟪⟫≅trA T-Ω)) (≼-trans (hi ph sh) (≅→≼ (≅-sym treeE2≅)))

B≼ᴱ : PortLo → SwapLo → BTBOᴵ ≼ ⟪ T-Ω ⟫
B≼ᴱ pl sl = ≼-trans (lo pl sl) (≅→≼ (≅-sym (⟪⟫≅trA T-Ω)))
```
