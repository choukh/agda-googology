# 从已有 BTBO 基座重新起步：值验收锚点

本文件只串接已有定理，不新增候选，不改变 `src` 的 BTBO。
源 BTBO 已与标为 EBO 第 2 级的参照互相 `≼`，即值为
$\psi_0(\Omega_\Omega)$。既有合法闭项 `SumOneClosed.T₁` 严格超过此基座。
这不是本轮新增强度；它明确后续研究应从哪里起步。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBORestartAnchor where

open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Align.Level using (suc)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; s≼s)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOFull using (BTBO≈)
import OCF.Align.NoCumsum as N
import OCF.Align.EBO as E
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.Label using (BTBO-label)
open import OCF.Align.TLRuleVar using (trA)
open import OCF.Align.SumOneClosed using (T₀; T₁)
open import OCF.Align.SumOneAccept using (T₀≈; step-T₁)

source≈reference : tr₀ Ord-Ord.BTBO ≈ᵛ N.BTBOᴵ
source≈reference = BTBO≈

reference-is-EBO2 : Lab N.BTBOᴵ (E.EBOψ 2)
reference-is-EBO2 = BTBO-label

source≈T₀ : tr₀ Ord-Ord.BTBO ≈ᵛ trA T₀
source≈T₀ =
  ≼-trans (proj₁ BTBO≈) (proj₂ T₀≈) ,
  ≼-trans (proj₁ T₀≈) (proj₂ BTBO≈)

source<T₁ : suc (tr₀ Ord-Ord.BTBO) ≼ trA T₁
source<T₁ = ≼-trans (s≼s (proj₁ BTBO≈)) step-T₁
```

这里的源 BTBO 验收是序数值验收，不是源树与 EBO 基本列逐项一致，
也没有由此宣称 FGH 相同。`T₁` 的结论是严格下界，不是
$\psi_0(\Omega_{\Omega+1})$ 的等值或上界。

下一项未填的值义务是：将 EBO 第 3 级
$\psi_0(\Omega_{\Omega_\Omega})$ 的完整参照送入合法树侧闭项，
继而对全塔给统一覆盖。上面的严格后继下界不蕴涵第 3 级覆盖；
NoCumsum 的整条 γ 链在这里已经构成第 2 级，不能把继续该链
当作已覆盖 EBO 全塔。旧 `EndLowAccept.treeE2≅` 将实际良基构造的
第 2 级与同一 `N.BTBOᴵ` 相接；本锚点不为重复该结论引入归档依赖。
