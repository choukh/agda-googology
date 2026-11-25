# 第 2 站保底成品的值下界
> 验收文件（读记号，不进成品）。档位：序数值下界，编译定理；不是互相 `≼`，不涉及上界。
> `low`、`low-all`：成品终点 `YiSHEntry.endᶻ`（`end-def`：定义上就是 `YiMTTab.EBOᶻ`）的读回不低于记号 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω) 沿基本列抽取的参照树，对参照的一切 `HC` 推导；`inst` 给非空实例。`btbo-low`：不低于 `src/OCF/BTBO` 的 BTBO 的值。
> 不证第 3 站 ψ₀(Ω_{Ω_Ω})，不证 ψ₀(Ω_{Ω₂})，不证 EBO 下界。来源：`YiFYRef.target-low`、`all-hc-low`、`instance-low`；`btbo-low` 是 `BTBOFull.BTBO≈` 与 `YiMTValue.btbo-EBOᶻ` 的复合。
> 读法：ψ₁(Ω_ω) 在 Ω 的算术下没有闭式，照原样写（判断：参数 Ω_ω ≥ Ω₂，超出 ψ₁(α) = Ω·ω^α 的适用范围；ψ₁(Ω_ω) 在 ε_{Ω+1} 与 Ω₂ 之间）。

参照项逐字写成记号的构造子：`ψ u a` 是 ψ_u(a)，`𝟏` 是 1，和是列表；即 ψ₀(Ω_Ω + ψ₁(Ω_ω) + ω)。`low` 与 `btbo-low` 用的读回是两份逐字相同的定义（`YiKVRel.readRW`、`YiBRValue.readRW`），沿用各自来源。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSHAccept where
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.Value using (_≼_; ≼-trans)
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiRefTw2 as RT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiBRValue as BR
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiMTValue as MV
import OCF.Lean.YiFYRef as FY
import OCF.Lean.YiSHEntry as N
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOFull using (BTBO≈)

end-def : N.endᶻ ≡ MT.EBOᶻ
end-def = refl

low : (h : E.HC (E.ψ [] (E.ψ (E.ψ (E.𝟏 ∷ []) [] ∷ []) [] ∷ E.ψ (E.𝟏 ∷ []) (E.ψ (E.ψ [] (E.𝟏 ∷ []) ∷ []) [] ∷ []) ∷ E.ψ [] (E.𝟏 ∷ []) ∷ []) ∷ []))
    → RT.Rt h ≼ K.readRW MT.EBOᶻ
low = FY.target-low

low-all : (h : SI.E.HC (E.ψ [] (E.ψ (E.ψ (E.𝟏 ∷ []) [] ∷ []) [] ∷ E.ψ (E.𝟏 ∷ []) (E.ψ (E.ψ [] (E.𝟏 ∷ []) ∷ []) [] ∷ []) ∷ E.ψ [] (E.𝟏 ∷ []) ∷ []) ∷ []))
        → SI.E.tree h ≼ K.readRW MT.EBOᶻ
low-all = FY.all-hc-low

inst : RT.Rt FY.hc-target ≼ K.readRW MT.EBOᶻ
inst = FY.instance-low

btbo-low : tr₀ Ord-Ord.BTBO ≼ BR.readRW MT.EBOᶻ
btbo-low = ≼-trans (proj₁ BTBO≈) MV.btbo-EBOᶻ
```
