# 固定 q=2 的 ψ₀(Ω_Ω+1) 值下界
验收文件；bound 把已编译的实际分支值比较换成该单一参照项的下界，hNext 为闭 HC。
不声称 FirstMissing 或新增终点强度；原 q=2、baseᴱ3 与 betaᴱ3 不变。
来源：YiFRStations.k2、YiKCSem.sem→M⁰、YiKVRel.G⁰.m-next 与 YiMSValue.value-next。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMSValueRef where
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiFRStations as FS
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiRefTw2 as R2
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
open import OCF.Align.EboLeanBase using (NF; GB; n[]; nf-ψ; Ctbl; c∷; c[]; InG; gp; gtl; gh; gw; gc)
open import OCF.Align.EboLean3Base using (nf-suc)
open import OCF.Lean.YiExInst using (back; tree-back)
open import OCF.Align.Value using (_≼_; ≼-trans)
open import OCF.Lean.YiMSValue using (β; out; value-next)
tNext = E.ψ [] (E.sucT (E.ΩTower 2)) ∷ []
β-lower : (h : E.HC (E.EBOψ 2)) → R2.Rt h ≼ K.readRW (proj₁ β)
β-lower h = ≼-trans (SI.toL-tree h) (FS.k2 (SI.conv h))
mβ : K.M⁰ (E.EBOψ 2) (proj₁ β)
mβ = CS.sem→M⁰ (ET.hc-tower 2) (proj₁ β) (β-lower (ET.hc-tower 2))
mNext : K.M⁰ tNext (proj₁ (O.next⁺ β))
mNext = K.G⁰.m-next {t = tNext} {p = E.ψ [] (E.ΩTower 2)} β refl (λ n → refl) mβ
bound : (h : SI.E.HC tNext) → SI.E.tree h ≼ K.readRW out
bound h = ≼-trans (tree-back h) (≼-trans (K.lower⁰ mNext (back h)) value-next)
GNext : GB [] (E.sucT (E.ΩTower 2)) (E.sucT (E.ΩTower 2))
GNext (gp (gh _)) = E.[]<
GNext (gp (gw _ i)) = subst (λ z → z E.<ᵀ E.sucT (E.ΩTower 2)) (sym (ET.G0-tower 1 i)) E.[]<
GNext (gp (gc _ ()))
GNext (gtl (gp (gh _))) = E.[]<
GNext (gtl (gp (gw _ ())))
GNext (gtl (gp (gc _ ())))
GNext (gtl (gtl ()))
nfNext : NF tNext
nfNext = nf-ψ n[] (nf-suc (ET.nf-ΩT 2)) GNext
opaque
  hNext : SI.E.HC tNext
  hNext = SI.conv (ET.hc nfNext (c∷ c[]))
```
