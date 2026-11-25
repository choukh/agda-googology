# 旧保持接口的指定 Ω 树值出口
验收接口，读记号；Family 明确列出带读回证据的请求，不量化全部合法层号。
Law 是 Leaf、LowKeep 及出口证据组合后的值陈述；不新增树侧行律。
两个实例不推出任意 Family 的 Law；与旧接口的接线见 YiNIBridge。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNIIface where
open import Data.List using ([]; _∷_)
import OCF.Lean.YiNIDomain as D
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiRefTw2 as RT
import OCF.Align.EboLeanDef as E
open import OCF.Align.Value using (_≼_)

record Request : Set where
  field
    node : D.Node
    index : E.T
    reads : GR.Rd (D.Node.layer node) index
  reference : E.T
  reference = E.ψ [] (E.Ωt index) ∷ []
  field
    nonempty : E.HC reference

record Family : Set₁ where
  field
    Member : Set
    request : Member → Request

module At (d : Request) where
  open Request d
  Value : Set
  Value = RT.Rt nonempty ≼ K.readRW (D.output node)
  Certificate : Set
  Certificate = K.M⁰ reference (D.output node)

Law : Family → Set
Law d = (a : Family.Member d) → At.Value (Family.request d a)
```
