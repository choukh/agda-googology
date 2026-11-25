# 零层孩子的 Ψ 小例
不读记号；编译定理覆盖 tw 1 的固定三个后继孩子，未外推不可数孩子。
来源：YiTVPsi.Finite；第 0 步临时试验的正式版本。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTMSmall where
open import Data.Product using (proj₁)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTVPsi as Q

c : B.Tr B.zero
c = B.suc (B.suc (B.suc B.zero))
v : V.V B.zero
v = V.val B.zero c
hv : V.LegV B.zero v
hv = V.val-leg B.zero c
small : Q.Ψ B.zero (P.Ok-tw 0) v hv V.≼ V.val B.zero (proj₁ (Q.Finite.fold c))
small = V.≼-refl _
g : B.Tr (B.tw 1)
g = proj₁ (O.upz {s = B.sΩ B.zero} {h = Q.Finite.h} c (O.Ωt (Q.Finite.h c)))
root-out : O.Tr⁺ B.zero
root-out = TB.ψ (B.tw 1) (P.Ok-tw 1) (MT.rbᶻ (B.tw 1)) (F.B₀ (B.tw 1))
  B.zero (P.z≤ (B.tw 1)) (O.Ωt B.zero) g
Ω-small : Q.Ψ B.zero (P.Ok-tw 0) v hv V.≼ V.val B.zero (proj₁ root-out)
Ω-small = V.≼-refl _
```
