# 值读回的 Ω 折叠候选
不读记号；Ψ 以合法值读成层号，再用最小比较表与标准底折叠 Ω 树。
来源：直接复用 YiTCValue.collapseᵛ，不改树、折叠与合法性；LegV 是显式前提。
small₁、small₂ 是两个有限输入上的编译值界，不外推实际 c₁。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTVPsi where
open import Data.Product using (proj₁; proj₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as T
import OCF.Lean.YiMTTab as M
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTCValue as C

Ψ : (k : B.L) → P.Ok k → (v : V.V k) → V.LegV k v → V.V B.zero
Ψ k o v hv = V.val B.zero (proj₁ (C.collapseᵛ k o v hv))

module Finite (c : B.Tr B.zero) where
  h : B.L
  h = B.zero B.⊕ B.↑ B.zero c
  fold : O.Tr⁺ B.zero
  fold = T.ψ h (proj₂ (P.Ok-tw 1) c) (M.rbᶻ h) (F.B₀ h)
    B.zero (P.z≤ h) (O.Ωt B.zero) (proj₁ (O.Ωt h))

small₁ : Ψ B.zero (P.Ok-tw 0) (V.val B.zero (proj₁ (O.Ωt B.zero)))
  (V.val-leg B.zero (proj₁ (O.Ωt B.zero)))
  V.≼ V.val B.zero (proj₁ (Finite.fold (proj₁ (O.Ωt B.zero))))
small₁ = V.≼-refl _

small₂ : Ψ B.zero (P.Ok-tw 0) (V.val B.zero (B.suc (B.suc B.zero)))
  (V.val-leg B.zero (B.suc (B.suc B.zero)))
  V.≼ V.val B.zero (proj₁ (Finite.fold (B.suc (B.suc B.zero))))
small₂ = V.≼-refl _
```
