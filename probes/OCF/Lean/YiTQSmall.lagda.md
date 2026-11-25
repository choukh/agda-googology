# Ω 折叠的小实例升级
不读记号；编译定理：标准 one 层的 Ω 折叠输出不高于 two 层输出。
目标累计列取第 1 项；不把有限实例外推为 Cover。
来源：YiTZSmall 的对象升级；复用 YiTBRow.mono、YiVWVal.val-+ 与 YiTMInner.right-⊹。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTQSmall where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTMInner as I
import OCF.Lean.YiTZSmall as S
import OCF.Lean.YiTZLocal as T

opaque
  low : O.Tr⁺ B.zero
  low = MT.ψ₀ᶻ S.one S.o-one (proj₁ (O.Ωt S.one))
  high : O.Tr⁺ B.zero
  high = MT.ψ₀ᶻ T.two T.o-two (proj₁ (O.Ωt T.two))
  high₀ : B.Tr B.zero
  high₀ = proj₁ (MT.ψ₀ᶻ S.one S.o-one (B.suc B.zero))
  high₁ : B.Tr B.zero
  high₁ = proj₁ (MT.ψ₀ᶻ S.one S.o-one (B.suc (proj₁ (O.next⁺ (O.Ωt S.one)))))
  one-two : V.val B.zero (proj₁ low) V.≼ V.val B.zero (proj₁ high)
  one-two = V.≼l 1 (V.≼-trans
    (V.◁→≼ (V.val-mono B.zero (TB.mono S.one S.o-one (MT.rbᶻ S.one)
      (F.B₀ S.one) B.zero (P.z≤ S.one) (O.Ωt B.zero)
      {x = proj₁ (O.Ωt S.one)}
      {y = B.suc (proj₁ (O.next⁺ (O.Ωt S.one)))}
      (B.◃t (B.◃l 0) B.◃s))))
    (V.≼-trans (I.right-⊹ (V.val B.zero high₀) (V.val B.zero high₁))
      (proj₂ (V.val-+ high₀ high₁))))
```
