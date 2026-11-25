# Ω 折叠的首个小对象比较
不读记号；编译定理：指定零层与 one 层的标准 Ω 折叠输出按值有序。
只检验这两个闭项，不外推颈结点或一般跨层单调。
来源：展开 YiTBRow 的后继行与 Ω 行；先在本路临时文件检查。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTZSmall where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V

one : B.L
one = B.nd B.sS (λ _ → B.zero)
o-one : P.Ok one
o-one = tt , λ _ → tt
opaque
  low : O.Tr⁺ B.zero
  low = MT.ψ₀ᶻ B.zero tt (proj₁ (O.Ωt B.zero))
  high : O.Tr⁺ B.zero
  high = MT.ψ₀ᶻ one o-one (proj₁ (O.Ωt one))
  small : V.val B.zero (proj₁ low) V.≼ V.val B.zero (proj₁ high)
  small = V.≼l 0 (V.≼-refl _)
```
