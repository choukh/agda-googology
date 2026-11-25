# YiXV：带参照前缀的节点律供给
> 验收文件。编译定理：任意 X:T₂ 的自比较证据和任意带 SC 的 f，完整给出 Norm 五字段。
> ν(y)=ψ₀(X+f(y))，P 用该第 2 层节点的真实显式折叠；不另假设所有 f 满足 SC。
> Sample 将 X=Ω₂、f=up 的整条 Norm 实填；Affine 的 SC 由输入 Good 的节点字段给出。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVAffRef where
open import Data.Product using (proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼l; 1≼ψ⁰) renaming (+-mono to +ᵛ)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVRef2Add as A
import OCF.Lean.YiXVNum as N

module Aff (X : F.T₂) (rx : X F.≤₂ X) (f : R.T₀ → R.T₁) (sc : O.SC f) where
  Z : R.T₀ → F.T₂
  Z y = L.add X A.σ₁ (f y)
  P ν : R.T₀ → R.T₀
  P y = L.ψ (L.suc L.zero) (λ r → r) (Z y)
  ν y = L.ψ⁰ (Z y)
  norm : N.Norm P ν
  N.Norm.same norm y = F.ψ₀≈ (Z y)
  N.Norm.pos norm y = ≼-trans (1≼ψ⁰ (Z y)) (proj₂ (F.ψ₀≈ (Z y)))
  N.Norm.mo norm x y o q = F.mono⁰ (A.tail rx (O.SC.mo sc x y o q))
  N.Norm.db norm y o = F.mono⁰ (A.tail rx (O.SC.db sc y o))
  N.Norm.two norm = ≼-trans (≼l 2 (+ᵛ (1≼ψ⁰ X) (1≼ψ⁰ X)))
    (≼-trans (F.mono⁰ (A.tail rx (O.SC.po sc))) (proj₂ (F.ψ₀≈ (Z R.𝟙))))

module Sample = Aff F.Ω₂ F.Ω₂-refl (L.up L.zero) O.SC-up
sample : N.Norm Sample.P Sample.ν
sample = Sample.norm
```
