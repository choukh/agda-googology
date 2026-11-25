# 有限层号 4：lower-one 的实际前提与未填参照桥
验收文件；编译定理：有限实例的 lower-one 与原输出相关性均已实填，末端接线带明确条件。
第 0 步整条管道未通过；MissingReferenceBridge 尚无本路构造，不声称一般孩子关系。
来源：YiPVF2.lower-one、YiPVSmall.output-R、YiPVOne.back；未调用有限层号的叶子下界。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFBFinite where
open import Data.Unit using (tt)
open import Data.Product using (proj₁)
import OCF.Lean.YiPVF2 as F2
import OCF.Lean.YiPVSmall as S
import OCF.Lean.YiPVOne as P
import OCF.Lean.YiLSRel as R
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
import OCF.Lean.YiLSFold as V
import OCF.Lean.YiANFam as AF
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiBVSmall as B
import OCF.Align.Level as L
open import OCF.Lean.YiBRRel using (RelT)

Reference : L.Ordᶜ (L.suc L.zero)
Reference = L.ψ F2.four-p (λ q → L.suc q) (L.Ω (L.natᴵ 4))

-- 只复用 output-R 与 Fout；本文件的下界由 lower-one 实填。
opaque
  unfolding S.Fout
  lower : R.Rel F2.one Reference S.Fout
  lower = F2.lower-one F2.four-nl tt tt (F.B₀ F2.four)
    (V.ok-B₀ F2.four) F2.four-corr F2.four-one F2.four-p

  related : RelT K.one F2.one (proj₁ (B.Small.child-out S.chosen)) S.Fout
  related = S.output-R

-- 参照桥尚未实填；下面的条件接线不计作第 0 步通过。
MissingReferenceBridge : Set
MissingReferenceBridge = R.Rel F2.one Reference S.Fout → AF.M 1 (AF.ψᴺ 1 (AF.Ωᴺ 4)) S.Fout

from-reference-bridge : MissingReferenceBridge → H.M 1 (AF.ψᴺ 1 (AF.Ωᴺ 4)) (proj₁ (B.Small.child-out S.chosen))
from-reference-bridge bridge = P.back related (bridge lower)
```
