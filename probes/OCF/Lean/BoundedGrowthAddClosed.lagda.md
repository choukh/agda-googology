# 含 Ω 增量的累加扩界闭项

复用配对路线的累加世界截面，将合法化后的 Ω 坐标作为增量。
旧世界按定理完整保留；这里的增量尚非高层输出的折叠读回。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedGrowthAddClosed where
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.LHRecLeg using (leg; Lg-leg; w₀L; lw₀L; pw)
open import OCF.Lean.LHRecFl using (flL; Lg-flL)
open import OCF.Lean.BoundedContextRun using (path-context)
open import OCF.Lean.BoundedGrowthIf
open import OCF.Lean.BoundedGrowthRun
import OCF.Lean.BoundedGrowthNegAdd as A
import OCF.Lean.BoundedContextClosed as C
open import Relation.Binary.PropositionalEquality using (_≡_)

R : HB (Lv C.k)
R = leg C.k C.B
legal-R : LgB R
legal-R = Lg-leg C.k C.B

bound : HB (Lv C.k)
bound = C.B ⊞ R
legal-bound : LgB bound
legal-bound = Lg-⊞ C.B R C.legal-B legal-R

module G = Grow (ΩL C.k) C.k C.w C.B bound (⊞-fst C.B R)
W : Wd G.Old.T
W = w₀L (ΩL C.k ⊕L upL C.k C.B)
module E = A.Add (ΩL C.k) C.k C.B W

growth : WorldGrowth (ΩL C.k) C.k C.w C.B bound (⊞-fst C.B R) W
growth = E.growth C.w R (lw₀L (ΩL C.k ⊕L upL C.k C.B))

exact-world : pw (path-context (ΩL C.k) C.k (⊞-fst {w = C.w} C.B R))
  (WorldGrowth.future growth) ≡ W
exact-world = E.project C.w R

moved : HB G.New.S
moved = G.move C.input
legal-moved : LgB moved
legal-moved = G.move-legal C.input C.legal-input

output : HB G.Fresh.T
output = G.result C.input ⊞ flL (ΩL C.k ⊕L upL C.k bound)
legal-output : LgB output
legal-output = Lg-⊞ (G.result C.input) (flL (ΩL C.k ⊕L upL C.k bound))
  (G.result-legal C.input C.legal-input) (Lg-flL (ΩL C.k ⊕L upL C.k bound))

preserved : ∀ {a} → a ⊲[ W ] C.input →
  G.move a ⊲[ WorldGrowth.future growth ] moved
preserved = G.witnessed-position growth
```

`leg` 保留 Ω 根，只对其分支合法化，故 R 不是纯可数增量。
合法的 bound、世界扩张、旧混合树搬运和新输出均已给出。
没有把外给坐标当成反馈产生的坐标，也没有序数值强度结论。
下一项需实现局部 read/fold，将真实高层输出变成此类低层增量。
