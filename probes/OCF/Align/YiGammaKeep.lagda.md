# γ 的保留结点：一个必须定义的合法分支

本篇不否定 InvD。它审查更早的构造义务：照模板折叠 γ 种子 Ω_Ω 到目标 Ω，
根结点的派发为保留；保留后的分支函数须对原 Gd 的每个合法输入有定义。
其中输入 suc ω 所在支是 Ω_{ω+1}，下一次按第一位置派发需公共界 (ω+1, Ω)。
下面只排除这个局部的、保持当前层号树形的派发接口，不否定其它 γ 定义。
下一篇再给真正外层 γ 的来源，并严格区分它与冻结 Actual。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGammaKeep where

open import Data.Empty using (⊥)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_,_; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.LevelFixCore using (Raw; Gd)
import OCF.Align.LevelFixCore as F
open F using (module G)
open import OCF.Align.LevelFixVal using (CP; CP-tr)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
import OCF.Align.YiCtxFork as W
import OCF.Align.YiRTransport as R
open import OCF.Align.YiSpineCommon using (Common; common→spinal)

root-common : Common W.one R.ν
root-common = R.ν , V.fst V.self , V.self

selected-branch-tree : V.Ω̂ (V.up F.zero W.ηb) ≡
  F.lc W.b (V.cO W.b) (V.Ω̂ W.b) (λ η e → V.up W.b η)
selected-branch-tree = refl

ν-not-b : CP (Y.tree R.ν) W.b → ⊥
ν-not-b (V.lim n p) = R.ν-not-finite (W.finite-position p (W.nat-finite n))

b-not-ν : CP W.b (Y.tree R.ν) → ⊥
b-not-ν (V.fst p) = W.lim-not-finite (W.finite-position p (W.fs W.fz))

no-common-b-ν : Common (Y.suc W.b-level) R.ν → ⊥
no-common-b-ν (B , p , q) with common→spinal {a = W.b-level} {b = R.ν}
  (B , CP-tr (V.suc V.self) p , q)
... | inj₁ bν = b-not-ν bν
... | inj₂ νb = ν-not-b νb

-- η=suc ζ 时，种子的该支 Ω_(suc ζ) 有根字段 up0 ζ。
below : (ζ : Raw F.zero) → Gd F.zero (V.cO F.zero) (G.suc ζ) → Y.Level
below ζ e = Y.level (V.up F.zero ζ) (V.lgl→Legal F.zero tt ζ (proj₂ e))

record KeepSeedDispatch : Set where
  field
    at-successor : ∀ ζ (e : Gd F.zero (V.cO F.zero) (G.suc ζ)) →
      Common (Y.suc (below ζ e)) R.ν
open KeepSeedDispatch public

no-keep-seed-dispatch : KeepSeedDispatch → ⊥
no-keep-seed-dispatch dispatch = no-common-b-ν
  (at-successor dispatch (G.lim W.raw-nat) W.guard-b)
```

guard-b 实填原 Gd，b-level 实填合法 ω 列，ν=Ω 是合法层号。
KeepSeedDispatch 只列出保留根之后“后继形坐标支的根”这一小部分派发，
没有把下标字段、所有历史成员或同一支深处的一切字段重新塞进 InvD。
它也不被写成新的输入不变量；否定说明这个具体的位置派发接线不能作为现成构造。
