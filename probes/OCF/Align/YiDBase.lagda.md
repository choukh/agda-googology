# 按实际需求逐对给第一位置界

InvD 的参数 D 是派发树与目标树之间的需求关系。字段仍由原 Field 定位，
目标仍来自当前 Env；只有 D 实际要求的那一对才需要合法公共界。
不同需求可以用不同的界，既不要求所有字段与整个 Env 相容，
也不把这些逐对界收集为一个全树界。D 的运行覆盖由验收层另给，
本接口不以“在 Env 中”代替“将来会比较”。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiDBase where

open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product.Base using (_,_)
open import OCF.Align.LevelFixCore using (LF)
import OCF.Align.LevelFixCore as F
open import OCF.Align.LevelFixVal using (CP)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
open import OCF.Align.YiCtxBase using (Field; Ctx)
open import OCF.Align.YiCtxStep using (field-level)
open import OCF.Align.YiSpineCommon using (Common)

Demand : Set₁
Demand = LF → LF → Set

dispatch : (t : Y.Level) → ∀ {k} → Field k (Y.tree t) → Y.Level
dispatch t f = Y.suc (field-level t f)

record InvD (D : Demand) (E : List Y.Level) (t : Y.Level) : Set where
  constructor demanded
  field
    context : Ctx E
    needed : ∀ {k} (f : Field k (Y.tree t)) {u} → u ∈ E →
      D (F.suc k) (Y.tree u) → Common (dispatch t f) u
open InvD public

weaken-demand : ∀ {D D′ E t} →
  (∀ {x y} → D′ x y → D x y) → InvD D E t → InvD D′ E t
weaken-demand sub i = demanded (context i) (λ f p d → needed i f p (sub d))

zero-position : ∀ t → CP F.zero t
zero-position F.zero = V.self
zero-position (F.suc t) = V.suc (zero-position t)
zero-position (F.lim f) = V.lim 0 (zero-position (f 0))
zero-position (F.lc k c t g) = V.fst (zero-position t)

zero-common : ∀ x → Common x Y.zero
zero-common x = x , V.self , zero-position (Y.tree x)
```

context 仅保存历史 Env 自身已有的界；needed 的公共界不必扩展它。
这正是本轮与 InvR 的差别。此处没有 ψ、比较裸下标的全域律、
原始树编码器或新的树构造子。
