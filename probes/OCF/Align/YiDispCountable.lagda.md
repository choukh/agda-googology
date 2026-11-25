# 目标 Ω：全部保留坐标的单向派发

本篇先修第八轮的 ω+1 支，再给对所有合法 Raw0 坐标的结论。
进一步对目标 Ω 的任意已确定保留的根，给它的第一支及每个原 Gd 分支的派发。
这不是 ψ 或 γ 输出的全部保持：这里只处理保留分支的结构型证据。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiDispCountable where

open import Data.List.Base using ([]; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.LevelFixCore using (LF; Raw; Gd)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
import OCF.Align.YiCtxBase as K
import OCF.Align.YiCtxStep as S
import OCF.Align.YiCtxFork as W
import OCF.Align.YiRTransport as R
open import OCF.Align.YiRCountable
  using (Small; small-zero; small-suc; small-lim; raw0-small;
         one-small; omega-fields; up-fields; raw0-omega-fields)
open import OCF.Align.YiDBase using (Demand; InvD)
import OCF.Align.YiGammaBase as H
open import OCF.Align.YiDispBase

Cover : LF → LF → Set
Cover i t = ∀ {k} → K.Field k t → Below (F.suc k) i

selected-ev : DispEv (Y.tree R.ν) W.b
selected-ev = structural (one (e-branch W.ηb W.guard-b))

selected-keep : choice selected-ev ≡ keep
selected-keep = refl

successor-coordinate : ∀ ζ (e : Gd F.zero (V.cO F.zero) (G.suc ζ)) →
  DispEv (Y.tree R.ν) (V.up F.zero ζ)
successor-coordinate ζ e = structural (one (e-branch (G.suc ζ) e))

all-zero-coordinates : ∀ η (e : Gd F.zero (V.cO F.zero) η) →
  Cover (Y.tree R.ν) (V.Ω̂ (V.up F.zero η))
all-zero-coordinates η e f = cp-edge (raw0-omega-fields η f) (e-branch η e)

seed-cover : Cover (Y.tree R.ν) (Y.tree R.seed-tree)
seed-cover K.at = one e-first
seed-cover (K.in-index ())
seed-cover (K.in-first f) = cp-edge
  (omega-fields (F.suc F.zero) one-small f) e-first
seed-cover (K.in-branch η e f) = all-zero-coordinates η e f

edge-small : ∀ {a b} → Edge a b → Small b → Small a
edge-small e-suc (small-suc s) = s
edge-small (e-lim n) (small-lim s) = s n
edge-small e-first ()
edge-small (e-branch η e) ()

below-small : ∀ {a b} → Below a b → Small b → Small a
below-small (one e) s = edge-small e s
below-small (more p e) s = below-small p (edge-small e s)

edge-Ω-small : ∀ {a} → Edge a (Y.tree R.ν) → Small a
edge-Ω-small e-first = one-small
edge-Ω-small (e-branch η e) = raw0-small η

below-Ω-small : ∀ {a} → Below a (Y.tree R.ν) → Small a
below-Ω-small (one e) = edge-Ω-small e
below-Ω-small (more p e) = below-small p (edge-Ω-small e)

small-field : ∀ {j} → Below (F.suc j) (Y.tree R.ν) → Small j
small-field p with below-Ω-small p
... | small-suc sj = sj

small-retained-domain : ∀ i (j : Y.Level) → Small (Y.tree j) →
  Below (F.suc (Y.tree j)) i → RetainedDomain i j
first (small-retained-domain i j sj p) f = structural
  (cp-below (omega-fields (Y.tree j) sj f) (below-trans (one e-suc) p))
branch (small-retained-domain i j sj p) η e f = structural
  (cp-below (up-fields (Y.tree j) sj η f) (below-trans (one e-suc) p))

-- 比较型已经给keep时，也能提取本目标中的真路径；不对宽位置重新判定。
keep-under-Ω : ∀ {j} (o : Y.Order (F.suc j) (Y.tree R.ν)) →
  order-choice o ≡ keep → Below (F.suc j) (Y.tree R.ν)
keep-under-Ω (Y.below (Y.under-first p)) e = cp-edge p e-first
keep-under-Ω (Y.equal ()) e
keep-under-Ω (Y.above p) ()

kept-Ω-path : ∀ {j} (ev : DispEv (Y.tree R.ν) j) → choice ev ≡ keep →
  Below (F.suc j) (Y.tree R.ν)
kept-Ω-path (structural p) e = p
kept-Ω-path (bounded B pj pi) e = keep-under-Ω (bounded-order B pj pi) e

all-retained-Ω : (j : Y.Level) (ev : DispEv (Y.tree R.ν) (Y.tree j)) →
  choice ev ≡ keep → RetainedDomain (Y.tree R.ν) j
all-retained-Ω j ev e = small-retained-domain (Y.tree R.ν) j
  (small-field (kept-Ω-path ev e)) (kept-Ω-path ev e)

OnlyΩ : Demand
OnlyΩ x y = y ≡ Y.tree R.ν

with-seed-structure : ∀ {D E} → InvD D E R.seed-tree → InvDS D OnlyΩ E R.seed-tree
with-seed-structure i = mixed i (λ {k} f p e →
  subst (Below (F.suc k)) (sym e) (seed-cover f))

NoRetain : Demand
NoRetain x y = ⊥

start : ∀ D → InvDS D NoRetain (Y.zero ∷ []) S.Ω₁
start D = mixed (H.start D) (λ f p d → ⊥-elim d)
```

all-retained-Ω 对任意合法结点字段 j 及任意原合法坐标成立，不是有限测试。
它使用目标 Ω 的一项实质结构事实：每个真子树都是 Small。
只给已保留分支单向证据，没有把其不同坐标拿去三路比较。
