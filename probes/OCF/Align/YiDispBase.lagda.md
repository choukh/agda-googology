# 两类派发证据：第一位置判定与单向树路径

DispEv i j 中 j 是结点字段，判定型比较的是 suc j 与 i，与原模板一致。
结构型保存 suc j 到 i 的真子树路径，直接保留；不比较两个宽位置。
路径只走后继、ℕ支、第一支及原 Gd 合法Ω支，不把 lc.k 字段计作值的下界。
这是一份明确的 Pre 类子树接口，不把原 Pre 的每个槽位自动解释成序关系。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiDispBase where

open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import OCF.Align.LevelFixCore using (LF; Raw; Gd)
import OCF.Align.LevelFixCore as F
open import OCF.Align.LevelFixVal using (CP; Legal)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
open import OCF.Align.YiLevelCompare using (compare; from-left; from-right)
open import OCF.Align.YiSpineCommon using (Common)
import OCF.Align.YiCtxBase as K
open import OCF.Align.YiDBase using (Demand; InvD; needed)
import OCF.Align.YiGammaBase as H

data Edge : LF → LF → Set where
  e-suc : ∀ {x} → Edge x (F.suc x)
  e-lim : ∀ {f} n → Edge (f n) (F.lim f)
  e-first : ∀ {k c t g} → Edge t (F.lc k c t g)
  e-branch : ∀ {k c t g} η e → Edge (g η e) (F.lc k c t g)

data Below : LF → LF → Set where
  one : ∀ {a b} → Edge a b → Below a b
  more : ∀ {a b c} → Below a b → Edge b c → Below a c

below-trans : ∀ {a b c} → Below a b → Below b c → Below a c
below-trans p (one e) = more p e
below-trans p (more q e) = more (below-trans p q) e

cp-edge : ∀ {a b c} → CP a b → Edge b c → Below a c
cp-edge V.self e = one e
cp-edge (V.suc p) e = more (cp-edge p e-suc) e
cp-edge (V.lim n p) e = more (cp-edge p (e-lim n)) e
cp-edge (V.fst p) e = more (cp-edge p e-first) e

cp-below : ∀ {a b c} → CP a b → Below b c → Below a c
cp-below p (one e) = cp-edge p e
cp-below p (more q e) = more (cp-below p q) e

data DispEv (i j : LF) : Set where
  bounded : (B : Y.Level) → CP (F.suc j) (Y.tree B) → CP i (Y.tree B) → DispEv i j
  structural : Below (F.suc j) i → DispEv i j

common-ev : ∀ i j → Common (Y.suc j) i → DispEv (Y.tree i) (Y.tree j)
common-ev i j (B , pj , pi) = bounded B pj pi

data Choice : Set where keep collapse : Choice

order-choice : ∀ {a b} → Y.Order a b → Choice
order-choice (Y.below p) = keep
order-choice (Y.equal p) = keep
order-choice (Y.above p) = collapse

bounded-order : ∀ {i j} B → CP (F.suc j) (Y.tree B) → CP i (Y.tree B) → Y.Order (F.suc j) i
bounded-order B pj pi with compare (Y.tree B) pj pi (Y.legal B)
... | inj₁ p = from-left p
... | inj₂ p = from-right p

choice : ∀ {i j} → DispEv i j → Choice
choice (bounded B pj pi) = order-choice (bounded-order B pj pi)
choice (structural p) = keep

-- 两类调用分开保存；实际D比较仍走原InvD/CP判定，不用结构型替代它。
record InvDS (D S : Demand) (E : List Y.Level) (t : Y.Level) : Set where
  constructor mixed
  field
    actual-inv : InvD D E t
    retained : ∀ {k} → K.Field k (Y.tree t) → ∀ {u} → u ∈ E →
      S (F.suc k) (Y.tree u) → Below (F.suc k) (Y.tree u)
open InvDS public

actual-ev : ∀ {D S E t k u} (i : InvDS D S E t) →
  K.Field k (Y.tree t) → u ∈ E → D (F.suc k) (Y.tree u) → DispEv (Y.tree u) k
actual-ev i f p d with needed (actual-inv i) f p d
... | B , pk , pu = bounded B pk pu

retained-ev : ∀ {D S E t k u} (i : InvDS D S E t) →
  K.Field k (Y.tree t) → u ∈ E → S (F.suc k) (Y.tree u) → DispEv (Y.tree u) k
retained-ev i f p d = structural (retained i f p d)

pred-inv : ∀ {D S E} x → InvDS D S E (Y.suc x) → InvDS D S E x
pred-inv x i = mixed (H.pred-inv x (actual-inv i))
  (λ f p d → retained i (K.in-suc f) p d)

enter-inv : ∀ {D S E k c t g} (lawful : Legal (F.lc k c t g)) →
  InvDS D S E (Y.level (F.lc k c t g) lawful) → ∀ η e →
  InvDS D S E (Y.level (g η e) (H.branch-lawful lawful η e))
enter-inv lawful i η e = mixed (H.enter-inv lawful (actual-inv i) η e)
  (λ f p d → retained i (K.in-branch η e f) p d)

-- 检验用充分覆盖合同，Field含额外路径；并非模板最小必要条件。
-- 后面的反例仅用first/top支的直接根，因此不依赖这些额外量词。
record RetainedDomain (i : LF) (j : Y.Level) : Set where
  field
    first : ∀ {h} → K.Field h (Y.tree (Y.Ω j)) → DispEv i h
    branch : ∀ η (e : Gd (Y.tree j) (V.cO (Y.tree j)) η) {h} →
      K.Field h (V.up (Y.tree j) η) → DispEv i h
open RetainedDomain public
```

structural 不返回序比较结果或否定其它方向，只按已有路径选择keep。
bounded 的eq行也保留，保持原规则；结构型的真路径没有自反构造子。
RetainedDomain是检验“初始派发证据能否传到保留支”所用的共享合同，
尚不由 Legal 或初始 DispEv 自动给出；其全部Field量词是充分条件，
实际运行需要的子集仍应由运行路径给出。
