# 正则层号的全层保留分支覆盖

本篇按结构参数证明：Reg j 加已确定的保留派发足以覆盖第一支与所有合法坐标。
不对两个宽位置比较，也不为原始树生成码。输出的 Reg 保持是另一项义务。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRegCover where

open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.LevelFixCore using (LF; Raw; Pre; Low; GdL; Kid; KidR)
import OCF.Align.LevelFixCore as F
open F using (module G)
open import OCF.Align.LevelFixVal using (CP)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
import OCF.Align.YiCtxBase as K
open import OCF.Align.YiDispBase
open import OCF.Align.YiDispCountable using (Cover)
open import OCF.Align.YiRegBase using (Reg; reg-fields)

node-cover : ∀ {i k c t g} → Reg k → Below (F.suc k) i →
  Cover i t → (∀ η e → Cover i (g η e)) → Cover i (F.lc k c t g)
node-cover rk p pt pg K.at = p
node-cover rk p pt pg (K.in-index f) =
  below-trans (reg-fields rk f) (below-trans (one e-suc) p)
node-cover rk p pt pg (K.in-first f) = pt f
node-cover rk p pt pg (K.in-branch η e f) = pg η e f

upN-cover : ∀ y → Reg y → (r : Pre y) (c : Low y r)
  (t : LF) (g : (η : Low y r) → GdL y r c η → LF) →
  ∀ i → Below y i → Cover i t → (∀ η e → Cover i (g η e)) → Cover i (V.upN y r c t g)
upN-cover F.zero ry ()
upN-cover (F.suc y) ry (inj₁ _) c t g i p pt pg = node-cover ry p pt pg
upN-cover (F.suc y) ry (inj₂ r) c t g i p pt pg =
  upN-cover y ry r c t g i (below-trans (one e-suc) p) pt pg
upN-cover (F.lim f) rf (n , r) c t g i p pt pg =
  upN-cover (f n) (rf n) r c t g i (below-trans (one (e-lim n)) p) pt pg
upN-cover (F.lc k c₀ t₀ g₀) (bound , rk , rt , rg) (inj₁ (inj₁ _)) c t g i p pt pg =
  node-cover rk (below-trans bound p) pt pg
upN-cover (F.lc k c₀ t₀ g₀) (bound , rk , rt , rg) (inj₁ (inj₂ r)) c t g i p pt pg =
  upN-cover k rk r c t g i (below-trans (below-trans (one e-suc) bound) p) pt pg
upN-cover (F.lc k c₀ t₀ g₀) (bound , rk , rt , rg) (inj₂ (inj₁ r)) c t g i p pt pg =
  upN-cover t₀ rt r c t g i (below-trans (one e-first) p) pt pg
upN-cover (F.lc k c₀ t₀ g₀) (bound , rk , rt , rg) (inj₂ (inj₂ (η , e , r))) c t g i p pt pg =
  upN-cover (g₀ η e) (rg η e) r c t g i (below-trans (one (e-branch η e)) p) pt pg

mutual
  omega-cover : ∀ y → Reg y → ∀ i → Below y i → Cover i (V.Ω̂ y)
  omega-cover F.zero ry i p (K.in-suc ())
  omega-cover (F.suc y) ry i p = node-cover ry p
    (omega-cover y ry i (below-trans (one e-suc) p))
    (λ η e → up-cover y ry i (below-trans (one e-suc) p) η)
  omega-cover (F.lim f) rf i p (K.in-lim n q) =
    omega-cover (f n) (rf n) i (below-trans (one (e-lim n)) p) q
  omega-cover (F.lc k c t g) (bound , rk , rt , rg) i p =
    node-cover rk (below-trans bound p)
      (omega-cover t rt i (below-trans (one e-first) p))
      (λ η e → omega-cover (g η e) (rg η e) i (below-trans (one (e-branch η e)) p))

  up-cover : ∀ y → Reg y → ∀ i → Below y i → ∀ η → Cover i (V.up y η)
  up-cover y ry i p G.zero ()
  up-cover y ry i p (G.suc η) (K.in-suc f) = up-cover y ry i p η f
  up-cover y ry i p (G.lim f) (K.in-lim n q) = up-cover y ry i p (f n) q
  up-cover y ry i p (G.lc r c t g) =
    upN-cover y ry r c (V.up y t) (λ η e → V.up y (g η e)) i p
      (up-cover y ry i p t) (λ η e → up-cover y ry i p (g η e))
  up-cover y ry i p (G.em k t) = upK-cover y ry i p k t
  up-cover y ry i p G.top = omega-cover y ry i p

  upK-cover : ∀ y → Reg y → ∀ i → Below y i → (k : Kid y) →
    (t : KidR y k) → Cover i (V.upK y k t)
  upK-cover F.zero ry i p () t
  upK-cover (F.suc y) ry i p k t = up-cover y ry i (below-trans (one e-suc) p) t
  upK-cover (F.lim f) rf i p n t = up-cover (f n) (rf n) i (below-trans (one (e-lim n)) p) t
  upK-cover (F.lc k c t g) (bound , rk , rt , rg) i p (inj₁ _) T =
    up-cover k rk i (below-trans (below-trans (one e-suc) bound) p) T
  upK-cover (F.lc k c t g) (bound , rk , rt , rg) i p (inj₂ (inj₁ _)) T =
    up-cover t rt i (below-trans (one e-first) p) T
  upK-cover (F.lc k c t g) (bound , rk , rt , rg) i p (inj₂ (inj₂ (η , e))) T =
    up-cover (g η e) (rg η e) i (below-trans (one (e-branch η e)) p) T

below-cp : ∀ {a b c} → Below a b → CP b c → Below a c
below-cp p V.self = p
below-cp p (V.suc q) = more (below-cp p q) e-suc
below-cp p (V.lim n q) = more (below-cp p q) (e-lim n)
below-cp p (V.fst q) = more (below-cp p q) e-first

proper-cp : ∀ {a b} → Y.Proper a b → CP a b
proper-cp (Y.under-suc p) = V.suc p
proper-cp (Y.under-lim n p) = V.lim n p
proper-cp (Y.under-first p) = V.fst p

keep-cp : ∀ {a b} (o : Y.Order a b) → order-choice o ≡ keep → CP a b
keep-cp (Y.below p) e = proper-cp p
keep-cp {a} (Y.equal e) kept = subst (CP a) e V.self
keep-cp (Y.above p) ()

kept-under : ∀ {i j} (ev : DispEv i j) → choice ev ≡ keep → Below j i
kept-under (structural p) e = below-trans (one e-suc) p
kept-under (bounded B pj pi) e = below-cp (one e-suc) (keep-cp (bounded-order B pj pi) e)

all-retained-reg : (i j : Y.Level) → Reg (Y.tree j) →
  (ev : DispEv (Y.tree i) (Y.tree j)) → choice ev ≡ keep → RetainedDomain (Y.tree i) j
first (all-retained-reg i j rj ev kept) f =
  structural (omega-cover (Y.tree j) rj (Y.tree i) (kept-under ev kept) f)
branch (all-retained-reg i j rj ev kept) η e f =
  structural (up-cover (Y.tree j) rj (Y.tree i) (kept-under ev kept) η f)
```

all-retained-reg 不限目标 Ω，也不限制坐标层。目标有原 Level 合法性，
甚至不需要额外的 Reg i；字段层 Reg j 与初始派发证据就够了。
up-cover 的位置界对任意 Raw 值成立；只有合法分支会进入 RetainedDomain 的调用。
这不是原始树编码器，也不保证读回树本身满足 Reg，后者须另证。
