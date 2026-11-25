# YiXVReadRouteKeep
> 验收文件。档位：编译定理。原 kp 的精确分支归纳：保留给槽位等式与搬运，对角给树内路径。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteKeep where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; subst)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSTw1 as T
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadWholeInput as Whole
import OCF.Lean.YiXVReadRouteInput as R
import OCF.Lean.YiXVReadRoute as Route
import OCF.Lean.YiXVReadRouteWay as Way
import OCF.Lean.YiXVReadRoutePush as Push
open import OCF.Lean.YiXVReadKeepLinkInput using (Link; link)
import OCF.Lean.YiXVReadKeepLink as LinkOps

mutual
  kp : ∀ cur (p : S.Pos (J.ℓ cur)) {y v} (rv : R.Route cur y v)
    {X : Set} (K : (q : S.Pos (J.ℓ y)) → (S.Br (J.ℓ y) q → S.Br (J.ℓ cur) p) → X)
    (d : X) (Q : X → Set)
    (hk : ∀ q cv → Link cur (inj₂ p) y q cv → Q (K q cv))
    (hd : y P.≤ᵀ J.slot cur p → Q d) →
    Q (Fold.kp (J.ℓ cur) (T.εh cur) (T.ρh cur) p v K d)
  kp cur p R.here K d Q hk hd = hk p (λ z → z) (link refl (λ a X h → h))
  kp (S.suc r) p (R.ins rv) K d Q hk hd = kp⁼ r p rv K d Q
    (λ q cv h → hk q cv (LinkOps.rise-suc r p h)) (λ h → hd (LinkOps.diag-suc r p h))
  kp (S.lim f a) (m , p) {y} (R.inl n rv) K d Q hk hd
    with Path.way (λ k → J.ℓ (f k)) (proj₂ (T.ρh (S.lim f a))) m n | Way.Family.way f a m n
  ... | Path.fwd v | vw = kp⁼ (f n) (Path.psh v p) rv
    (λ q cv → K q (λ z → Path.pshBr v p (cv z))) d Q
    (λ q cv h → hk q (λ z → Path.pshBr v p (cv z))
      (LinkOps.rise-lim f a m p
        (LinkOps.pre (f m) p (f n) (Path.psh v p) (Path.pshBr v p)
          (Push.slot vw p) (Push.pull vw p) h)))
    (λ h → hd (LinkOps.diag-lim f a m p
      (subst (λ r → y P.≤ᵀ r) (Push.slot vw p) h)))
  ... | Path.bwd v | vw = kp⁼ (f m) p (Route.compose vw rv) K d Q
    (λ q cv h → hk q cv (LinkOps.rise-lim f a m p h))
    (λ h → hd (LinkOps.diag-lim f a m p h))
  kp (S.lim f a) (m , p) (R.inlu rv) K d Q hk hd = kp⁼ (f m) p (rv m) K d Q
    (λ q cv h → hk q cv (LinkOps.rise-lim f a m p h))
    (λ h → hd (LinkOps.diag-lim f a m p h))
  kp⁼ : ∀ cur (p : S.Pos⁼ (J.ℓ cur)) {y v} (rv : R.Route cur y v)
    {X : Set} (K : (q : S.Pos (J.ℓ y)) → (S.Br (J.ℓ y) q → S.Br⁼ (J.ℓ cur) p) → X)
    (d : X) (Q : X → Set)
    (hk : ∀ q cv → Link cur p y q cv → Q (K q cv))
    (hd : y P.≤ᵀ Whole.slot cur p → Q d) →
    Q (Fold.kp⁼ (J.ℓ cur) (T.εh cur) (T.ρh cur) p v K d)
  kp⁼ cur (inj₁ t) rv K d Q hk hd = hd (Route.within rv)
  kp⁼ cur (inj₂ p) rv K d Q hk hd = kp cur p rv K d Q hk hd
```
