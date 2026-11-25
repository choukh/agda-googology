# 规则 (48) 的 W4 纯 Ω 森林探针

第四层，无条件。实际一级反馈能逐轮保留旧代码及其 Ω 提升。所有较小正规纯森林的恢复值合起来仍低于指定父值，该初段的上确界有统一精确值，首轮为 ψ₀(Ω_ω)。
推论 12.3 的规则在指定的 distinguished set 上递归，每步对先前各段之并施加可及部分运算。本探针检验旧初段在 W4 中的位置和恢复值。文献记号的校准与 W4 全局下界仍开放。[Rathjen，命题 12.2 与推论 12.3](https://eprints.whiterose.ac.uk/76751/1/Diss.pdf)

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module Survey.W4Rule48 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; subst)
open import OCF.Align.EboLeanDef using (T; ΩTower; _<ᵀ_; []<; hd<; tl<; lv<; ar<)
open import OCF.Align.EboLeanBase using (NF; nf-Ω)
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.Bachmann using (<sucT)
open import OCF.Lean.YiRefTw2 using (Rt; tree-≼)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼l; ≅→≼; ≼-refl; ≼-trans; ≼-suc; l≼; s≼s)
open import OCF.Align.EBO using (<-sucT)
import OCF.Align.EboLeanDef as Notation
open import OCF.Align.TightValBase using (s≼-irrefl)
import OCF.Align.Level as L
import B25DTrack as Run
import B26CForest as Forest
import B26CScalar as Scalar
import B26OSparse as Name
import B28CodePath as Path
import B28FHead as Head
import B28FGap as Gap
import B28Orbit as Orbit
import B26CDecode as Decode
import B12XRef as Ref

code = λ a → Scalar.code (Forest.small a)
At = λ a n → Path.Path (code a) (Run.χ n)

lift-at : ∀ {a n} → At a n → At (Name.card a) (suc n)
lift-at p = Path.take 0 (Path.power p)

retain : ∀ {a} → Forest.Pure a → NF a → Path.Path (code a) (code (Name.card a))
retain {a} pa na = Path.descend (Forest.normal pa na) normal (Forest.belowε (Name.card a))
  (hc normal (Forest.count (Name.card a))) (Forest.below-head pa [])
  where normal = Forest.normal (Forest.node pa Forest.empty) (nf-Ω na)

both : ∀ {a n} → Forest.Pure a → NF a → At a n → At a (suc n) × At (Name.card a) (suc n)
both {a} {n} pa na p = Path.join (retain pa na) next , next
  where next = lift-at {a} {n} p

located : ∀ n → At (ΩTower n) (suc n)
located zero = lift-at {[]} {0} Path.stop
located (suc n) = lift-at {ΩTower n} {suc n} (located n)
```

令 $C(t)=\psi_0(\Omega_t)$。给定正规纯 Ω 森林 $a$，取 $u=\Omega_{a+1}$。任意非空正规纯森林 $t<u$ 的首下标至多为 $a$。首下标小于 $a$ 时，一份 $\Omega_a$ 已盖住 $t$。等于 $a$ 时，剥去重复的首项即可给出份数。这里比较的是恢复后的原记号值。中间名取 $C(\psi_a(1))$。

```agda
module History (a : T) (pa : Forest.Pure a) (na : NF a) where
  module G = Gap.At a pa na
  middle = Rt G.hmid
  parent = Rt G.hup
  charge = λ {t} (pt : Forest.Pure t) (nt : NF t) → Rt (Head.response pt nt)

  represented : ∀ {t} (pt : Forest.Pure t) (nt : NF t) → t <ᵀ G.upper →
    Σ ℕ (λ j → L.suc (charge pt nt) ≼ G.R.point j)
  represented Forest.empty nt []< = 0 , Head.step Forest.empty nt
    (Head.pure-copies pa 1) (G.R.normal 1) (Head.response Forest.empty nt) (G.R.at 0) []<
  represented pt@(Forest.node pu ps) nt (hd< (lv< h)) with <sucT a h
  ... | inj₁ less = 0 , Head.step pt nt (Head.pure-copies pa 1) (G.R.normal 1)
    (Head.response pt nt) (G.R.at 0) (hd< (lv< less))
  ... | inj₂ refl = G.R.inside ps nt (Head.response pt nt)
  represented (Forest.node _ _) _ (hd< (ar< ()))
  represented (Forest.node _ _) _ (tl< ())

  before : ∀ {t} (pt : Forest.Pure t) (nt : NF t) → t <ᵀ G.upper → L.suc (charge pt nt) ≼ middle
  before pt nt lt with represented pt nt lt
  ... | j , h = ≼-trans {b = G.R.point j} h (≼-trans {b = L.suc (G.R.point j)}
    (≼-suc (≼-refl _)) (G.first j))

  copies-below : ∀ k → Head.copies a k <ᵀ G.upper
  copies-below zero = []<
  copies-below (suc k) = hd< (lv< (<-sucT a))

  stages : Notation.HC (Name.collapse G.mid)
  stages = Notation.hω refl λ k → Head.response (Head.pure-copies pa k) (G.R.normal k)

  exact-history : middle ≈ᵛ G.R.limit
  exact-history = ≼-trans {b = Rt stages} (tree-≼ refl G.hmid stages) (l≼ upper) ,
    l≼ (λ j → ≼-trans {b = L.suc (G.R.point j)} (≼-suc (≼-refl _)) (G.first j))
    where
    upper : ∀ k → charge (Head.pure-copies pa k) (G.R.normal k) ≼ G.R.limit
    upper k with represented (Head.pure-copies pa k) (G.R.normal k) (copies-below k)
    ... | j , h = ≼l {f = G.R.point} j (≼-trans (≼-suc (≼-refl _)) h)

  misses : ∀ {t} (pt : Forest.Pure t) (nt : NF t) → t <ᵀ G.upper → middle ≼ charge pt nt → ⊥
  misses pt nt lt h = s≼-irrefl _ (≼-trans (before pt nt lt) h)

  no-history : ∀ (ts : ℕ → T) (ps : ∀ i → Forest.Pure (ts i)) (ns : ∀ i → NF (ts i))
    → (∀ i → ts i <ᵀ G.upper) → parent ≼ L.lim (λ i → charge (ps i) (ns i)) → ⊥
  no-history ts ps ns lt h = s≼-irrefl middle (≼-trans {b = parent} G.next (≼-trans h
    (l≼ (λ i → ≼-trans (≼-suc (≼-refl _)) (before (ps i) (ns i) (lt i))))))
```

把 a 实例化为实际输入 χₙ 恢复的森林。严格低于 u 的每个旧代码都能放在同一个 χₙ₊₁ 中，并能在下一输入继续提升。

```agda
module OnOrbit (n : ℕ) where
  module H = History (Orbit.forest n) (Orbit.pure n) (Orbit.regular n)

  all-at : ∀ {t} (pt : Forest.Pure t) (nt : NF t) → t <ᵀ H.G.upper → At t (suc n)
  all-at pt nt lt = subst (Path.Path _) (Orbit.literal (suc n))
    (Path.descend (Forest.normal pt nt) (Orbit.regular-term (suc n))
      (Forest.belowε (Orbit.forest (suc n))) (Orbit.input-h (suc n))
      (Forest.forward pt (Orbit.pure (suc n)) lt))

  continue : ∀ {t} (pt : Forest.Pure t) (nt : NF t) → t <ᵀ H.G.upper →
    At t (suc (suc n)) × At (Name.card t) (suc (suc n))
  continue {t} pt nt lt = both {t} {suc n} pt nt (all-at pt nt lt)

module Start = OnOrbit 0
source-short : L.suc Run.unit-output ≼ Start.H.middle
source-short = ≼-trans {b = L.suc (Start.H.G.R.point 0)}
  (s≼s (≼-trans {b = Ref.row 1} Decode.read-bound
    (tree-≼ refl (Ref.H 1) (Start.H.G.R.at 0)))) (Start.H.G.first 0)
```

取 a=0。中间名的基本列给出各有限层。另以第 31 批实际 (0,1) 正槽的完整返回检验同一门槛。

```agda
import B28FFinite as Finite
import B12BtboCut as Cut

first-scale : Start.H.middle ≈ᵛ Cut.omega-cut
first-scale = ≼-trans {b = Finite.R.limit} (proj₁ Start.H.exact-history) Finite.up ,
  ≼-trans {b = Finite.R.limit} Finite.down (proj₂ Start.H.exact-history)

finite-three-short : L.suc (Cut.finite 3) ≼ Start.H.middle
finite-three-short = ≼-trans {b = L.suc (Finite.R.point 2)}
  (s≼s (≅→≼ (L.≅-sym (Finite.point 2)))) (Start.H.G.first 2)
```

令 U 为所有塔与自然数位置的单位重置返回的上确界。对每个有限层找一个严格超过它的真实返回，恰好能使 U 覆盖首轮中间值。

```agda
import B27Joint as Unit
import B27UEnvelope as Units

word-below : ∀ k → Finite.word k <ᵀ Start.H.G.upper
word-below zero = []<
word-below (suc k) = hd< (lv< []<)

finite-short : ∀ k → L.suc (Cut.finite k) ≼ Start.H.middle
finite-short k = ≼-trans {b = L.suc (Start.H.charge p n)}
  (s≼s (≅→≼ (L.≅-sym (Finite.Fin.same k (Head.response p n)))))
  (Start.H.before p n (word-below k))
  where p = Head.pure-copies Forest.empty k
        n = Finite.R.normal k

-- Hit 给出一座实际塔、一个位置和该单位返回严格超过门槛的证明。
to-hits : Start.H.middle ≼ Units.U → ∀ k → Unit.Hit (Cut.finite k)
to-hits d k = Unit.Matrix.locate Unit.f (Cut.finite k) (≼-trans {b = Start.H.middle} (finite-short k) d)

from-hits : (∀ k → Unit.Hit (Cut.finite k)) → Start.H.middle ≼ Units.U
from-hits hits = ≼-trans {b = Cut.omega-cut} (proj₁ first-scale)
  (l≼ (λ k → Unit.bound (Cut.finite k) Units.U Units.component (hits k)))

paid-two : Unit.Hit (Cut.finite 2)
paid-two = 1 , 0 , ≼-trans {a = L.suc (Cut.finite 2)} {b = L.suc (Finite.R.point 1)} {c = Unit.f 1 0}
  (s≼s {a = Cut.finite 2} {b = Finite.R.point 1} (≅→≼ (L.≅-sym (Finite.point 1)))) (Finite.paid 0 0 (Finite.R.at 1))
```

让实际轨道位置 n 也变化。每段旧历史的精确值位于相邻两次恢复值之间，可以直接对这些历史验收整树下界。

```agda
import B28OneChild as Child
import B28Acceptance as Accept
import B26Names as Original
import B14Goal as Goal

cut = OnOrbit.H.middle
rises : ∀ n → L.suc (Orbit.value n) ≼ cut n
rises n = ≼-trans {b = OnOrbit.H.G.R.point n 0} (Child.At.strict n 0)
  (≼-trans {b = L.suc (OnOrbit.H.G.R.point n 0)} (≼-suc (≼-refl _)) (OnOrbit.H.G.first n 0))

below-next : ∀ n → L.suc (cut n) ≼ Orbit.value (suc n)
below-next n = ≼-trans {b = OnOrbit.H.parent n} (OnOrbit.H.G.next n)
  (tree-≼ refl (OnOrbit.H.G.hup n) (Orbit.out-h (suc n)))

cofinal : Original.E ≈ᵛ L.lim cut
cofinal = Accept.whole (L.lim cut) (λ n → ≼l {f = cut} n (≼-trans {b = L.suc (Orbit.value n)} (≼-suc (≼-refl _)) (rises n))) ,
  l≼ (λ n → ≼-trans {b = L.suc (cut n)} (≼-suc (≼-refl _)) (≼-trans {b = Orbit.value (suc n)} (below-next n)
    (≼-trans {b = L.suc (Orbit.value (suc n))} (≼-suc (≼-refl _)) (Original.strict (Orbit.target (suc n))))))

enough : (∀ n → cut n ≼ Units.U) → Goal.Goal
enough pay = Unit.unit-to-terminal (≼-trans {b = L.lim cut} (proj₁ cofinal) (l≼ pay))
```
