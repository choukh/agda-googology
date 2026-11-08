# 异层关系保持原统一输入改写

这里的程序逐字为 GenFoldTree.Tree.Int，不重定义算法。
源层与输出层两边均可不同；每个 ni 的坐标低层由原位置给出。
只比较同世界、同未来扩张路径和合法证明。机制继承 ValNewRel.Int-M：
外递归沿输入关系，内递归沿原 Acc 子项；不是给每种事件另写一套。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformGeneratedInt where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst₂)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf
import OCF.Align.GenFoldTree as GT
import OCF.Align.UniformGeneratedBuild as B

module Original (T : KS) where
  module P = GT.Tree T
  open B.General (step T) (ZK T)
  S : KS
  S = step T
  open KS S using () renaming (LgW to LegalW; _≤w_ to _≤_)
  open P using (≤rf; ≤tr)

  outC-old : ∀ {b W k V} (p : k ⊲[ W ] b) (x : Vc b p V) → outC p x ≡ P.outC p x
  outC-old hself x = refl
  outC-old (hsuc p) x = outC-old p x
  outC-old (hlim n p) x = outC-old p x
  outC-old (hLim e p) x = outC-old p x

  outS-old : ∀ {L W k V} (r : StH {S} W k L) (x : Vs L r V) → outS r x ≡ P.outS r x
  outS-old (ss p) x = outC-old p x
  outS-old (sl n p) x = outC-old p x
  outS-old (sL e p) x = outC-old p x

  outC-in : ∀ {b W k V} (p : k ⊲[ W ] b) (x : D k V) → outC p (P.inC p x) ≡ x
  outC-in hself x = refl
  outC-in (hsuc p) x = outC-in p x
  outC-in (hlim n p) x = outC-in p x
  outC-in (hLim e p) x = outC-in p x

  outS-in : ∀ {L W k V} (r : StH {S} W k L) (x : D k V) → outS r (P.inS r x) ≡ x
  outS-in (ss p) x = outC-in p x
  outS-in (sl n p) x = outC-in p x
  outS-in (sL e p) x = outC-in p x

  outward : ∀ {L L′ W k k′ V} (r : StH {S} W k L) (r′ : StH W k′ L′)
    {x : Vs L r V} {y : Vs L′ r′ V} →
    Rel (child r) (child r′) (outS r x) (outS r′ y) → R (P.outS r x) (P.outS r′ y)
  outward r r′ {x} {y} xy = subst₂ R (outS-old r x) (outS-old r′ y) (into (child r) (child r′) xy)

  inward : ∀ {L L′ W k k′ V} (r : StH {S} W k L) (r′ : StH W k′ L′)
    {x : D k V} {y : D k′ V} → R x y →
    Rel (child r) (child r′) (outS r (P.inS r x)) (outS r′ (P.inS r′ y))
  inward r r′ {x} {y} xy = from (child r) (child r′)
    (subst₂ R (sym (outS-in r x)) (sym (outS-in r′ y)) xy)

  prefix : ∀ {L L′ W₀ W} (q : W₀ ≤ W) {f : ℕ → D L W₀} {g : ℕ → D L′ W₀} →
    (∀ n → R (f n) (g n)) → ∀ n → R (P.Pre q f n) (P.Pre q g n)
  prefix q p zero = rz
  prefix q p (suc n) = ra (prefix q p n) (rw (p n))

  Callback : (k k′ l l′ : HB S) (W : Wd S) →
    (∀ {V} → W ≤ V → LegalW V → D k V → D l V) →
    (∀ {V} → W ≤ V → LegalW V → D k′ V → D l′ V) → Set
  Callback k k′ l l′ W u v = ∀ {V} (p : W ≤ V) (lv : LegalW V) {x : D k V} {y : D k′ V} →
    R x y → R (u p lv x) (v p lv y)

  preserve : ∀ {k k′ l l′ W₀ W} (a : AccY {S} k) (a′ : AccY k′)
    {x : D k W₀} {y : D k′ W₀} → R x y → (q : W₀ ≤ W) (lw : LegalW W) →
    (zy : ∀ κ → ZK T k κ → ZK T l κ) (zy′ : ∀ κ → ZK T k′ κ → ZK T l′ κ) →
    (mk : ∀ {V j} → W ≤ V → StH V j k → StH V j l)
    (mk′ : ∀ {V j} → W ≤ V → StH V j k′ → StH V j l′) →
    {u : ∀ {V} → W ≤ V → LegalW V → D k V → D l V}
    {v : ∀ {V} → W ≤ V → LegalW V → D k′ V → D l′ V} →
    Callback k k′ l l′ W u v → {w : D k W} {w′ : D k′ W} → R w w′ →
    R (P.Int a x q lw zy mk u w) (P.Int a′ y q lw zy′ mk′ v w′)
  preserve a a′ rz q lw zy zy′ mk mk′ uv ww = rz
  preserve a a′ ro q lw zy zy′ mk mk′ uv ww = uv ≤rf lw ww
  preserve a a′ (ra px py) q lw zy zy′ mk mk′ uv ww =
    ra (preserve a a′ px q lw zy zy′ mk mk′ uv ww)
       (preserve a a′ py q lw zy zy′ mk mk′ uv (ra ww (rw px)))
  preserve a a′ (rl p) q lw zy zy′ mk mk′ uv ww =
    rl (λ n → preserve a a′ (p n) q lw zy zy′ mk mk′ uv (ra ww (prefix q p n)))
  preserve a a′ (rw {p = p} xy) q lw zy zy′ mk mk′ uv ww =
    preserve a a′ xy (≤tr p q) lw zy zy′ mk mk′ uv ww
  preserve a a′ (rc h) q lw zy zy′ mk mk′ uv ww =
    rc (λ p lv → preserve a a′ (h (≤tr q p) lv) ≤rf lv zy zy′
      (λ p′ → mk (≤tr p p′)) (λ p′ → mk′ (≤tr p p′)) (λ p′ → uv (≤tr p p′)) (rw ww))
  preserve (acc f) (acc g) (ri {r = r} {r′ = r′} shape h) q lw zy zy′ mk mk′ uv ww =
    ri shape (λ p lv x y xy →
      preserve (acc f) (acc g)
        (h (≤tr q p) lv _ _ (inward r r′ (outward (mk ≤rf (GT.Kup q r)) (mk′ ≤rf (GT.Kup q r′)) xy)))
        ≤rf lv zy zy′ (λ p′ → mk (≤tr p p′)) (λ p′ → mk′ (≤tr p p′)) (λ p′ → uv (≤tr p p′))
        (ra (rw ww)
          (preserve (f r) (g r′) (outward (mk ≤rf (GT.Kup q r)) (mk′ ≤rf (GT.Kup q r′)) xy)
            ≤rf lv (GT.zkS r) (GT.zkS r′) (P.mkOf r (≤tr q p)) (P.mkOf r′ (≤tr q p))
            (λ p′ lv′ z → h (≤tr (≤tr q p) p′) lv′ _ _ (inward r r′ z)) rz)))
```

本定理没有把缺失的坐标前缀走法补回：原 GenFold 的 nc 分支仍按原式执行。
它也不提供 read/drop 或原 EvFold 跨历史事件自然性。这里只统一原 Int 的生成关系，
后续实例必须实际给 Callback 与前缀关系，不能从所有 raw 数据自相关推出。
