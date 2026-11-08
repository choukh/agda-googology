# 带种子模型对实际支持的结构同余

回灌产生的坐标只有 Same 时，不能不加条件就把它送入任意 Ω 分支。
使用已在全部实际坐标验证的 Ext；不使用函数外延。
这里的 Same 同余是固定树类型上的值侧结构定理：消费已给的逐构造子证据，
不判定该证据是否存在，不选择层或槽，也不比较不可入下标。
实际更新槽仍是固定第二分量；不能把本结论推广成裸下标分类律。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenOutputModel where

open import Data.Nat using (ℕ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Align.FrozenInnerOuter using (same-refl; same-mul; coordinates-same)
open import OCF.Align.FrozenSupportExt using (Ext; old-ext)
open import OCF.Align.FrozenOutputIf
import OCF.Align.FrozenOutputSim as CS
import OCF.Align.FrozenValueSecond as S

same-trans : ∀ {U} {a b c : HB U} → Same a b → Same b c → Same a c
same-trans zz zz = zz
same-trans (ss p) (ss q) = ss (same-trans p q)
same-trans (ll p) (ll q) = ll (λ n → same-trans (p n) (q n))
same-trans (oo p) (oo q) = oo (λ c → same-trans (p c) (q c))

update-same : ∀ m {a b c d} → Same a b → Same c d → Same (update m a c) (update m b d)
update-same changing p q = q
update-same frozen p q = p

module Congruence (A : Cd) where
  open Model A

  run-same : ∀ m c → Ext c → ∀ {d} → Same c d → ∀ {a b} → Same a b →
    Same (run m a c) (run m b d)
  run-same m hz ec zz p = same-refl A
  run-same m (hs c) ec (ss q) p = ll (same-mul (run-same m c ec q p))
  run-same m (hl f) ec (ll q) p = ll (λ n → run-same m (f n) (ec n) (q n) p)
  run-same m (hΩ (inj₁ ()) g) ec q p
  run-same m (hΩ (inj₂ tt) g) (respect , eg) (oo {g = h} q) {a} {b} p =
    ll (CS.Sim.sums Same a b p a b p (update m) (update m) (update-same m)
      (λ w e → run m w (g e)) (λ w e → run m w (h e))
      (λ w e → run m w (g e)) (λ w e → run m w (h e))
      rec-step rec-step)
    where
    rec-step : ∀ {w v x y} → Same w v → Same x y → Same (run m w (g x)) (run m v (h y))
    rec-step {x = x} {y} rw xy = run-same m (g x) (eg x) (same-trans (respect xy) (q y)) rw

  actual-coordinate-congruence : ∀ m b n →
    Same (run m b (S.Old.ce n)) (run m b (S.Frozen.ce n))
  actual-coordinate-congruence m b n = run-same m _ (old-ext n)
    (coordinates-same n) (same-refl b)
```

这消除了模型中原/冻结外层坐标的表示差异，覆盖全部 n 和任意种子 b。
它比较相同 mode；changing 与 frozen 之间的吸收仍未证明。
实际 OT/NT 到模型的桥也仍是独立义务。
