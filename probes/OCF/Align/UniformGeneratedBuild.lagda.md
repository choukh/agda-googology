# 原统一数据的异层生成实例

本篇直接消费原 GenFold 的数据与 Ωd；没有另定义读回、折叠或事件。
可达证明的转换是关系证明，不是证明无关等式。原 Ωd 的全部种类均有实例，
包括未来世界里由 top 选出不同低层的高阶回调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformGeneratedBuild where
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree using (accL; accC)
import OCF.Align.GenFoldTree as GT
open import OCF.Align.EventReturnCodeIf using (Shape; sz; ss; sl; so)
open import OCF.Align.UniformGeneratedIf

module General (S : KS) (Z : HB S → K S → Set) where
  open Family S Z public

  change : ∀ {L L′} (a c : AccY L) (b d : AccY L′) {W}
    {x : D L W} {y : D L′ W} → Rel a b x y → Rel c d x y
  change (acc f) (acc h) (acc g) (acc i) rz = rz
  change (acc f) (acc h) (acc g) (acc i) ro = ro
  change a@(acc f) c@(acc h) b@(acc g) d@(acc i) (ra p q) =
    ra (change a c b d p) (change a c b d q)
  change a@(acc f) c@(acc h) b@(acc g) d@(acc i) (rl p) =
    rl (λ n → change a c b d (p n))
  change a@(acc f) c@(acc h) b@(acc g) d@(acc i) (rw p) =
    rw (change a c b d p)
  change a@(acc f) c@(acc h) b@(acc g) d@(acc i) (rc p) =
    rc (λ q lw → change a c b d (p q lw))
  change a@(acc f) c@(acc h) b@(acc g) d@(acc i) (ri {r = r} {r′ = r′} s p) =
    ri s (λ q lw x y xy → change a c b d
      (p q lw x y (change (h r) (f r) (i r′) (g r′) xy)))

  child : ∀ {L W k} → StH {S} W k L → AccY k
  child (ss p) = accC _ p
  child (sl n p) = accC _ p
  child (sL e p) = accC _ p

  canonical : ∀ {L : HB S} → AccY L
  canonical = acc child

  R : ∀ {L L′ W} → D L W → D L′ W → Set
  R = Rel canonical canonical

  into : ∀ {L L′} (a : AccY L) (b : AccY L′) {W}
    {x : D L W} {y : D L′ W} → Rel a b x y → R x y
  into a b = change a canonical b canonical

  from : ∀ {L L′} (a : AccY L) (b : AccY L′) {W}
    {x : D L W} {y : D L′ W} → R x y → Rel a b x y
  from a b = change canonical a canonical b

module Original (T : KS) (tp : TopG (step T)) where
  module G = General (step T) (ZK T)
  open G
  module OriginalTree = GT.Tree T
  module O = OriginalTree.Om tp

  omega-related : ∀ {L L′} → Shape L L′ → ∀ {W} → R (O.Ωd L {W}) (O.Ωd L′ {W})
  omega-related sz = ro
  omega-related (ss q) = ra ro (ri q (λ p lw x y xy → ro))
  omega-related (sl q) = ra ro (rl (λ n → ri (q n) (λ p lw x y xy → ro)))
  omega-related (so q) = ra ro (rc (λ {W} p lw →
    ri (q (top tp _ W)) (λ p′ lw′ x y xy → ro)))
```

omega-related 不需要任意 raw 数据自相关；ni 的分支本来就是原 Ωd 的 n1。
这只是原生成种子的全层实例。下一输入改写保持须消费相关外回调和相关前缀，
不能从这个实例跳成任意 Run 的自然性，也没有改变原 GenFold nc 不走坐标前缀的规则。
