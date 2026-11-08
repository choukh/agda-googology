# 一般种类统一生成关系：异层、同世界首版

直接使用原 GenFoldIf.DataG S Z，不再定义第一/第二层专属数据。
S 任意 KS，Z 任意层与种类许可。首版的世界配对就是同一实际世界，
高阶分支消费同一个未来扩张路径和合法证明；不声称跨历史自然性。
ni 的两低层各有原 StH 位置（分别在源父层内），并携带 Shape；
不在裸下标上判断或比较。关系不假定所有 raw 数据自相关。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformGeneratedIf where
open import Data.Nat using (ℕ)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf
open import OCF.Align.EventReturnCodeIf using (Shape)

module Family (S : KS) (Z : HB S → K S → Set) where
  open DataG S Z public

  outC : ∀ {b W k V} (p : k ⊲[ W ] b) → Vc b p V → D k V
  outC hself x = x
  outC (hsuc p) x = outC p x
  outC (hlim n p) x = outC p x
  outC (hLim e p) x = outC p x

  outS : ∀ {L W k V} (r : StH {S} W k L) → Vs L r V → D k V
  outS (ss p) = outC p
  outS (sl n p) = outC p
  outS (sL e p) = outC p

  LoT : HB S → HB S → Set₁
  LoT L L′ = ∀ {W k k′} (r : StH W k L) (r′ : StH W k′ L′) →
    Shape k k′ → ∀ {V} → D k V → D k′ V → Set

  module _ {L L′ : HB S} (Lo : LoT L L′) where
    data LayerRel : ∀ {W} → D L W → D L′ W → Set where
      rz : ∀ {W} → LayerRel (n0 {W = W}) n0
      ro : ∀ {W} → LayerRel (n1 {W = W}) n1
      ra : ∀ {W} {a b : D L W} {a′ b′ : D L′ W} →
           LayerRel a a′ → LayerRel b b′ → LayerRel (a ⨾ b) (a′ ⨾ b′)
      rl : ∀ {W} {f : ℕ → D L W} {g : ℕ → D L′ W} →
           (∀ n → LayerRel (f n) (g n)) → LayerRel (nl f) (nl g)
      rw : ∀ {U W} {p : _≤w_ S U W} {x : D L U} {y : D L′ U} →
           LayerRel x y → LayerRel (nw p x) (nw p y)
      rc : ∀ {W κ} {z : Z L κ} {z′ : Z L′ κ}
           {u : ∀ {V} → _≤w_ S W V → LgW S V → D L V}
           {v : ∀ {V} → _≤w_ S W V → LgW S V → D L′ V} →
           (∀ {V} (p : _≤w_ S W V) (lv : LgW S V) → LayerRel (u p lv) (v p lv)) →
           LayerRel (nc κ z u) (nc κ z′ v)
      ri : ∀ {W k k′} {r : StH W k L} {r′ : StH W k′ L′}
           (q : Shape k k′)
           {u : ∀ {V} → _≤w_ S W V → LgW S V → Vs L r V → D L V}
           {v : ∀ {V} → _≤w_ S W V → LgW S V → Vs L′ r′ V → D L′ V} →
           (∀ {V} (p : _≤w_ S W V) (lv : LgW S V) x y →
             Lo r r′ q (outS r x) (outS r′ y) → LayerRel (u p lv x) (v p lv y)) →
           LayerRel (ni r u) (ni r′ v)

  Rel : ∀ {L L′} → AccY {S} L → AccY L′ → ∀ {W} → D L W → D L′ W → Set
  Rel (acc f) (acc g) = LayerRel (λ r r′ q → Rel (f r) (g r′))
```

LayerRel 先对固定 Lo 作严格正归纳；Rel 后按两个原 Acc 下降。
q 是显式低层形状证据，不能由关系反推层相等，也不参与裸比较。
原许可 Z 没有新增封闭公理：每个 nc 的两侧许可分别出现在构造子类型。
