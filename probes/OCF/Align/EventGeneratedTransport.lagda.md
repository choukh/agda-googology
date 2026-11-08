# 同世界 Shape 层间的实际数据转换

本实验保留原 D 的全部构造子。ni 的低坐标沿对应低层反向转换，
外回调返回的数据再正向转换；两个 Acc 的内调用都取原子证明。
不使用 accessible 产生的新 Acc 作为终止依据，不假定函数外延。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventGeneratedTransport where
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EventReturnCodeIf using (Shape; sz; ss; sl; so)
open import OCF.Align.EventGeneratedPath using (node; reverse)

nonzero : ∀ {L L′} → Shape L L′ → NZ L → NZ L′
nonzero sz ()
nonzero (ss p) z = tt
nonzero (sl p) z = tt
nonzero (so p) z = tt

nonone : ∀ {L L′} → Shape L L′ → NZ₁ L → NZ₁ L′
nonone sz ()
nonone (ss p) z = nonzero p z
nonone (sl p) z = tt
nonone (so p) z = tt

nontwo : ∀ {L L′} → Shape L L′ → NZ₂ L → NZ₂ L′
nontwo sz ()
nontwo (ss p) z = nonone p z
nontwo (sl p) z = tt
nontwo (so p) z = tt

allowed : ∀ κ {L L′} → Shape L L′ → ZE κ L → ZE κ L′
allowed (_ , hself) p z = nontwo p z
allowed (_ , hsuc hself) p z = nonone p z

record Maps (L L′ : Ht) : Set where
  field
    forward : ∀ {W} → D L W → D L′ W
    backward : ∀ {W} → D L′ W → D L W
open Maps

maps : ∀ {L L′} → AccY L → AccY L′ → Shape L L′ → Maps L L′
maps {L} {L′} (acc f) (acc f′) p = record { forward = go ; backward = back }
  where
  go : ∀ {W} → D L W → D L′ W
  go n0 = n0
  go n1 = n1
  go (x ⨾ y) = go x ⨾ go y
  go (nl d) = nl (λ n → go (d n))
  go (ni r u) with node p r
  ... | k′ , q , r′ = ni r′ (λ w lw y →
    go (u w lw (inS r (backward (maps (f r) (f′ r′) q) (outS r′ y)))))
  go (nκ z u) = nκ (nonzero p z) (λ q lc → go (u q lc))
  go (nε κ z u) = nε κ (allowed κ p z) (λ q lw → go (u q lw))
  go (nw q x) = nw q (go x)

  back : ∀ {W} → D L′ W → D L W
  back n0 = n0
  back n1 = n1
  back (x ⨾ y) = back x ⨾ back y
  back (nl d) = nl (λ n → back (d n))
  back (ni r′ u) with node (reverse p) r′
  ... | k , q , r = ni r (λ w lw y →
    back (u w lw (inS r′ (forward (maps (f r) (f′ r′) (reverse q)) (outS r y)))))
  back (nκ z u) = nκ (nonzero (reverse p) z) (λ q lc → back (u q lc))
  back (nε κ z u) = nε κ (allowed κ (reverse p) z) (λ q lw → back (u q lw))
  back (nw q x) = nw q (back x)

retype : ∀ {L L′ W} → AccY L → AccY L′ → Shape L L′ → D L W → D L′ W
retype ac ac′ p = forward (maps ac ac′ p)

untype : ∀ {L L′ W} → AccY L → AccY L′ → Shape L L′ → D L′ W → D L W
untype ac ac′ p = backward (maps ac ac′ p)

```

这是实际同世界数据转换，不是两世界 Run 自然性。两向转换分别为 retype 与 untype，始终固定两个 Acc 的顺序；未断言往返的高阶函数字面等于原函数。
