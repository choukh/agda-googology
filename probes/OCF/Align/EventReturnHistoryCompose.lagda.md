# 单侧迁回所需的历史关系组合

只对原事件历史及其 Shape payload 证明组合。不要求任意高层树值
自反或函数同余；`future-left` 的三个输入正是旧基、实际后缀、
两未来历史的关系。它供回调消费，不代替回调本身的相容性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnHistoryCompose where

open import Data.Unit using (tt)
open import Data.List using (_∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.Align.CumReadCF using (Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead using (tp; evx)
open import OCF.Align.EventReturnCodeIf using (Shape; sz; ss; sl; so)
open import OCF.Align.EventReturnCodeBuild using (shape-self)
open import OCF.Align.EventReturnValueEvent
open import OCF.Align.EventReturnHistory

shape-compose : ∀ {S : KS} {a b c : HB S} → Shape a b → Shape b c → Shape a c
shape-compose sz sz = sz
shape-compose (ss p) (ss q) = ss (shape-compose p q)
shape-compose (sl p) (sl q) = sl (λ n → shape-compose (p n) (q n))
shape-compose (so p) (so q) = so (λ e → shape-compose (p e) (q e))

shape-reverse : ∀ {S : KS} {a b : HB S} → Shape a b → Shape b a
shape-reverse sz = sz
shape-reverse (ss p) = ss (shape-reverse p)
shape-reverse (sl p) = sl (λ n → shape-reverse (p n))
shape-reverse (so p) = so (λ e → shape-reverse (p e))

identity : ∀ H → HistLow H H
identity Data.List.[] = empty
identity (e ∷ H) = extend (event-self e) (identity H)

reverse : ∀ {H J} → HistLow H J → HistLow J H
reverse empty = empty
reverse (low lx ly p q) = low ly lx (shape-reverse p) (reverse q)
reverse (forget-left x lx q) = forget-right x lx (reverse q)
reverse (forget-right x lx q) = forget-left x lx (reverse q)

compose : ∀ {H J K} → HistLow H J → HistLow J K → HistLow H K
compose (forget-left x lx p) q = forget-left x lx (compose p q)
compose p (forget-right x lx q) = forget-right x lx (compose p q)
compose (forget-right x lx p) (forget-left .x .lx q) = compose p q
compose empty empty = empty
compose (low lx ly p r) (low .ly lz q s) = low lx lz (shape-compose p q) (compose r s)

original : ∀ {H J} (p : Suf H J) → tp p H ≡ J
original here = refl
original (there e p) = cong (e ∷_) (original p)

future-left : ∀ {H K J J′} → HistLow H K → (s : Suf K J) → HistLow J J′ →
  HistLow (tp s H) J′
future-left {H} p s q = compose
  (subst (λ X → HistLow (tp s H) X) (original s) (drop-context s p)) q

-- 实际 rd₂ 新建事件的 suffix，而非抽象后缀的唯一使用。
future-observed : ∀ {a H K J′} (la : Lg a) → HistLow H K → ∀ x →
  HistLow (evx {a , K} (la , tt) x ∷ K) J′ →
  HistLow (tp (there (evx {a , K} (la , tt) x) here) H) J′
future-observed la p x q = future-left p (there (evx (la , tt) x) here) q
```
