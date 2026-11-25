# 第一个正反馈下标里的一个低层询问已盖住首座独立标准塔

第四层，无条件。对地址 (1,0) 的首塔运行，沿其第一个正反馈下标选自然极限孩子，直到第一个后继源。该处自槽仍含前两座标准塔，在第一个反馈步读回时已经覆盖 std(1)。[单位预算](W4ReturnCap.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ReturnCapLeaf where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import WVOne using (𝟏; read; h₁)
open import WVTwo using (◃→≼)
import W4Block as W
import W4Fold as F
import W4Ops as O
import W4Path as P
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl)
import B12Terminal as T
import B12ActualSlots as Cov
import B13FiniteLift as S
import B18TowerSlots as Slots
import B18TowerEmb as Emb
import B18Product as M
import B19IdealArithmetic as Ar
import B20Head as Head
import B20StandardInside as Std
import B27URetained as Retain
import B28BFirst as Restrict
import B31Address as Addr
import B31Head as Query
import Survey.W4ReturnCap as Root
open T.Run

raw = λ k → Slots.slots k 2 k W.self
Held : ∀ {k} → T.Run k → Set
Held {k} r = ∀ i (w : i W.≤ k) → Cov._⊴_ (proj₁ (raw i)) (proj₁ (bs r i w))

compose : ∀ {k} {a b c : W.Tr k} → Cov._⊴_ a b → Cov._⊴_ b c → Cov._⊴_ a c
compose ab (inj₁ refl) = ab
compose ab (inj₂ bc) = Cov.extend ab bc

enter : ∀ s h (r : T.Run (W.nd s h)) c x → Held r → Held (T.enterRun s h r c x)
enter s h r c x holds i w = compose (holds i (W.inc c w))
  (Cov.preserve (W.nd s h) (ok r) (bs r) i (W.inc c w) (bs r i (W.inc c w)) x)

module Successor (k : W.L) (r : T.Run (S.sc k)) (holds : Held r) where
  module J = Query.Cell k r
  μ = Retain.eval k J.o J.B (O.Ωt W.zero)
  start = Slots.slots k 1 k W.self
  priced : Std.std 1 ≼ μ (proj₁ (raw k))
  priced = ≼-trans {b = Ar.norm (Std.std 1)} (Ar.up (Std.std 1))
    (≼-trans {b = μ (proj₁ start) M.· Ar.norm (Std.std 1)}
      (M.pad (T.inflate0 k J.o J.B (P.z≤ k) (O.Ωt W.zero) (proj₁ start)) (Ar.norm (Std.std 1)))
      (proj₂ (Retain.At.extension k J.o J.B (O.Ωt W.zero) (proj₁ start) (proj₁ (Emb.standard 1)))))
  original : Cov._⊴_ (proj₁ (raw k)) (J.state 1)
  original = compose (holds k (W.inc tt W.self))
    (Cov.preserve k J.o J.B k W.self J.slot (W.suc W.zero))
  into : Std.std 1 ≼ J.leaf 1
  into = ≼-trans {b = μ (proj₁ (raw k))} priced (compare original)
    where
    compare : ∀ {x y} → Cov._⊴_ x y → μ x ≼ μ y
    compare (inj₁ refl) = ≼-refl _
    compare (inj₂ d) = ◃→≼ (F.mono k J.o J.B W.zero (P.z≤ k) (O.Ωt W.zero) d)

positive-after : ∀ {x y : W.Tr W.zero} → W.zero W.⊢ x ◃ y → W.zero W.⊢ W.zero ◃ y
positive-after {x} p with O.zl x
... | inj₁ refl = p
... | inj₂ g = W.◃t g p

find : ∀ (z : W.Tr W.zero) (r : T.Run (h₁ z)) → Held r → W.zero W.⊢ W.zero ◃ z →
  Σ (Addr.Addr z) (λ p → Std.std 1 ≼ Addr.readAt z r p)
find W.zero r holds p = Data.Empty.⊥-elim (Head.no-zero p)
  where import Data.Empty
find (W.suc z) r holds p = 1 , Successor.into (h₁ z) r holds
find (W.lim g step) r holds p = let a , h = find (g 1) child
                                      (enter W.sL branch r 1 (T.prefix branch 1) holds) (positive-after (step 0))
                                 in (1 , a) , h
  where branch = λ n → h₁ (g n); child = T.limRun branch r 1

module A = Root.Actual
held : Held A.r
held i w = inj₁ (trans (cong proj₁ (sym (Restrict.one (W.tw 1) i w 2)))
  (cong (λ b → proj₁ (b i w)) (sym (Slots.At.all 1 W.zero))))

first = A.A.idx 1
positive : W.zero W.⊢ W.zero ◃ first
positive = proj₂ (F.ψ (W.tw 1) (ok A.r) (bs A.r) W.zero (W.ink W.self) A.A.slot (WVOne.gt W.zero))

opaque
  witness : Σ (Addr.Addr first) (λ p → Std.std 1 ≼ Addr.readAt first (A.A.point 1) p)
  witness = find first (A.A.point 1) (enter (W.sΩ W.zero) h₁ A.r first W.zero held) positive
```
