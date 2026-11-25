# 第二座标准塔支付任意多个真实重复块

第四层。每块从第零个孩子把变换后的预算送入实际正下标。指定孩子路径的输出即使重置了环境，仍能从首个正下标的独立运行取回同一数值。因此同一个块可以对所有零路径反复提升值律。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4NextLiftBlock where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum.Base using (inj₁)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (subst; sym; refl)
import W4Block as W
import W4Ops as O
import W4Path as P
import W4Fold as F
import WKGen as Node
open import WVOne using (T₀; read; 𝟏; h₁)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≼l; l≼)
import B12Terminal as T
import B12ActualSlots as C
import B14Tower as V
import B15ReadPaths as R
import B15Spine as S
import B15TowerIteration as Iter
import B19RowSecondParent as Add
import B20Room as Room
import B20StandardInside as Std
import Survey.W4RoomHeight as H
import Survey.W4RoomDerivative as D
import Survey.W4NextLiftIndex as I
open T.Run

w = W.↑ (W.tw 1) (proj₁ (O.Ωt (W.tw 1)))
family = λ c → W.zero W.⊕ I.diag c
module Block (p : List W.L) (f : T₀ → T₀) (pay : H.Law (I.plug p (family W.zero)) f) where
  child = λ c → I.plug p (family c)
  root = W.nd (W.sΩ W.zero) child
  module At (r : T.Run root) (cv : C.Covered r) (x : T₀) (high : Room.Room r x) where
    module A = S.Cardinal W.zero child r
    initial = A.child 0
    old = λ t → high (W.inc W.zero t)
    old-cv = A.cover cv 0
    ir = V.reset initial (bs r W.zero (W.ink W.self)) (oneB r (W.ink W.self))
    z = A.ix 1
    fund : f x ≼ read z
    fund = pay ir old-cv x old (W.self W.∙ proj₂ (proj₁ (ok r)) W.zero)
    call = λ u z → F.ψ root (ok r) (bs r) W.zero u (β r) (A.b z)
    node = λ u → read (proj₁ (F.node⁺ (F.kp root (ok r) A.p u) (call u) A.step))
    within : ∀ u n → read (proj₁ (call u (A.ix n))) ≼ node u
    within u n = Node.node-ge (F.kp root (ok r) A.p u) (call u) A.step n
    reset = T.initial (child z) (proj₂ (ok r) z)
    independent : f x ≼ read (T.value reset)
    independent = ≼-trans fund (I.growth z (W.zero ∷ p) reset (C.initial (child z) (ok reset)))
    all : ∀ u → f x ≼ V.valueAt r u
    all (W.inu us) = ≼-trans (pay initial old-cv x old (us W.zero)) (within (W.inu us) 0)
    all (W.ink W.self) = ≼-trans (pay initial old-cv x old (W.self W.∙ proj₂ (proj₁ (ok r)) W.zero))
      (within (W.ink W.self) 0)
    all (W.inc c u) = ≼-trans independent (≼-trans
      (Add.append (β r) (F.ψ₀ (child z) (ok reset) (proj₁ (O.Ωt (child z))))) (within (W.inc c u) 1))

  law : H.Law (I.plug p w) f
  law = subst (λ l → H.Law l f) (sym (I.node p (W.sΩ W.zero) family)) At.all

tiles = W.iter (W._⊕ w) w
level : ℕ → W.L
level zero = W.tw 1
level (suc n) = W.tw 1 W.⊕ tiles n
op = W.iter H.repeat D.next
all : ∀ n → H.Law (level n) (op n)
all zero = D.law
all (suc zero) = Block.law (W.tw 1 ∷ []) (op 1)
  (H.Successor.all (W.sΩ W.zero) h₁ (op 0) (all 0))
all (suc (suc zero)) = Block.law (w ∷ W.tw 1 ∷ []) (op 2)
  (H.Successor.all (W.sΩ W.zero) (λ c → W.tw 1 W.⊕ family c) (op 1) (all 1))
all (suc (suc (suc n))) = Block.law (tiles (suc n) ∷ W.tw 1 ∷ []) (op (suc (suc (suc n))))
  (H.Successor.all (W.sΩ W.zero) (λ c → W.tw 1 W.⊕ (tiles n W.⊕ family c)) (op (suc (suc n))) (all (suc (suc n))))

```
