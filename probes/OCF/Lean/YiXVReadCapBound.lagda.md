# YiXVReadCapBound
> 验收文件。档位：编译定理。每个实际源 x 的 cap 不大于以 read x 为下标、目标取 lvl x 的原零源层折叠。
> 复用 Level、CountableFold/MapCompare 与 ReadOmega 的构造，完整实例见代码；未接实际源世界或原外层 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadCapBound where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLSTw1 as T
import OCF.Lean.YiLSRead as Read
import OCF.Align.Level as L
open import OCF.Align.Value using (≺→s≼)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as Ω
import OCF.Lean.YiXVCountableFloor as Floor
import OCF.Lean.YiXVCountableGroundValue as Ground
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadOmega as C
import OCF.Lean.YiXVReadOmegaLimit as Limit
open import OCF.Lean.YiXVLvlSteps using (read-strong)
import OCF.Lean.YiXVRefLift as E
import OCF.Lean.YiXVRefAlgebra as R
import OCF.Lean.YiXVFlatInput as F
import OCF.Lean.YiXVFlatGround as FG

upper : ∀ x → L.Ordᶜ (T.lvl x)
upper x = F.flat (T.lvl x) (F.empty (T.lvl x)) (Read.read x)
good-upper : ∀ x → A.Gd (upper x)
good-upper x = F.good {κ = L.zero} {ν = T.lvl x} tt (read-strong x) (F.empty (T.lvl x)) (Ground.good (Read.read x))
floor : ∀ x → A.Le (L.Ω (T.lvl x)) (upper x)
floor x = Floor.floor (L.zero {a = T.lvl x}) (F.insert (F.empty (T.lvl x))) (Read.read x) (good-upper x)
mutual
  bound : ∀ x → A.Le (C.cap x) (upper x)
  bound S.zero = A.Layer.rfl L.zero A.Gd< A.Le< A.groundΩ
  bound (S.suc x) = R.sum-ω
    (Floor.floor (L.zero {a = T.lvl (S.suc x)}) (F.insert (F.empty (T.lvl (S.suc x)))) (Read.read x)
      (F.good {κ = L.zero} {ν = T.lvl (S.suc x)} tt (read-strong (S.suc x)) (F.empty (T.lvl (S.suc x))) (Ground.good (Read.read x))))
    (Floor.floor (L.zero {a = T.lvl (S.suc x)}) (F.insert (F.empty (T.lvl (S.suc x)))) (Read.read x)
      (F.good {κ = L.zero} {ν = T.lvl (S.suc x)} tt (read-strong (S.suc x)) (F.empty (T.lvl (S.suc x))) (Ground.good (Read.read x))))
  bound x@(S.lim f a) = finish f a
  bound (S.Ω () g)
  bound (S.up x () y e)

  finish : ∀ f (a : ∀ n → S.zero S.⊢ f n ◃ f (suc n)) →
    A.Le (C.cap (S.lim f a)) (upper (S.lim f a))
  finish f a = D.pack M.good (good-upper x) (D.ll (λ n →
    D.pack (M.good-partial n) (good-upper x) (D.lr (suc n) (D.trans (partial n) (next n)))))
    where
    x = S.lim f a
    κ = T.lvl x
    module D = A.Layer κ A.Gd< A.Le<
    module M = Limit.Limit f a (λ n → C.cap (f n)) (C.branches f)
    row : ℕ → L.Ordᶜ κ
    row n = F.flat κ (F.empty κ) (Read.read (f n))
    good-row : ∀ n → A.Gd (row n)
    good-row n = F.good {κ = L.zero} {ν = T.lvl x} tt (read-strong x) (F.empty (T.lvl x)) (Ground.good (Read.read (f n)))
    next : ∀ n → A.Le (F.flat κ (F.empty κ) (L.suc (Read.read (f n)))) (row (suc n))
    next n = F.mono {κ = L.zero} {ν = κ} tt (read-strong x) (F.empty κ) (F.empty κ)
      (Ground.native (≺→s≼ (Read.◃→≺ (a n))))
    child : ∀ n → A.Le (E.embedded (J.σchild x n) (C.cap (f n))) (row n)
    child n = D.trans (E.embedded-mono {σ = J.σchild x n} (bound (f n)))
      (FG.bound {a = T.lvl (f n)} {b = κ} (read-strong (f n)) (read-strong x) (J.q x (n , inj₁ tt))
        (J.σchild x n) (F.empty (T.lvl (f n))) (F.empty κ) (Read.read (f n)))
    partial : ∀ n → A.Le (M.partial n) (F.flat κ (F.empty κ) (L.suc (Read.read (f n))))
    partial zero = D.trans (R.split (J.σchild x zero) (proj₁ (Ω.model κ)) (C.good (f zero)))
      (R.sum-ω (Floor.floor (L.zero {a = κ}) (F.insert (F.empty κ)) (Read.read (f zero)) (good-row zero)) (child zero))
    partial (suc n) = D.trans (R.split (J.σchild x (suc n)) (M.good-partial n) (C.good (f (suc n))))
      (R.sum-ω (D.trans (partial n) (next n)) (child (suc n)))

actual : A.Le (C.cap (S.suc S.zero)) (upper (S.suc S.zero))
actual = bound (S.suc S.zero)
```
