# 纯可数折叠与已有验收折叠的值桥

验收专用。这里不改变P、旧闭项或完成项。P one的后继基本列从一份
起，而Level.ψ⁰从零份起；有限加法先左右结合再作错位共尾比较。
结论是全部可数输入的双向值界，不是基本列逐项一致。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionPureAccept where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; same-sym)
open import OCF.Align.FrozenInnerOuter using (same-refl; same-add)
open import OCF.Align.FrozenOutputModel using (same-trans)
open import OCF.Align.FrozenAbsorbNegUpper using (P; assoc)
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.Level as L
import OCF.Align.OCFSpecBase as V
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

one : Cd
one = hs hz
F : Cd → Cd
F = P one

left : Cd → ℕ → Cd
left a zero = hz
left a (suc n) = a ⊞ left a n

zero-left : ∀ (a : Cd) → Same (hz ⊞ a) a
zero-left hz = zz
zero-left (hs a) = ss (zero-left a)
zero-left (hl f) = ll (λ n → zero-left (f n))

rotate : ∀ (a : Cd) n → Same (left a n ⊞ a) (left a (suc n))
rotate a zero = zero-left a
rotate a (suc n) = same-trans (same-sym (assoc a (left a n) a))
  (same-add (same-refl a) (rotate a n))

mul-left : ∀ (a : Cd) n → Same (mul a n) (left a (suc n))
mul-left a zero = same-refl a
mul-left a (suc n) = same-trans (same-add (mul-left a n) (same-refl a))
  (rotate a (suc n))

read-same : ∀ {a b : Cd} → Same a b → B.read a L.≅ B.read b
read-same zz = L.z≅
read-same (ss p) = L.s≅ (read-same p)
read-same (ll p) = L.l≅ (λ n → read-same (p n))

read-add : ∀ (a b : Cd) → B.read (a ⊞ b) L.≅ (B.read a L.+ B.read b)
read-add a hz = L.≅-refl⁰ (B.read a)
read-add a (hs b) = L.s≅ (read-add a b)
read-add a (hl f) = L.l≅ (λ n → read-add a (f n))

read-left : ∀ (a : Cd) n → B.read (left a n) L.≅
  iter (B.read a L.+_) L.zero n
read-left a zero = L.z≅
read-left a (suc n) = L.≅-trans (read-add a (left a n))
  (L.add-≅ (L.≅-refl⁰ (B.read a)) (read-left a n))

read-mul : ∀ (a : Cd) n → B.read (mul a n) L.≅
  iter (B.read a L.+_) L.zero (suc n)
read-mul a n = L.≅-trans (read-same (mul-left a n)) (read-left a (suc n))

iter-mono : ∀ (a b : L.Ordᶜ L.zero) → a V.≼ b → ∀ n →
  iter (a L.+_) L.zero n V.≼ iter (b L.+_) L.zero n
iter-mono a b p zero = V.z≼
iter-mono a b p (suc n) = V.+-mono p (iter-mono a b p n)

F≤ψ : ∀ c → B.read (F c) V.≼ L.ψ⁰ (B.read c)
F≤ψ hz = V.≼-refl _
F≤ψ (hs c) = V.l≼ (λ n → V.≼l (suc n)
  (V.≼-trans (V.≅→≼ (read-mul (F c) n))
    (iter-mono _ _ (F≤ψ c) (suc n))))
F≤ψ (hl f) = V.l≼ (λ n → V.≼l n (F≤ψ (f n)))

ψ≤F : ∀ c → L.ψ⁰ (B.read c) V.≼ B.read (F c)
ψ≤F hz = V.≼-refl _
ψ≤F (hs c) = V.l≼ branch
  where
  branch : ∀ n → iter (L.ψ⁰ (B.read c) L.+_) L.zero n V.≼ B.read (F (hs c))
  branch zero = V.z≼
  branch (suc n) = V.≼l n
    (V.≼-trans (iter-mono _ _ (ψ≤F c) (suc n))
      (V.≅→≼ (L.≅-sym (read-mul (F c) n))))
ψ≤F (hl f) = V.l≼ (λ n → V.≼l n (ψ≤F (f n)))

```

这只在纯可数输入上比较值；没有推导含Ω节点的折叠同余，也没有把
值桥当作原路径或合法性证明。记号未进入P、原闭项或完成证书。
