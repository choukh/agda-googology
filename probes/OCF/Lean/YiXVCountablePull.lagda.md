# YiXVCountablePull
> 验收文件。档位：编译定理。由原 Restr 的回搬保持律构造统一节点接口，含零层完整实例。
> 推广 YiXVFiniteFamily/Level 的结构递归；共享映射证明供搬运与加法复用。未证明可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountablePull where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Product using (proj₁)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as Omega
import OCF.Lean.YiXVCountableMapInput as V
import OCF.Lean.YiXVCountableRep as Rep
import OCF.Lean.YiXVCountableTransportInput as Q
import OCF.Lean.YiXVCountableTransportModels as Model

record Back {i ν} (r : L.Restr i ν) : Set where
  field
    good : ∀ {X} → A.Gd X → A.Gd (L.Restr.back r X)
    mono : ∀ {X Y} → A.Le X Y → A.Le (L.Restr.back r X) (L.Restr.back r Y)

make : ∀ {κ ν i} (q : i L.<ᴵ κ) (r : L.Restr i ν) → i ≡ L.Restr.rep r → Back r →
  (∀ X → L.Restr.back r (L.suc X) ≡ L.suc (L.Restr.back r X)) →
  L.Restr.back r (L.Ω (L.Restr.rep r)) L.≅ L.Ω i →
  (∀ {X} → A.Gd X → L.Restr.back r X L.≅ X) → V.Pull {κ} {ν} q
V.Pull.index (make q r same bk su om tr) = L.Restr.rep r
V.Pull.bound (make q r same bk su om tr) = L.Restr.lt r
V.Pull.same (make q r same bk su om tr) = same
V.Pull.raw (make q r same bk su om tr) u = L.into (L.<→◃ q) (L.Restr.back r (L.out (L.<→◃ (L.Restr.lt r)) u))
V.Pull.back (make q r same bk su om tr) X = L.Restr.back r X
V.Pull.input (make q r same bk su om tr) X = cong (λ Z → L.into (L.<→◃ q) (L.Restr.back r Z)) (L.out-into (L.<→◃ (L.Restr.lt r)) X)
V.Pull.good (make q r same bk su om tr) = Back.good bk
V.Pull.mono (make q r same bk su om tr) = Back.mono bk
V.Pull.floor (make {i = i} q r same bk su om tr) t = A.Layer.trans i A.Gd< A.Le<
  (A.Layer.pack (proj₁ (Omega.model i)) (Back.good bk (proj₁ (Omega.model (L.Restr.rep r)))) (A.Layer.ce (L.≅-sym om)))
  (Back.mono bk t)
V.Pull.suc (make q r same bk su om tr) X = su X
V.Pull.transparent (make q r same bk su om tr) = tr

zero-back : Back (L.res (L.zero {a = L.zero}) (L.s≅ L.z≅))
Back.good zero-back = Q.Ops.minus-good Model.zero-ops
Back.mono zero-back = Q.Ops.minus-mono Model.zero-ops
actual : V.Pull {L.suc L.zero} {L.suc L.zero} L.zero
actual = make L.zero (L.res L.zero (L.s≅ L.z≅)) refl zero-back (Rep.plus-suc L.zero (L.s≅ L.z≅))
  (Rep.plus-Ω L.zero (L.s≅ L.z≅)) (λ gx → L.back-≅ L.zero (L.s≅ L.z≅) (A.self gx))
```
