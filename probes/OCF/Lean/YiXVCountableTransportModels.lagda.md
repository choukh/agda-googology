# YiXVCountableTransportModels
> 验收文件。档位：编译定理。零层、一层的正反向搬运完整实例，先于一般构造实填所有字段。
> 推广 YiXVFiniteFamily/Level 的结构递归；共享映射证明供搬运与加法复用。未证明可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableTransportModels where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableMapInput as V
import OCF.Lean.YiXVCountableMap as Map
import OCF.Lean.YiXVCountableTransportInput as Q

data Dir : Set where forward backward : Dir
other : Dir → Dir
other forward = backward
other backward = forward
-- 零层、一层闭实例使用构造子的自反证明，两向端点均字面相等。
z : Dir → L.Ordᶜ L.zero → L.Ordᶜ L.zero
z forward = L.tr L.z≅
z backward = L.tr⁻ L.z≅
o : Dir → L.Ordᶜ (L.suc L.zero) → L.Ordᶜ (L.suc L.zero)
o forward = L.tr (L.s≅ L.z≅)
o backward = L.tr⁻ (L.s≅ L.z≅)
zc : ∀ d {X Y} → X L.≅ Y → z d X L.≅ z d Y
zc forward e = L.≅-trans (L.tr-≅ L.z≅ e) (L.≅-sym (L.tr-≅ L.z≅ (L.≅-trans (L.≅-sym e) e)))
zc backward e = L.≅-trans (L.tr⁻-≅ L.z≅ e) (L.≅-sym (L.tr⁻-≅ L.z≅ (L.≅-trans (L.≅-sym e) e)))
oc : ∀ d {X Y} → X L.≅ Y → o d X L.≅ o d Y
oc forward e = L.≅-trans (L.tr-≅ (L.s≅ L.z≅) e) (L.≅-sym (L.tr-≅ (L.s≅ L.z≅) (L.≅-trans (L.≅-sym e) e)))
oc backward e = L.≅-trans (L.tr⁻-≅ (L.s≅ L.z≅) e) (L.≅-sym (L.tr⁻-≅ (L.s≅ L.z≅) (L.≅-trans (L.≅-sym e) e)))
zero : ∀ d → V.View L.zero L.zero (z d)
V.View.zero (zero forward) = A.Zero.gz
V.View.zero (zero backward) = A.Zero.gz
V.View.suc (zero forward) X = refl
V.View.suc (zero backward) X = refl
V.View.lim (zero forward) f = refl
V.View.lim (zero backward) f = refl
V.View.node (zero d) ()
V.View.node-shape (zero d) () f
V.View.up (zero d) ()
V.View.up-shape (zero d) () X
V.View.cong (zero d) e = zc d e

gz : ∀ d {X} → A.Gd X → A.Gd (z d X)
gz d = Map.Map.good (z d) (zero d)
mz : ∀ d {X Y} → A.Le X Y → A.Le (z d X) (z d Y)
mz d = Map.Map.mono (z d) (zero d)
tz : ∀ d {X} → A.Gd X → z d X L.≅ X
tz forward gx = L.tr-≅ L.z≅ (A.self gx)
tz backward gx = L.tr⁻-≅ L.z≅ (A.self gx)
zero-ops : Q.Ops L.z≅ refl
Q.Ops.good zero-ops = gz forward
Q.Ops.mono zero-ops = mz forward
Q.Ops.minus-good zero-ops = gz backward
Q.Ops.minus-mono zero-ops = mz backward

zs : ∀ d X → z d (L.suc X) ≡ L.suc (z d X)
zs forward X = refl
zs backward X = refl
zf : ∀ d {X} → A.Le (L.Ω L.zero) X → A.Le (L.Ω L.zero) (z d X)
zf forward t = mz forward t
zf backward t = mz backward t
pull0 : ∀ d → V.Pull {L.suc L.zero} {L.suc L.zero} L.zero
pull0 d = record
  { index = L.zero ; bound = L.zero ; same = refl
  ; raw = z (other d) ; back = z (other d)
  ; input = λ X → refl
  ; good = gz (other d) ; mono = mz (other d)
  ; floor = zf (other d) ; suc = zs (other d)
  ; transparent = tz (other d) }
og : ∀ d → A.Gd (o d L.zero)
og forward = A.One.gz
og backward = A.One.gz
os : ∀ d X → o d (L.suc X) ≡ L.suc (o d X)
os forward X = refl
os backward X = refl
ol : ∀ d f → o d (L.lim f) ≡ L.lim (λ n → o d (f n))
ol forward f = refl
ol backward f = refl
on : ∀ d {i} (q : i L.<ᴵ L.suc L.zero) → V.Pull {L.suc L.zero} {L.suc L.zero} q
on d L.zero = pull0 d
on d (L.suc ())
ons : ∀ d {i} (q : i L.<ᴵ L.suc L.zero) f →
  o d (L.limᵢ q f) ≡ L.limᵢ (V.Pull.bound (on d q)) (λ u → o d (f (V.Pull.raw (on d q) u)))
ons forward L.zero f = refl
ons backward L.zero f = refl
ons d (L.suc ()) f
ur : ∀ d {X} → A.Gd X → A.Le (o d L.zero) (A.Up L.zero (z d X))
ur forward gx = A.Basics.z≤ (L.suc L.zero) (A.Basics.up (L.suc L.zero) L.zero (gz forward gx))
ur backward gx = A.Basics.z≤ (L.suc L.zero) (A.Basics.up (L.suc L.zero) L.zero (gz backward gx))
ou : ∀ d {i} (r : i L.◃₁ L.suc L.zero) → V.Child r (o d L.zero)
ou d L.zero = record
  { map = λ X → A.Up L.zero (z d X)
  ; good = λ gx → A.Basics.up (L.suc L.zero) L.zero (gz d gx)
  ; mono = λ t → A.Basics.up-mono (L.suc L.zero) L.zero (mz d t)
  ; right = ur d }
ous : ∀ d {i} (r : i L.◃₁ L.suc L.zero) X → o d (A.Up r X) ≡ V.Child.map (ou d r) X
ous forward L.zero X = refl
ous backward L.zero X = refl
one : ∀ d → V.View (L.suc L.zero) (L.suc L.zero) (o d)
one d = record { zero = og d ; suc = os d ; lim = ol d ; node = on d
  ; node-shape = ons d ; up = ou d ; up-shape = ous d ; cong = oc d }

one-ops : Q.Ops (L.s≅ L.z≅) refl
Q.Ops.good one-ops = Map.Map.good (o forward) (one forward)
Q.Ops.mono one-ops = Map.Map.mono (o forward) (one forward)
Q.Ops.minus-good one-ops = Map.Map.good (o backward) (one backward)
Q.Ops.minus-mono one-ops = Map.Map.mono (o backward) (one backward)
actual : A.Gd (L.tr (L.s≅ L.z≅) (L.Ω (L.suc L.zero)))
actual = Q.Ops.good one-ops A.oneΩ
```
