# 原合法可数高度的同形参照层

验收专用。直接把原Cd高度及其合法证读成旧Ordᴵ层，不先完成输入。
原位置只提供前驱包含；种类实际秩带hs i⊲B时，才给严格旧层路径。
较小侧合法证沿该路径取出，避免假定任意合法证据相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedHeight where
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as B

position-sub : ∀ {a C : Cd} → a ⊲ C → B.read a L.⊑⁰ B.read C
position-sub hself h = h
position-sub (hsuc p) h = L.≺s (position-sub p h)
position-sub (hlim n p) h = L.≺l n (position-sub p h)
position-sub (hLim {κ = ()} e p) h

native-HS : ∀ C → LgB C → L.HS (B.read C)
native-HS hz lC = L.hz
native-HS (hs C) lC = L.hs (native-HS C lC)
native-HS (hl f) (st , sub) = L.hl (λ n → native-HS (f n) (sub n))
  (λ n → position-sub (st n))
native-HS (hΩ () f) lC

height : ∀ C → LgB C → L.Ordᴵ
height C lC = L.toLevel (B.read C) (native-HS C lC)
index-bound : ∀ {i C : Cd} (lC : LgB C) (p : hs i ⊲ C) →
  height i (lgB⊲ p tt lC) L.<ᴵ height C lC
index-bound lC hself = L.zero
index-bound lC (hsuc p) = L.suc (index-bound lC p)
index-bound lC (hlim n p) = L.lim n (index-bound (proj₂ lC n) p)
index-bound lC (hLim {κ = ()} e p)

height-position : ∀ {a C : Cd} la lC → a ⊲ C → height a la L.⊑ᴵ height C lC
height-position {a} {C} la lC p = L.toLevel-⊑ (native-HS a la) (native-HS C lC) (position-sub p)
read-shape : ∀ {a b : Cd} → Same a b → B.read a L.≅ B.read b
read-shape zz = L.z≅
read-shape (ss p) = L.s≅ (read-shape p)
read-shape (ll p) = L.l≅ (λ n → read-shape (p n))
read-shape (oo {κ = ()} p)
height-shape : ∀ {a b : Cd} (p : Same a b) la lb → height a la L.≅ᴵ height b lb
height-shape {a} {b} p la lb = L.toLevel-≅ (native-HS a la) (native-HS b lb) (read-shape p)

rank-legal : ∀ {i C : Cd} (p : hs i ⊲ C) lC →
  lgB⊲ (⊲ᴮ-tr (hsuc hself) p) tt lC ≡ lgB⊲ p tt lC
rank-legal hself lC = refl
rank-legal (hsuc p) lC = rank-legal p lC
rank-legal (hlim n p) lC = rank-legal p (proj₂ lC n)
rank-legal (hLim {κ = ()} e p) lC
```

height-shape只给结构等价，不给层的字面相等；后续坐标须保留tr⁻。
index-bound正好覆盖原cl生成的种类秩，未把任意a⊲C反射为严格<ᴵ。
本篇没有把toLevel(γ₁)认成双重完成高度，也没有给Γ的值界。
