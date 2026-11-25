# YiXVSourceRefPath
> 验收文件。档位：编译定理。参照有限路径的提升、加法展开与 Ω 倍数界。
> 接 YiXVSourceSem、SourceAffine*、Finite*，有限搬运比较参照 YiXVCan2Embed；未交完整外层链或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceRefPath where
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import Data.Fin as F
import OCF.Align.Level as L
open import OCF.Lean.YiASIface using (Sbᶠ; s0; ss)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceWorldInput as W
import OCF.Lean.YiXVSourceEmbed as E

ref : ∀ {n m} → Sbᶠ n m → P.Path n m
ref s0 = P.top
ref (ss s) = P.down (W.up (ref s))
lift : ∀ {H n} → P.Path H n → I.T n → I.T H
lift P.top X = X
lift (P.down p) X = lift p (L.up L.zero X)
good : ∀ {H n} (p : P.Path H n) X → A.Gd n X → A.Gd H (lift p X)
good P.top X gx = gx
good {n = n} (P.down p) X gx = good p (L.up L.zero X) (A.Layer.gu {n = n} gx)
mono : ∀ {H n} (p : P.Path H n) X Y → A.Le n X Y → A.Le H (lift p X) (lift p Y)
mono P.top X Y t = t
mono {n = n} (P.down p) X Y t = mono p (L.up L.zero X) (L.up L.zero Y)
  (D.u≤ (B.left n F.zero {X = X} {Y = Y} t) (B.right n F.zero {X = X} {Y = Y} t) t)
  where module D = A.Layer n (A.GoFam n) (A.LeFam n)
shape : ∀ {H n} (p : P.Path H n) (Z : I.T H) X → L.add Z (P.σ p) X ≡ Z L.+ lift p X
shape P.top Z X = refl
shape (P.down p) Z X = shape p Z (L.up L.zero X)
mult : ∀ {H n} (p : P.Path H n) k → A.Le H (lift p (E.M n k)) (E.M H k)
mult P.top k = B.rfl _ F.zero {X = E.M _ k} (E.mg _ k)
mult {H} {n} (P.down p) k = B.trans H F.zero {X = lift p (L.up L.zero (E.M n k))}
  {Y = lift p (E.M (suc n) k)} {Z = E.M H k} (mono p _ _ (E.up-M n k)) (mult p k)
M-mono : ∀ n {k l} → k ≤ l → A.Le n (E.M n k) (E.M n l)
M-mono n {k = zero} {l = l} z≤n = B.z≤ n F.zero {Y = E.M n l} (E.mg n l)
M-mono n {k = suc k} {l = suc l} (s≤s t) = Add.plus n {X = E.Ω n} {X′ = E.Ω n} {Y = E.M n k} {Y′ = E.M n l}
  (B.rfl n F.zero {X = E.Ω n} (B.actual n)) (M-mono n t)
add-bound : ∀ {H n} (p : P.Path H n) Z X k → A.Gd H Z → A.Le n X (E.M n k) →
  A.Le H (L.add Z (P.σ p) X) (Z L.+ E.M H k)
add-bound {H} p Z X k gz t = subst (λ v → A.Le H v (Z L.+ E.M H k)) (sym (shape p Z X))
  (Add.plus H {X = Z} {X′ = Z} {Y = lift p X} {Y′ = E.M H k} (B.rfl H F.zero {X = Z} gz)
    (B.trans H F.zero {X = lift p X} {Y = lift p (E.M _ k)} {Z = E.M H k} (mono p _ _ t) (mult p k)))

actual : A.Le 3 (L.add (E.Ω 3) (P.σ (ref (ss (ss s0)))) (E.cap s0)) (E.Ω 3 L.+ E.M 3 2)
actual = add-bound (ref (ss (ss s0))) (E.Ω 3) (E.cap s0) 2 (B.actual 3) (E.cap-bound {n = 1} {m = 1} s0)
```
