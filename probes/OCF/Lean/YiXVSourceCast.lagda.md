# YiXVSourceCast
> 验收文件。档位：编译定理。原 fg 的有限坐标及有限层证书、折叠换型；零层号上的等式唯一性。
> 接 YiXVSourceSem、SourceAffine*、Finite*，有限搬运比较参照 YiXVCan2Embed；未交完整外层链或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceCast where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as P
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceSelfInput as Default
import OCF.Lean.YiXVStart as Start

num : ℕ → S.Tr S.zero
num = O.iter S.suc S.zero
plus-one : ∀ n → S.suc S.zero O.+ num n ≡ num (suc n)
plus-one zero = refl
plus-one (suc n) = cong S.suc (plus-one n)
iter-one : ∀ n → O.iter (S.suc S.zero O.+_) (S.suc S.zero) n ≡ num (suc n)
iter-one zero = refl
iter-one (suc n) = trans (cong (S.suc S.zero O.+_) (iter-one n)) (plus-one (suc n))
read-num : ∀ n → S.↑ S.zero (num n) ≡ J.nat n
read-num zero = refl
read-num (suc n) = cong S.suc (read-num n)
zero-plus : ∀ n → S.zero S.⊕ J.nat n ≡ J.nat n
zero-plus zero = refl
zero-plus (suc n) = cong S.suc (zero-plus n)
fg : ∀ n → Start.fg n ≡ J.nat (suc n)
fg n = trans (cong (λ x → S.zero S.⊕ S.↑ S.zero x) (iter-one n))
  (trans (cong (S.zero S.⊕_) (read-num (suc n))) (zero-plus (suc n)))
ev : ∀ n (e : P.Ev (J.nat n)) → e ≡ Default.ev n
ev zero tt = refl
ev (suc n) e = ev n e
rt : ∀ n (r : P.Rt (J.nat n)) → r ≡ Default.rt n
rt zero tt = refl
rt (suc n) r = rt n r

cast⊥ : ∀ n {a} (e : a ≡ J.nat n) ε ρ (B : Fold.Base a) (x : S.Tr a) →
  Fold.ψ⊥ a ε ρ B x ≡ Fold.ψ⊥ (J.nat n) (Default.ev n) (Default.rt n) (subst Fold.Base e B) (subst S.Tr e x)
cast⊥ n refl ε ρ B x rewrite ev n ε | rt n ρ = refl
castS : ∀ n {a} (e : a ≡ J.nat n) ε ρ (B : Fold.Base a) {j} (w : j P.≤ a) β nβ (x : S.Tr a) →
  Fold.ψs a ε ρ B j w β nβ x ≡ Fold.ψs (J.nat n) (Default.ev n) (Default.rt n)
    (subst Fold.Base e B) j (subst (j P.≤_) e w) β nβ (subst S.Tr e x)
castS n refl ε ρ B w β nβ x rewrite ev n ε | rt n ρ = refl

zero-unique : (p : _≡_ {A = S.L} S.zero S.zero) → p ≡ refl
zero-unique refl = refl
```
