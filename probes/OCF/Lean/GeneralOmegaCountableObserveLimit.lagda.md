# 原观察器沿指定ℕ分量注入的相容性

本篇固定并层中的同一分量编号n：source从f n升到hl f，目标t的
路径只增加hlim n。没有把不同分量、不同路径或同值高度混同。
这是原累计地板分量捕获所需的一个结构步骤，尚不声称观察器保
右加项，亦不由此声称Γ沿所有第一位置单调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableObserveLimit where
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (<-cmp; <-irrefl; ≡-irrelevant)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableRelIf
open import OCF.Lean.GeneralOmegaCountableRelClass
open import OCF.Lean.GeneralOmegaCountableRelRun

record LimitSimulation : Set₁ where
  field
    full-limit : ∀ f lB n t pt {a b} → Rel (f n) a b →
      Rel t (observe (f n) (proj₂ lB n) t pt a)
        (observe (hl f) lB t (hlim n pt) (ι n b))

-- 只有自然数编号的判等证明被规范化，不要求Cd路径证明无关。
cmp-component : ∀ f (lB : LgB (hl f)) n {a b}
  (p : a ⊲ f n) (q : b ⊲ f n) →
  cmpB (hlim n p) (hlim n q) tt lB ≡ cmpB p q tt (proj₂ lB n)
cmp-component f (st , l) n p q with <-cmp n n
... | tri< lt _ _ = ⊥-elim (<-irrefl refl lt)
... | tri> _ _ gt = ⊥-elim (<-irrefl refl gt)
... | tri≈ _ eq _ rewrite ≡-irrelevant eq refl = refl

lift-decision : ∀ {B D t A} → (∀ {a} → a ⊲ B → a ⊲ D) →
  C.Dc F B t A → C.Dc F D t A
lift-decision raise (C.keep κ fr) = C.keep κ fr
lift-decision raise (C.same to) = C.same to
lift-decision raise (C.above i pi ti to) = C.above i (raise pi) ti to

lift-pick : ∀ {B D t i A} (raise : ∀ {a} → a ⊲ B → a ⊲ D)
  (to : HB (F i) → A) (pi : hs i ⊲ B)
  (r : (t ⊲ hs i) ⊎ (hs i ⊲ t)) →
  lift-decision raise (C.pick S⊥ to pi r) ≡ C.pick S⊥ to (raise pi) r
lift-pick raise to pi (inj₂ p) = refl
lift-pick raise to pi (inj₁ hself) = refl
lift-pick raise to pi (inj₁ (hsuc hself)) = refl
lift-pick raise to pi (inj₁ (hsuc (hsuc p))) = refl
lift-pick raise to pi (inj₁ (hsuc (hlim m p))) = refl
lift-pick raise to pi (inj₁ (hsuc (hLim {κ = ()} b p)))

classify-lift : ∀ f (lB : LgB (hl f)) n t (pt : t ⊲ f n) {κ}
  (v : C.Cl {S⊥} (f n) κ) →
  C.dcl (hlim n pt) lB (C.cL n v) ≡ lift-decision (hlim n) (C.dcl pt (proj₂ lB n) v)
classify-lift f lB n t pt (C.bas () to)
classify-lift f lB n t pt (C.nw i pi to) = trans
  (cong (C.pick S⊥ to (hlim n pi)) (cmp-component f lB n pi pt))
  (sym (lift-pick (hlim n) to pi (cmpB pi pt tt (proj₂ lB n))))

classify-limit : ∀ f (lB : LgB (hl f)) n t (pt : t ⊲ f n) κ →
  classify (hl f) lB t (hlim n pt) (n , κ) ≡
    lift-decision (hlim n) (classify (f n) (proj₂ lB n) t pt κ)
classify-limit f lB n t pt κ = classify-lift f lB n t pt (C.cl (f n) κ)

node-limit : ∀ {f t A} (Q : A → A → Set) n (pt : t ⊲ f n)
  (v : C.Dc F (f n) t A) → Good Q v →
  (rec : ∀ r → r ⊲ f n → A → HB (F r)) →
  (rec′ : ∀ r → r ⊲ hl f → A → HB (F r)) →
  (∀ r pr {a b} → Q a b → Rel r (rec r pr a) (rec′ r (hlim n pr) b)) →
  Rel t (node pt v rec) (node (hlim n pt) (lift-decision (hlim n) v) rec′)
node-limit Q n pt (C.keep κ fr) good rec rec′ rel = ro (λ r → rel _ pt (good r))
node-limit {t = t} Q n pt (C.same to) good rec rec′ rel = rl (λ k → rel t pt
  (good (iterate-rel (λ r → rel t pt (good r)) (floor-related t) k)))
node-limit {t = t} Q n pt (C.above i pi ti to) good rec rec′ rel = rl (λ k → rel t pt
  (good (iterate-rel (λ r → rel i (⊲ᴮ-tr (hsuc hself) pi) (good r)) (floor-related i) k)))

limit-observe : ∀ f lB n t pt {a b} → Rel (f n) a b →
  Rel t (observe (f n) (proj₂ lB n) t pt a)
    (observe (hl f) lB t (hlim n pt) (ι n b))
limit-observe f lB n t pt rz = floor-related t
limit-observe f lB n t pt (rs p) = rl (left-rel (limit-observe f lB n t pt p))
limit-observe f lB n t pt (rl p) = rl (λ k → limit-observe f lB n t pt (p k))
limit-observe f lB n t pt (ro {κ} {f = a} {g = b} p) = subst
  (λ v → Rel t (node pt (classify (f n) (proj₂ lB n) t pt κ)
    (λ r pr e → observe (f n) (proj₂ lB n) r pr (a e)))
    (node (hlim n pt) v (λ r pr e → observe (hl f) lB r pr (ι n (b e)))))
  (sym (classify-limit f lB n t pt κ))
  (node-limit (Coord (f n) κ) n pt (classify (f n) (proj₂ lB n) t pt κ)
    (class-good (f n) (proj₂ lB n) t pt κ)
    (λ r pr e → observe (f n) (proj₂ lB n) r pr (a e))
    (λ r pr e → observe (hl f) lB r pr (ι n (b e)))
    (λ r pr cd → limit-observe f lB n r pr (p cd)))

instance-limit : LimitSimulation
instance-limit = record { full-limit = limit-observe }
```

floor-related为任意分量提供实际非空输入，反馈沿原source子树递归。
本篇只给指定ι和指定hlim路径的完整输出关系；它不提供累计和中
右分量的观察下界，也不改变原Γ及其地板或完成操作。
