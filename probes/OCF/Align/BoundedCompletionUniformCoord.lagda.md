# 原有限决定的有向坐标运输

沿实际Ctx拉回两坐标的结构关系。这里不比较两个裸下标；每个层搬运
都有明确c⊲t，实际决定仍在同一合法B内。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionUniformCoord where
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecLeg using (Ctx; here; viaS; viaL; ek; frC)
open import OCF.Lean.BoundedContextRun using (compose; path-context)
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldRun
open import OCF.Align.BoundedCompletionUniformIf
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteBridgeDecision using (FiniteClass; finite-classify; finite-raise)

Pred : KS → Set₁
Pred S = ∀ κ → E S κ → E S κ → Set
pull : ∀ {T S} → Pred T → Ctx T S → Pred S
pull Q here κ x y = Q κ x y
pull Q (viaS c) κ x y = pull Q c (inj₁ κ) x y
pull Q (viaL c n) κ x y = pull Q c (n , κ) x y
pull-compose : ∀ {T S R} (Q : Pred T) (a : Ctx T S) (b : Ctx S R) κ x y →
  pull Q (compose a b) κ x y ≡ pull (pull Q a) b κ x y
pull-compose Q a here κ x y = refl
pull-compose Q a (viaS b) κ x y = pull-compose Q a b (inj₁ κ) x y
pull-compose Q a (viaL b n) κ x y = pull-compose Q a b (n , κ) x y
pull-fr : ∀ {T S} (Q : Pred T) (c : Ctx T S) κ x y →
  Q (ek c κ) x y → pull Q c κ (frC c κ x) (frC c κ y)
pull-fr Q here κ x y r = r
pull-fr Q (viaS c) κ x y r = pull-fr Q c (inj₁ κ) x y r
pull-fr Q (viaL c n) κ x y r = pull-fr Q c (n , κ) x y r

pull-coord : ∀ {c t : Cd} (p : c ⊲ t) κ x y →
  pull (CoordValue t) (path-context (ls lz) lz p) κ x y ≡ CoordValue c κ x y
pull-coord hself κ x y = refl
pull-coord {t = hs t} (hsuc p) κ x y = trans
  (pull-compose (CoordValue (hs t)) (viaS here) (path-context (ls lz) lz p) κ x y)
  (pull-coord p κ x y)
pull-coord {t = hl f} (hlim n p) κ x y = trans
  (pull-compose (CoordValue (hl f)) (viaL here n) (path-context (ls lz) lz p) κ x y)
  (pull-coord p κ x y)

along-rel : ∀ {i t} (p : hs i ⊲ t) x y → CoordValue t (along p) x y →
  Value i (fr-along p x) (fr-along p y)
along-rel {i} {t} p x y r = subst (λ X → X)
  (pull-coord p (inj₂ tt) (fr-along p x) (fr-along p y))
  (pull-fr (CoordValue t) (path-context (ls lz) lz p) (inj₂ tt) x y r)
base-rel : ∀ t κ x y → CoordValue t (base-kind t κ) x y →
  CoordValue hz κ (base-fr t κ x) (base-fr t κ y)
base-rel hz κ x y r = r
base-rel (hs t) κ x y r = base-rel t κ x y r
base-rel (hl f) κ x y r = base-rel (f 0) κ x y r

Supported : ∀ {c A} → (A → A → Set) → Class c A → Set
Supported Q (base κ to fr a b) = ∀ x y → CoordValue hz κ x y → Q (to x) (to y)
Supported Q (rank i p to fr a b) = ∀ x y → Value i x y → Q (to x) (to y)
raise-supported : ∀ {c d A} (Q : A → A → Set) (p : c ⊲ d) cl →
  Supported Q cl → Supported Q (raise p cl)
raise-supported Q p (base κ to fr a b) r = r
raise-supported Q p (rank i pi to fr a b) r = r
classified : ∀ c κ → Supported (CoordValue c κ) (classify c κ)
classified hz κ x y r = r
classified (hs c) (inj₁ κ) =
  raise-supported (CoordValue c κ) (hsuc hself) (classify c κ) (classified c κ)
classified (hs c) (inj₂ _) x y r = r
classified (hl f) (n , κ) =
  raise-supported (CoordValue (f n) κ) (hlim n hself) (classify (f n) κ) (classified (f n) κ)

Allowed : ∀ {B t A} → (A → A → Set) → Decision B t A → Set
Allowed {t = t} Q (keep κ fr) = ∀ x y → CoordValue t κ x y → Q (fr x) (fr y)
Allowed {t = t} Q (same to) = ∀ x y → Value t x y → Q (to x) (to y)
Allowed Q (above i pi q to) = ∀ x y → Value i x y → Q (to x) (to y)

pick-allowed : ∀ {B t i A} (Q : A → A → Set) to pi s →
  (∀ x y → Value i x y → Q (to x) (to y)) →
  Allowed {B} {t} Q (pick {i = i} to pi s)
pick-allowed Q to pi (inj₂ q) r x y xy = r _ _ (along-rel q x y xy)
pick-allowed Q to pi (inj₁ hself) r = r
pick-allowed Q to pi (inj₁ (hsuc hself)) r = r
pick-allowed Q to pi (inj₁ (hsuc q@(hsuc _))) r = r
pick-allowed Q to pi (inj₁ (hsuc q@(hlim _ _))) r = r
pick-allowed Q to pi (inj₁ (hsuc (hLim {κ = ()} _ _))) r

decide-allowed : ∀ {B t A} (Q : A → A → Set) pt lB cl → Supported Q cl →
  Allowed {B} {t} Q (decide pt lB cl)
decide-allowed {t = t} Q pt lB (base κ to fr a b) r x y xy = r _ _ (base-rel t κ x y xy)
decide-allowed Q pt lB (rank i pi to fr a b) r =
  pick-allowed Q to pi (cmpB pi pt tt lB) r

FiniteDecision : ∀ {B t A} → Decision B t A → Set
FiniteDecision (keep κ fr) = ⊤
FiniteDecision (same to) = ⊤
FiniteDecision (above i pi q to) = Σ ℕ (λ n → i ≡ num n)
pick-finite : ∀ {B t i A} (to : HB (Native i) → A) pi s →
  Σ ℕ (λ n → i ≡ num n) → FiniteDecision (pick {B} {t} to pi s)
pick-finite to pi (inj₂ q) r = tt
pick-finite to pi (inj₁ hself) r = tt
pick-finite to pi (inj₁ (hsuc hself)) r = tt
pick-finite to pi (inj₁ (hsuc q@(hsuc _))) r = r
pick-finite to pi (inj₁ (hsuc q@(hlim _ _))) r = r
pick-finite to pi (inj₁ (hsuc (hLim {κ = ()} _ _))) r

decide-finite : ∀ {B t A} pt lB (cl : Class B A) → FiniteClass cl →
  FiniteDecision (decide {t = t} pt lB cl)
decide-finite pt lB (base κ to fr a b) r = tt
decide-finite pt lB (rank i pi to fr a b) r = pick-finite to pi (cmpB pi pt tt lB) r
```
