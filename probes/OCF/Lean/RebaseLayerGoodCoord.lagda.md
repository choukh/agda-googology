# 原decide的有证坐标运输

沿实际有界Ctx搬运新Coord及其自证端点；不是对裸下标判等。
旧分类器与运行器均不改，以下结构步骤对照原有限坐标运输逐项证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseLayerGoodCoord where
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecLeg using (Ctx; here; viaS; viaL; ek; frC)
open import OCF.Lean.BoundedContextRun using (compose; path-context)
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldRun
open import OCF.Lean.RebaseLayerGoodIf
open import OCF.Lean.RebaseLayerGoodDomain using (diagonal; left)
open import OCF.Lean.RebaseLayerGoodClosure using (self)
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
  pull (Coord t) (path-context (ls lz) lz p) κ x y ≡ Coord c κ x y
pull-coord hself κ x y = refl
pull-coord {t = hs t} (hsuc p) κ x y = trans
  (pull-compose (Coord (hs t)) (viaS here) (path-context (ls lz) lz p) κ x y)
  (pull-coord p κ x y)
pull-coord {t = hl f} (hlim n p) κ x y = trans
  (pull-compose (Coord (hl f)) (viaL here n) (path-context (ls lz) lz p) κ x y)
  (pull-coord p κ x y)

along-rel : ∀ {i t} (p : hs i ⊲ t) x y → Coord t (along p) x y →
  (Value i (fr-along p x) (fr-along p y) ×
    (Good i (fr-along p x) × Good i (fr-along p y)))
along-rel {i} {t} p x y r = subst (λ X → X)
  (pull-coord p (inj₂ tt) (fr-along p x) (fr-along p y))
  (pull-fr (Coord t) (path-context (ls lz) lz p) (inj₂ tt) x y r)
base-rel : ∀ t κ x y → Coord t (base-kind t κ) x y →
  Coord hz κ (base-fr t κ x) (base-fr t κ y)
base-rel hz κ x y r = r
base-rel (hs t) κ x y r = base-rel t κ x y r
base-rel (hl f) κ x y r = base-rel (f 0) κ x y r

Supported : ∀ {c A} → (A → A → Set) → Class c A → Set
Supported Q (base κ to fr a b) = ∀ x y → Coord hz κ x y → Q (to x) (to y)
Supported Q (rank i p to fr a b) = ∀ x y → (Value i x y × (Good i x × Good i y)) → Q (to x) (to y)
raise-supported : ∀ {c d A} (Q : A → A → Set) (p : c ⊲ d) cl →
  Supported Q cl → Supported Q (raise p cl)
raise-supported Q p (base κ to fr a b) r = r
raise-supported Q p (rank i pi to fr a b) r = r
classified : ∀ c κ → Supported (Coord c κ) (classify c κ)
classified hz κ x y r = r
classified (hs c) (inj₁ κ) =
  raise-supported (Coord c κ) (hsuc hself) (classify c κ) (classified c κ)
classified (hs c) (inj₂ _) x y r = r
classified (hl f) (n , κ) =
  raise-supported (Coord (f n) κ) (hlim n hself) (classify (f n) κ) (classified (f n) κ)

Allowed : ∀ {B t A} → (A → A → Set) → Decision B t A → Set
Allowed {t = t} Q (keep κ fr) = ∀ x y → Coord t κ x y → Q (fr x) (fr y)
Allowed {t = t} Q (same to) = ∀ x y → (Value t x y × (Good t x × Good t y)) → Q (to x) (to y)
Allowed Q (above i pi q to) = ∀ x y → (Value i x y × (Good i x × Good i y)) → Q (to x) (to y)

pick-allowed : ∀ {B t i A} (Q : A → A → Set) to pi s →
  (∀ x y → (Value i x y × (Good i x × Good i y)) → Q (to x) (to y)) →
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

```

新关系的统一右规则还需要单坐标Admit；它可从上述成对运输在同一点
的实例推出，不要求所有raw坐标自证。

```agda
Admitted : ∀ {B t A} → (A → Set) → Decision B t A → Set
Admitted {t = t} P (keep κ fr) = ∀ e → Admit t κ e → P (fr e)
Admitted {t = t} P (same to) = ∀ e → Good t e → P (to e)
Admitted P (above i pi q to) = ∀ e → Good i e → P (to e)

allowed-admit : ∀ {c κ B t} (d : Decision B t (E (Native c) κ)) →
  Allowed (Coord c κ) d → Admitted (Admit c κ) d
allowed-admit {c} {κ} {t = t} (keep κ′ fr) al e se =
  left c κ (al e e (diagonal t κ′ e se))
allowed-admit {c} {κ} (same to) al e se = left c κ (al e e (self _ se , se , se))
allowed-admit {c} {κ} (above i pi q to) al e se = left c κ (al e e (self _ se , se , se))

actual-admit : ∀ {c B t} (lB : LgB B) (pc : c ⊲ B) (pt : t ⊲ B) κ →
  Admitted (Admit c κ) (decide pt lB (raise pc (classify c κ)))
actual-admit {c} lB pc pt κ = allowed-admit _
  (decide-allowed (Coord c κ) pt lB (raise pc (classify c κ))
    (raise-supported (Coord c κ) pc (classify c κ) (classified c κ)))
```

实际非零层可取c=hs hz、B=c、pc=hself、pt=hsuc hself；classify的
所有种类都由actual-admit覆盖。该定理只完成坐标准入搬运，不声称
折叠已经保持SampleValue或输入自证可逐枝反演。
