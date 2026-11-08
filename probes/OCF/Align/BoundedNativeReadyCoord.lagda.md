# 相干证书沿真实坐标上下文运输

点态拉回坐标谓词，沿Ctx组合归纳；不识别函数或路径，不从raw LgB推Good。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeReadyCoord where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecLeg using (Ctx; here; viaS; viaL; ek; toC; frC)
open import OCF.Lean.BoundedContextRun using (compose; path-context)
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeReadyGood

Pred : KS → Set₁
Pred S = ∀ κ → E S κ → Set
pull : ∀ {T S} → Pred T → Ctx T S → Pred S
pull Q here κ e = Q κ e
pull Q (viaS c) κ e = pull Q c (inj₁ κ) e
pull Q (viaL c n) κ e = pull Q c (n , κ) e
pull-compose : ∀ {T S R} (Q : Pred T) (a : Ctx T S) (b : Ctx S R) κ e →
  pull Q (compose a b) κ e ≡ pull (pull Q a) b κ e
pull-compose Q a here κ e = refl
pull-compose Q a (viaS b) κ e = pull-compose Q a b (inj₁ κ) e
pull-compose Q a (viaL b n) κ e = pull-compose Q a b (n , κ) e
pull-is : ∀ {T S} (Q : Pred T) (c : Ctx T S) κ e →
  pull Q c κ e ≡ Q (ek c κ) (toC c κ e)
pull-is Q here κ e = refl
pull-is Q (viaS c) κ e = pull-is Q c (inj₁ κ) e
pull-is Q (viaL c n) κ e = pull-is Q c (n , κ) e

tofr : ∀ {T S} (c : Ctx T S) κ e → toC c κ (frC c κ e) ≡ e
tofr here κ e = refl
tofr (viaS c) κ e = tofr c (inj₁ κ) e
tofr (viaL c n) κ e = tofr c (n , κ) e

pull-coord : ∀ {c t : Cd} (p : c ⊲ t) κ e →
  pull (Coord t) (path-context (ls lz) lz p) κ e ≡ Coord c κ e
pull-coord hself κ e = refl
pull-coord {t = hs t} (hsuc p) κ e = trans
  (pull-compose (Coord (hs t)) (viaS here) (path-context (ls lz) lz p) κ e)
  (pull-coord p κ e)
pull-coord {t = hl f} (hlim n p) κ e = trans
  (pull-compose (Coord (hl f)) (viaL here n) (path-context (ls lz) lz p) κ e)
  (pull-coord p κ e)

along-good : ∀ {i t} (p : hs i ⊲ t) e → Coord t (along p) e → Good i (fr-along p e)
along-good {i} {t} p e le = subst (λ X → X)
  (trans (sym (pull-is (Coord t) ctx (inj₂ tt) (fr-along p e)))
    (pull-coord p (inj₂ tt) (fr-along p e)))
  (subst (Coord t (along p)) (sym (tofr ctx (inj₂ tt) e)) le)
  where ctx = path-context (ls lz) lz p

base-good : ∀ t κ e → Coord t (base-kind t κ) e → Coord hz κ (base-fr t κ e)
base-good hz κ e l = l
base-good (hs t) κ e l = base-good t κ e l
base-good (hl f) κ e l = base-good (f 0) κ e l
```

实际classify/decide的保留与回灌坐标都使用同一Good，不借raw合法性代换。

```agda
open import Data.Sum using (_⊎_)
open import OCF.Align.BoundedNativeFoldRun using (Decision; keep; same; above; pick; decide)
open import OCF.Align.BoundedNativeZeroWorld using (seed)

admitted : ∀ c κ {v e} → LgW (Native hz) v →
  Bd (Native c) κ e (seed c v) → Coord c κ e
admitted hz (inj₁ ()) lv b
admitted hz (inj₂ _) lv b = lgB⊲ b (Data.Product.proj₁ lv) (Data.Product.proj₂ lv)
admitted (hs c) (inj₁ κ) lv b = admitted c κ lv b
admitted (hs c) (inj₂ _) lv hself = tt
admitted (hs c) (inj₂ _) lv (hsuc hself) = tt
admitted (hl f) (n , κ) lv b = admitted (f n) κ lv b

Supported : ∀ {B A} → (A → Set) → Class B A → Set
Supported Q (base κ to fr a b) = ∀ e → Coord hz κ e → Q (to e)
Supported Q (rank i p to fr a b) = ∀ e → Good i e → Q (to e)
raise-supported : ∀ {B C A} (Q : A → Set) (p : B ⊲ C) cl → Supported Q cl → Supported Q (raise p cl)
raise-supported Q p (base κ to fr a b) h = h
raise-supported Q p (rank i q to fr a b) h = h
classified : ∀ c κ → Supported (Coord c κ) (classify c κ)
classified hz κ e le = le
classified (hs c) (inj₁ κ) = raise-supported (Coord c κ) (hsuc hself) _ (classified c κ)
classified (hs c) (inj₂ _) e le = le
classified (hl f) (n , κ) = raise-supported (Coord (f n) κ) (hlim n hself) _ (classified (f n) κ)

Allowed : ∀ {B t A} → (A → Set) → Decision B t A → Set
Allowed {t = t} Q (keep κ fr) = ∀ e → Coord t κ e → Q (fr e)
Allowed Q (same to) = ∀ e → Good _ e → Q (to e)
Allowed Q (above i pi ti to) = ∀ e → Good i e → Q (to e)
pick-allowed : ∀ {B t i A} (Q : A → Set) (to : HB (Native i) → A)
  (p : hs i ⊲ B) (q : (t ⊲ hs i) ⊎ (hs i ⊲ t)) →
  (∀ e → Good i e → Q (to e)) → Allowed Q (pick to p q)
pick-allowed Q to p (inj₂ q) h e le = h _ (along-good q e le)
pick-allowed Q to p (inj₁ hself) h e le = h e le
pick-allowed Q to p (inj₁ (hsuc hself)) h = h
pick-allowed Q to p (inj₁ (hsuc q@(hsuc _))) h = h
pick-allowed Q to p (inj₁ (hsuc q@(hlim _ _))) h = h
pick-allowed Q to p (inj₁ (hsuc (hLim {κ = ()} _ _))) h
decision : ∀ {B t A} (Q : A → Set) (pt : t ⊲ B) lB cl → Supported Q cl → Allowed Q (decide pt lB cl)
decision {t = t} Q pt lB (base κ to fr a b) h e le = h _ (base-good t κ e le)
decision Q pt lB (rank i pi to fr a b) h = pick-allowed Q to pi (cmpB pi pt tt lB) h
component : ∀ {B t} c κ (pc : c ⊲ B) (pt : t ⊲ B) lB →
  Allowed (Coord c κ) (decide pt lB (raise pc (classify c κ)))
component c κ pc pt lB = decision (Coord c κ) pt lB _ (raise-supported (Coord c κ) pc _ (classified c κ))
```
