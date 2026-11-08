# 同一底世界的所有原生目标视图

目标限定为 seed t v：所有底副本共用 v，高rank界均为真实种子1。
这避开任意世界副本不相干的反例，但保留原 classify/decide，不更改运行器。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeReadySeedView where
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecLeg using (pw; bdTo; bdFr; prFr)
open import OCF.Lean.BoundedContextRun using (path-context)
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldRun using (Decision; pick; decide)
open import OCF.Align.BoundedNativeViewIf
import OCF.Align.BoundedNativeZeroWorld as Z
import OCF.Align.BoundedNativeViewZero as V0

base-bd : ∀ t v κ e → Bd (Native t) (base-kind t κ) e (Z.seed t v) ≡
  Bd (Native hz) κ (base-fr t κ e) v
base-bd hz v κ e = refl
base-bd (hs t) v κ e = base-bd t v κ e
base-bd (hl f) v κ e = base-bd (f 0) v κ e
base-pr : ∀ t v κ e d → Pr (Native t) (base-kind t κ) (Z.seed t v) e d ≡
  Pr (Native hz) κ v (base-fr t κ e) (base-fr t κ d)
base-pr hz v κ e d = refl
base-pr (hs t) v κ e d = base-pr t v κ e d
base-pr (hl f) v κ e d = base-pr (f 0) v κ e d
base-legal : ∀ t {v} → LgW (Native t) (Z.seed t v) → LgW (Native hz) v
base-legal hz l = l
base-legal (hs t) l = base-legal t (proj₁ l)
base-legal (hl f) l = base-legal (f 0) (l 0)
```

```agda
open import OCF.Align.BoundedNativeSeedProjection using (rank-project)

along-bd-fr : ∀ {i t} (p : hs i ⊲ t) v e →
  Bd (Native t) (along p) e (Z.seed t v) → fr-along p e ⊲[ Z.seed i v ] hs hz
along-bd-fr {i} p v e b = subst
  (λ W → Bd (Native (hs i)) (inj₂ tt) (fr-along p e) W)
  (rank-project p v) (bdFr (path-context (ls lz) lz p) (inj₂ tt) b)
along-pr-fr : ∀ {i t} (p : hs i ⊲ t) v e d →
  Pr (Native t) (along p) (Z.seed t v) e d →
  fr-along p e ⊲[ Z.seed i v ] fr-along p d
along-pr-fr {i} p v e d r = subst
  (λ W → Pr (Native (hs i)) (inj₂ tt) W (fr-along p e) (fr-along p d))
  (rank-project p v) (prFr (path-context (ls lz) lz p) (inj₂ tt) r)
along-bd-to : ∀ {i t} (p : hs i ⊲ t) v e → e ⊲[ Z.seed i v ] hs hz →
  Bd (Native t) (along p) (to-along p e) (Z.seed t v)
along-bd-to {i} p v e b = bdTo (path-context (ls lz) lz p) (inj₂ tt)
  (subst (λ W → Bd (Native (hs i)) (inj₂ tt) e W) (sym (rank-project p v)) b)

module At {c t : Cd} (κ : K (Native c)) (v : Wd (Native hz)) where
  bd = λ e → Bd (Native c) κ e (Z.seed c v)
  pr = Pr (Native c) κ (Z.seed c v)
  Result : ∀ {B} → Decision B t (E (Native c) κ) → Set
  Result {B} = Laws.For {B = B} (Z.seed t v) (Z.seed c v) κ

  rank-laws : ∀ {B i} (to : HB (Native i) → E (Native c) κ) fr round inv
    (pi : hs i ⊲ B) (q : (t ⊲ hs i) ⊎ (hs i ⊲ t)) →
    Z.Law v bd pr (rank i pi to fr round inv) → Result (pick to pi q)
  rank-laws to fr round inv pi (inj₂ q) (db , dp) =
    (λ e b → subst (λ X → X) (sym (db (fr-along q e))) (along-bd-fr q v e b)) ,
    (λ e d be bd p → subst (λ X → X) (sym (dp (fr-along q e) (fr-along q d))) (along-pr-fr q v e d p)) ,
    (λ a b → to-along q (fr a) , trans (cong to (along-roundtrip q (fr a))) (round a) ,
      along-bd-to q v (fr a) (subst (λ X → X) (db (fr a)) (subst bd (sym (round a)) b)))
  rank-laws to fr round inv pi (inj₁ hself) (db , dp) =
    (λ e b → subst (λ X → X) (sym (db e)) b) ,
    (λ e d be bd p → subst (λ X → X) (sym (dp e d)) p) ,
    (λ a b → fr a , round a , subst (λ X → X) (db (fr a)) (subst bd (sym (round a)) b))
  rank-laws to fr round inv pi (inj₁ (hsuc hself)) (db , dp) = V0.At.co κ v to fr round db dp
  rank-laws to fr round inv pi (inj₁ (hsuc q@(hsuc _))) (db , dp) = V0.At.co κ v to fr round db dp
  rank-laws to fr round inv pi (inj₁ (hsuc q@(hlim _ _))) (db , dp) = V0.At.co κ v to fr round db dp
  rank-laws to fr round inv pi (inj₁ (hsuc (hLim {κ = ()} _ _))) l

  decision-laws : ∀ {B} (pt : t ⊲ B) lB (cl : Class B (E (Native c) κ)) →
    Z.Law v bd pr cl → Result (decide pt lB cl)
  decision-laws pt lB (base j to fr round inv) (db , dp) =
    (λ e b → subst (λ X → X) (sym (db (base-fr t j e))) (subst (λ X → X) (base-bd t v j e) b)) ,
    (λ e d be bd p → subst (λ X → X) (sym (dp (base-fr t j e) (base-fr t j d)))
      (subst (λ X → X) (base-pr t v j e d) p)) ,
    (λ a b → base-to t j (fr a) , trans (cong to (base-frto t j (fr a))) (round a) ,
      subst (λ X → X) (sym (base-bd t v j (base-to t j (fr a))))
        (subst (λ e → Bd (Native hz) j e v) (sym (base-frto t j (fr a)))
          (subst (λ X → X) (db (fr a)) (subst bd (sym (round a)) b))))
  decision-laws pt lB (rank i pi to fr round inv) l =
    rank-laws to fr round inv pi (cmpB pi pt tt lB) l

seed-view : ∀ {B} (lB : LgB B) c (pc : c ⊲ B) t (pt : t ⊲ B) v →
  View lB c pc t pt (Z.seed t v)
seed-view lB c pc t pt v = record
  { input-world = Z.seed c v
  ; legal-world = λ l → Z.seed-legal c (base-legal t l)
  ; node-laws = λ κ → At.decision-laws κ v pt lB _ (Z.component c κ v pc) }
```

seed-view 已对实际全部可数源层与目标层给出实例，包含原 above 递归可能
访问的非零目标；前提可由 Z.seed-legal 从任意合法底世界构造。
这仍只提供相干世界域内的视图，不宣称 raw LgB preservation。
