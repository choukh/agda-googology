# 零目标的完整实际decide视图

使用已给seed世界，将每个分量的实际classify/raise/decide分支接到共享
View接口。这里的目标仅Native0，不要求非零目标的不同副本相容。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeViewZero where
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldRun using (pick; decide)
open import OCF.Align.BoundedNativeViewIf
import OCF.Align.BoundedNativeZeroWorld as Z

module At {c : Cd} (κ : K (Native c)) (W : Wd (Native hz)) where
  V = Z.seed c W
  bd = λ e → Bd (Native c) κ e V
  pr = Pr (Native c) κ V

  co : ∀ {i} (to : HB (Native i) → E (Native c) κ) (fr : E (Native c) κ → HB (Native i)) →
    (∀ a → to (fr a) ≡ a) →
    (∀ e → bd (to e) ≡ (e ⊲[ Z.seed i W ] hs hz)) →
    (∀ e d → pr (to e) (to d) ≡ (e ⊲[ Z.seed i W ] d)) →
    bd (to (hs hz)) × (∀ a → bd a → pr a (to (hs hz)))
  co to fr round db dp = subst (λ X → X) (sym (db (hs hz))) hself , λ a b →
    subst (λ x → pr x (to (hs hz))) (round a)
      (subst (λ X → X) (sym (dp (fr a) (hs hz)))
        (subst (λ X → X) (db (fr a)) (subst bd (sym (round a)) b)))

  rank-laws : ∀ {B i} (to : HB (Native i) → E (Native c) κ) fr round inv
    (pi : hs i ⊲ B) (q : (hz ⊲ hs i) ⊎ (hs i ⊲ hz)) →
    Z.Law W bd pr (rank i pi to fr round inv) → Laws.For W V κ (pick to pi q)
  rank-laws to fr round inv pi (inj₂ ()) l
  rank-laws to fr round inv pi (inj₁ (hsuc hself)) (db , dp) = co to fr round db dp
  rank-laws to fr round inv pi (inj₁ (hsuc q@(hsuc _))) (db , dp) = co to fr round db dp
  rank-laws to fr round inv pi (inj₁ (hsuc q@(hlim _ _))) (db , dp) = co to fr round db dp
  rank-laws to fr round inv pi (inj₁ (hsuc (hLim {κ = ()} _ _))) l

  decision-laws : ∀ {B} (pt : hz ⊲ B) lB (cl : Class B (E (Native c) κ)) →
    Z.Law W bd pr cl → Laws.For W V κ (decide pt lB cl)
  decision-laws pt lB (base j to fr round inv) (db , dp) =
    (λ e b → subst (λ X → X) (sym (db e)) b) ,
    (λ e d be bd p → subst (λ X → X) (sym (dp e d)) p) ,
    (λ a b → fr a , round a , subst (λ X → X) (db (fr a)) (subst bd (sym (round a)) b))
  decision-laws pt lB (rank i pi to fr round inv) l =
    rank-laws to fr round inv pi (cmpB pi pt tt lB) l

zero-view : ∀ {B} (lB : LgB B) c (pc : c ⊲ B) (pt : hz ⊲ B) W → View lB c pc hz pt W
zero-view lB c pc pt W = record
  { input-world = Z.seed c W
  ; legal-world = Z.seed-legal c
  ; node-laws = λ κ → At.decision-laws κ W pt lB _ (Z.component c κ W pc) }
```

共享接口现在有全部源分量、全部源kind的真实零目标实例，含co的seed1
可入与上界律。仍不由此推出完整fold.position：above的坐标递归目标i
可以非零，其证书不能由零目标视图自动代替。
