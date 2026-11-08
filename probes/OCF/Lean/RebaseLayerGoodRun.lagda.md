# 原有限at的Good采样保持与有向比较

本篇使用原decide与原diagonal。采样链的Good由输入递归字段给出，
没有从顶层值自证反演子树；比较律保留各自字面公共界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseLayerGoodRun where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.RebaseLayerIf using (vz; vs; vr; vl; vli; vo; vor)
open import OCF.Lean.RebaseLayerGoodIf
open import OCF.Lean.RebaseLayerGoodClosure
open import OCF.Lean.RebaseLayerGoodDomain
open import OCF.Lean.RebaseLayerClosure using (add)
open import OCF.Lean.RebaseLayerGoodCoord
open import OCF.Lean.BoundedFoldRun using (chain; diagonal)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldRun using (decide; keep; same; above)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteBridgeDecision
open import OCF.Align.BoundedCompletionUniformCoord using (decide-finite)
open import OCF.Align.BoundedCompletionFiniteRunIf using (at)
import OCF.Lean.BoundedDiagonalRel as D

one : ∀ c → Good c (hs hz)
one c = vs vz , vz
chain-good : ∀ c f → (∀ e → Good c e → Good c (f e)) → ∀ n → Good c (chain f n)
chain-good c f k zero = one c
chain-good c f k (suc n) = good-add c (chain-good c f k n) (k _ (chain-good c f k n))
partial-good : ∀ c f → (∀ n → Good c (f n)) → ∀ n → Good c (Ops.partial (Native c) f n)
partial-good c f k zero = k zero
partial-good c f k (suc n) = good-add c (partial-good c f k n) (k (suc n))
repeat-value : ∀ c {a b} → Value c a b → Value c (Ops.repeat (Native c) a) (Ops.repeat (Native c) b)
repeat-value c p = vl (λ n → vli n (parts n))
  where
  parts : ∀ n → Value c (Ops.partial (Native c) (λ _ → _) n) (Ops.partial (Native c) (λ _ → _) n)
  parts zero = p
  parts (suc n) = add (parts n) p

positive : ∀ n m {B} (lB : LgB B) (pc : num n ⊲ B) (pt : num m ⊲ B)
  a → Value (num m) (hs hz) (at n m lB pc pt a)
positive n m lB pc pt hz = vs vz
positive n m lB pc pt (hs a) = vli 0 (positive n m lB pc pt a)
positive n m lB pc pt (hl f) = vli 0 (positive n m lB pc pt (f 0))
positive n m lB pc pt (hΩ κ g) with decide pt lB (raise pc (classify (num n) κ))
... | keep κ′ fr = vor (λ e se → positive n m lB pc pt (g (fr e)))
... | same to = vli 0 (positive n m lB pc pt (g (to (hs hz))))
... | above i pi q to = vli 0 (positive n m lB pc pt (g (to (hs hz))))

module Sim (c d : Cd) (f f′ : HB (Native c) → HB (Native c))
  (g g′ : HB (Native c) → HB (Native d))
  (kf : ∀ e → Good c e → Good c (f e)) (kf′ : ∀ e → Good c e → Good c (f′ e))
  (step : ∀ {x y} → Good c x → Good c y → Value c x y → Value c (f x) (f′ y))
  (emit : ∀ {x y} → Good c x → Good c y → Value c x y → Value d (g x) (g′ y)) where
  module Run = D.Sim (λ x y → Value c x y Data.Product.× (Good c x Data.Product.× Good c y)) (Value d)
    f f′ g g′ (vs vz , one c , one c)
    (λ p q → add (proj₁ p) (proj₁ q) , good-add c (proj₁ (proj₂ p)) (proj₁ (proj₂ q)) ,
      good-add c (proj₂ (proj₂ p)) (proj₂ (proj₂ q)))
    add (λ p → vl (λ n → vli n (p n)))
    (λ p → step (proj₁ (proj₂ p)) (proj₂ (proj₂ p)) (proj₁ p) ,
      kf _ (proj₁ (proj₂ p)) , kf′ _ (proj₂ (proj₂ p)))
    (λ p → emit (proj₁ (proj₂ p)) (proj₂ (proj₂ p)) (proj₁ p))
  result = Run.result

mutual
  preserve : ∀ n m {B} (lB : LgB B) (pc : num n ⊲ B) (pt : num m ⊲ B)
    a → Good (num n) a → Good (num m) (at n m lB pc pt a)
  compare : ∀ n m {B B′} (lB : LgB B) (lB′ : LgB B′)
    (pc : num n ⊲ B) (pc′ : num n ⊲ B′) (pt : num m ⊲ B) (pt′ : num m ⊲ B′)
    {a b} → Good (num n) a → Good (num n) b → Value (num n) a b →
    Value (num m) (at n m lB pc pt a) (at n m lB′ pc′ pt′ b)

  preserve n m lB pc pt hz ga = one (num m)
  preserve n m lB pc pt (hs a) ga =
    compare n m lB lB pc pc pt pt {a = hs a} {b = hs a} ga ga (self (num n) {a = hs a} ga) ,
    partial-good (num m) _ (λ _ → preserve n m lB pc pt a (proj₂ ga))
  preserve n m lB pc pt (hl f) ga =
    compare n m lB lB pc pc pt pt {a = hl f} {b = hl f} ga ga (self (num n) {a = hl f} ga) ,
    (λ j → preserve n m lB pc pt (f j) (proj₂ ga j))
  preserve n m lB pc pt (hΩ κ g) ga
    with decide pt lB (raise pc (classify (num n) κ))
       | actual-admit lB pc pt κ
       | decide-finite pt lB (raise pc (classify (num n) κ))
           (finite-raise pc (classify (num n) κ) (finite-classify n κ))
       | compare n m lB lB pc pc pt pt {a = hΩ κ g} {b = hΩ κ g} ga ga (self (num n) {a = hΩ κ g} ga)
  ... | keep κ′ fr | ad | fin | vv = vv , (λ e se → preserve n m lB pc pt (g (fr e)) (proj₂ ga (fr e) (ad e se)))
  ... | same to | ad | fin | vv = vv , partial-good (num m) _ (λ j → k _ (chain-good (num m) _ k j))
    where
    k : ∀ e → Good (num m) e → Good (num m) (at n m lB pc pt (g (to e)))
    k e se = preserve n m lB pc pt (g (to e)) (proj₂ ga (to e) (ad e se))
  ... | above i pi q to | ad | j , refl | vv = vv , partial-good (num m) _
    (λ k → preserve n m lB pc pt (g (to (chain _ k)))
      (proj₂ ga _ (ad _ (chain-good (num j) _ keep-good k))))
    where
    keep-good : ∀ e → Good (num j) e → Good (num j)
      (at n j lB pc (⊲ᴮ-tr (hsuc hself) pi) (g (to e)))
    keep-good e se = preserve n j lB pc (⊲ᴮ-tr (hsuc hself) pi) (g (to e)) (proj₂ ga (to e) (ad e se))

  compare n m lB lB′ pc pc′ pt pt′ {b = b} ga gb vz = positive n m lB′ pc′ pt′ b
  compare n m lB lB′ pc pc′ pt pt′ ga gb (vs p) = repeat-value (num m)
    (compare n m lB lB′ pc pc′ pt pt′ (proj₂ ga) (proj₂ gb) p)
  compare n m lB lB′ pc pc′ pt pt′ ga gb (vr p) = vli 0 (compare n m lB lB′ pc pc′ pt pt′ ga (proj₂ gb) p)
  compare n m lB lB′ pc pc′ pt pt′ ga gb (vl p) = vl (λ j → compare n m lB lB′ pc pc′ pt pt′ (proj₂ ga j) gb (p j))
  compare n m lB lB′ pc pc′ pt pt′ ga gb (vli j p) = vli j (compare n m lB lB′ pc pc′ pt pt′ ga (proj₂ gb j) p)
  compare n m lB lB′ pc pc′ pt pt′ ga gb (vo {κ = κ} {f} {g} p)
    with decide pt lB (raise pc (classify (num n) κ))
       | decide pt′ lB′ (raise pc′ (classify (num n) κ))
       | actual-component n m κ lB lB′ pc pc′ pt pt′
       | decide-allowed (Coord (num n) κ) pt lB (raise pc (classify (num n) κ))
           (raise-supported (Coord (num n) κ) pc (classify (num n) κ) (classified (num n) κ))
       | decide-finite pt lB (raise pc (classify (num n) κ))
           (finite-raise pc (classify (num n) κ) (finite-classify n κ))
  ... | keep κ′ fr | .(keep κ′ fr) | kept .κ′ .fr | al | fin = vo (λ x y xy →
    compare n m lB lB′ pc pc′ pt pt′
      (proj₂ ga _ (left (num n) κ (al x y xy))) (proj₂ gb _ (right (num n) κ (al x y xy)))
      (p _ _ (al x y xy)))
  ... | same to | .(same to) | same-rank .to | al | fin = Sim.result (num m) (num m) _ _ _ _
    (λ e se → preserve n m lB pc pt (f (to e)) (proj₂ ga _ (left (num n) κ (al e e (self (num m) se , se , se)))))
    (λ e se → preserve n m lB′ pc′ pt′ (g (to e)) (proj₂ gb _ (right (num n) κ (al e e (self (num m) se , se , se)))))
    (λ {x} {y} sx sy xy → compare n m lB lB′ pc pc′ pt pt′
      (proj₂ ga _ (left (num n) κ (al x y (xy , sx , sy))))
      (proj₂ gb _ (right (num n) κ (al x y (xy , sx , sy)))) (p _ _ (al x y (xy , sx , sy))))
    (λ {x} {y} sx sy xy → compare n m lB lB′ pc pc′ pt pt′
      (proj₂ ga _ (left (num n) κ (al x y (xy , sx , sy))))
      (proj₂ gb _ (right (num n) κ (al x y (xy , sx , sy)))) (p _ _ (al x y (xy , sx , sy))))
  ... | above i pi q to | .(above i _ q to) | higher .i .pi pi′ .q .to | al | j , refl = Sim.result (num j) (num m) _ _ _ _
    (λ e se → preserve n j lB pc (⊲ᴮ-tr (hsuc hself) pi) (f (to e)) (proj₂ ga _ (left (num n) κ (al e e (self (num j) se , se , se)))))
    (λ e se → preserve n j lB′ pc′ (⊲ᴮ-tr (hsuc hself) pi′) (g (to e)) (proj₂ gb _ (right (num n) κ (al e e (self (num j) se , se , se)))))
    (λ {x} {y} sx sy xy → compare n j lB lB′ pc pc′ (⊲ᴮ-tr (hsuc hself) pi) (⊲ᴮ-tr (hsuc hself) pi′)
      (proj₂ ga _ (left (num n) κ (al x y (xy , sx , sy))))
      (proj₂ gb _ (right (num n) κ (al x y (xy , sx , sy)))) (p _ _ (al x y (xy , sx , sy))))
    (λ {x} {y} sx sy xy → compare n m lB lB′ pc pc′ pt pt′
      (proj₂ ga _ (left (num n) κ (al x y (xy , sx , sy))))
      (proj₂ gb _ (right (num n) κ (al x y (xy , sx , sy)))) (p _ _ (al x y (xy , sx , sy))))
  compare n m lB lB′ pc pc′ pt pt′ ga gb (vor {κ = κ} {g} p)
    with decide pt′ lB′ (raise pc′ (classify (num n) κ)) | actual-admit lB′ pc′ pt′ κ
  ... | keep κ′ fr | ad = vor (λ e se → compare n m lB lB′ pc pc′ pt pt′ ga
    (proj₂ gb _ (ad e se)) (p (fr e) (ad e se)))
  ... | same to | ad = vli 0 (compare n m lB lB′ pc pc′ pt pt′ ga
    (proj₂ gb _ (ad _ (one (num m)))) (p (to (hs hz)) (ad _ (one (num m)))))
  ... | above i pi q to | ad = vli 0 (compare n m lB lB′ pc pc′ pt pt′ ga
    (proj₂ gb _ (ad _ (one i))) (p (to (hs hz)) (ad _ (one i))))
```
