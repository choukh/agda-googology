# 实际局部塔的种类分类

指标分量通过 first-index 回到前缀；后继新种类记录其字面高度。
仅在同一合法 B 下比较目标 t 与种类高度。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedFoldClass where
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf
open import OCF.Lean.BoundedContextRun using (path-context)
open import OCF.Lean.BoundedIndexContext using (first-index)
open import OCF.Lean.LHRecLeg using (ek; frC)

module _ (β : HB S⊥) where
  data Class (B : HB U) (A : Set) : Set where
    base : (κ : K (T hz)) → (E (T hz) κ → A) → Class B A
    rank : (i : HB U) → hs i ⊲[ (tt , β) ] B → (HB (T i) → A) → Class B A

  liftS : ∀ {B A} → Class B A → Class (hs B) A
  liftS (base κ f) = base κ f
  liftS (rank i p f) = rank i (hsuc p) f
  liftL : ∀ {f A} n → Class (f n) A → Class (hl f) A
  liftL n (base κ f) = base κ f
  liftL n (rank i p f) = rank i (hlim n p) f
  liftO : ∀ {f A e} → e ⊲[ tt ] β → Class (f e) A → Class (hΩ (inj₂ tt) f) A
  liftO b (base κ f) = base κ f
  liftO b (rank i p f) = rank i (hLim b p) f

  classify : ∀ B κ → Pos β B κ → Class B (E (T B) κ)
  classify hz κ p = base κ (λ c → c)
  classify (hs B) (inj₁ κ) p = liftS (classify B κ p)
  classify (hs B) (inj₂ _) p = rank B hself (λ c → c)
  classify (hl f) (n , κ) p = liftL n (classify (f n) κ p)
  classify (hΩ (inj₁ ()) f) κ p
  classify (hΩ (inj₂ _) f) (inj₁ _ , κ) p = base (ek first-index κ) (frC first-index κ)
  classify (hΩ (inj₂ _) f) (inj₂ e , κ) (b , p) = liftO b (classify (f e) κ p)

  data Decision (B t : HB U) (A : Set) : Set where
    keep : (κ : K (T t)) → (E (T t) κ → A) → Decision B t A
    same : (HB (T t) → A) → Decision B t A
    above : (i : HB U) → hs i ⊲[ (tt , β) ] B → t ⊲[ (tt , β) ] i →
      (HB (T i) → A) → Decision B t A

  pick : ∀ {B t i A} → (HB (T i) → A) → hs i ⊲[ (tt , β) ] B →
    (t ⊲[ (tt , β) ] hs i) ⊎ (hs i ⊲[ (tt , β) ] t) → Decision B t A
  pick to p (inj₂ q) = keep (ek (path-context P k q) (inj₂ tt))
    (λ c → to (frC (path-context P k q) (inj₂ tt) c))
  pick to p (inj₁ hself) = keep (inj₂ tt) to
  pick to p (inj₁ (hsuc hself)) = same to
  pick to p (inj₁ (hsuc q@(hsuc _))) = above _ p q to
  pick to p (inj₁ (hsuc q@(hlim _ _))) = above _ p q to
  pick to p (inj₁ (hsuc q@(hLim _ _))) = above _ p q to

  decide : ∀ {B t A} → t ⊲[ (tt , β) ] B → LgB β → LgB B → Class B A → Decision B t A
  decide {t = t} pt lb lB (base κ to) = keep (ek (path-context P k (z⊲ᴮ {w = (tt , β)} t)) κ)
    (λ c → to (frC (path-context P k (z⊲ᴮ {w = (tt , β)} t)) κ c))
  decide pt lb lB (rank i pi to) = pick to pi (cmpB pi pt (tt , lb) lB)
```
