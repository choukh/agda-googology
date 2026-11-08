# 动态路径的扩界与加法闭包

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexFoldPath where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecLeg using (J₁)
open import OCF.Lean.LHRecIf using (LHRecIf)
open import OCF.Lean.HigherIndexClassWorld using (position↑)
open import OCF.Lean.HigherIndexFoldIf

mono : ∀ {β β′ B B′} → β ⊲ β′ → B ⊲[ tt , β′ ] B′ →
  ∀ a → Path β B a → Path β′ B′ a
mono q r hz p = tt
mono q r (hs a) p = mono q r a p
mono q r (hl f) p = λ n → mono q r (f n) (p n)
mono q r (hΩ (inj₁ _ , inj₁ (inj₁ ())) f) p
mono q r (hΩ (inj₁ _ , inj₁ (inj₂ _)) f) p = λ e qe le →
  mono hself (⊲ᴮ↑ (tt , hsuc qe) r) (f e) (p e (⊲ᴮ-tr q qe) le)
mono q r (hΩ (inj₁ _ , inj₂ _) f) p = λ e ad →
  p e (proj₁ (LHRecIf.adm↓ J₁ k ((tt , q) , r) ad))
mono q r (hΩ (inj₂ c , κ) f) ((pc , pos) , p) =
  (⊲ᴮ-tr (⊲ᴮ↑ (tt , q) pc) r , position↑ (tt , q) c κ pos) ,
  λ e → mono q r (f e) (p e)

add : ∀ {β B} a b → Path β B a → Path β B b → Path β B (a ⊞ b)
add a hz pa pb = pa
add a (hs b) pa pb = add a b pa pb
add a (hl f) pa pb = λ n → add a (f n) pa (pb n)
add a (hΩ (inj₁ _ , inj₁ (inj₁ ())) f) pa pb
add a (hΩ (inj₁ _ , inj₁ (inj₂ _)) f) pa pb = λ e qe le →
  add a (f e) (mono (hsuc qe) hself a pa) (pb e qe le)
add a (hΩ (inj₁ _ , inj₂ _) f) pa pb = λ e ad →
  add a (f e)
    (mono (proj₂ (proj₁ (LHRecIf.nx-up J₁ k ad))) (proj₂ (LHRecIf.nx-up J₁ k ad)) a pa)
    (pb e ad)
add a (hΩ (inj₂ c , κ) f) pa (ev , pb) = ev , λ e → add a (f e) pa (pb e)
```
