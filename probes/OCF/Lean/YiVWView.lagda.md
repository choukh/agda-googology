# 新块的布劳威尔 View
> 成品候选。来源：`YiLPView`；直接使用新块和值，不经固定旧层号的接口。
> 编译定理 `brwView`：同一个通用记录覆盖一切层号；部分仍为本层对象，值互相 `≼`，ℕ 极限沿值的第一位置步进。
> Ω 坐标为低层树；对象层步进与部分良基见 `YiVWWf`。不作强度验收。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVWView where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps using (zl)
open import OCF.Lean.YiVWVal
open import OCF.Align.BrwViewDef using (View; vz; vs; vl; vΩ; BrwView) renaming (Sig to BSig)

SigY : BSig
SigY = record
  { Ix = L ; B = V ; _≼_ = λ a b → a ≼ b ; Stp = λ a b → a ◁ b
  ; Kd = Pos ; Cd = λ {i} p → Br i p ; LgC = λ _ → ⊤ ; tg = λ {i} _ → i
  ; bz = zero ; bs = suc ; bl = lim ; bΩ = Ω }

VW : (ℓ : L) → V ℓ → Set
VW ℓ v = View SigY Tr (λ {i} x → val i x) (λ _ → ⊤) ℓ v

chT⁻ : (ℓ : L) (c : CH ℓ) → Tr (chL ℓ c) → ChT ℓ c
chT⁻ zero     () y
chT⁻ (nd s h) c y = y

conv : (ℓ : L) (c : CH ℓ) {a b : Tr (chL ℓ c)} → chL ℓ c ⊢ a ◃ b → RCh ℓ c (chT⁻ ℓ c a) (chT⁻ ℓ c b)
conv zero     () d
conv (nd s h) c d = d

conv₀ : (ℓ : L) (c : CH ℓ) {b : Tr (chL ℓ c)} → chL ℓ c ⊢ zero ◃ b → RCh ℓ c (chZ ℓ c) (chT⁻ ℓ c b)
conv₀ zero     () d
conv₀ (nd s h) c d = d

chT-β : (ℓ : L) (c : CH ℓ) (y : Tr (chL ℓ c)) → chT ℓ c (chT⁻ ℓ c y) ≡ y
chT-β zero     () y
chT-β (nd s h) c y = refl

upz′ : (ℓ : L) (c : CH ℓ) → Tr ℓ → (y : Tr (chL ℓ c)) → (zero ≡ y) ⊎ (chL ℓ c ⊢ zero ◃ y) → Tr ℓ
upz′ ℓ c x y (inj₁ _) = x
upz′ ℓ c x y (inj₂ d) = up x c (chT⁻ ℓ c y) (conv₀ ℓ c d)

upz : (ℓ : L) (c : CH ℓ) → Tr ℓ → Tr (chL ℓ c) → Tr ℓ
upz ℓ c x y = upz′ ℓ c x y (zl y)

valCh-β : (ℓ : L) (c : CH ℓ) (y : Tr (chL ℓ c)) → valCh ℓ c (chT⁻ ℓ c y) ≡ emb ℓ c (val (chL ℓ c) y)
valCh-β zero     () y
valCh-β (nd s h) c y = refl

val-upz′ : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) (y : Tr (chL ℓ c)) (s : (zero ≡ y) ⊎ (chL ℓ c ⊢ zero ◃ y))
         → val ℓ (upz′ ℓ c x y s) ≡ val ℓ x ⊹ emb ℓ c (val (chL ℓ c) y)
val-upz′ ℓ c x .zero (inj₁ refl) = refl
val-upz′ ℓ c x y     (inj₂ d)    = cong (val ℓ x ⊹_) (valCh-β ℓ c y)

val-upz : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) (y : Tr (chL ℓ c))
        → val ℓ (upz ℓ c x y) ≡ val ℓ x ⊹ emb ℓ c (val (chL ℓ c) y)
val-upz ℓ c x y = val-upz′ ℓ c x y (zl y)

reidx : ∀ {ℓ} {w w′ : V ℓ} → w′ ≈ w → VW ℓ w → VW ℓ w′
reidx e (vz e′)         = vz (≈-trans e e′)
reidx e (vs y h e′)     = vs y h (≈-trans e e′)
reidx e (vl f h st e′)  = vl f h st (≈-trans e e′)
reidx e (vΩ p g h e′)   = vΩ p g h (≈-trans e e′)

lim≡ : ∀ {ℓ} (a b : ℕ → V ℓ) → ((n : ℕ) → a n ≡ b n) → lim a ≈ lim b
lim≡ a b e = l≼ (λ n → ≼l n (subst (λ t → a n ≼ t) (e n) (≼-refl (a n))))
           , l≼ (λ n → ≼l n (subst (λ t → b n ≼ t) (sym (e n)) (≼-refl (b n))))

Ω≡ : ∀ {ℓ} (p : Pos ℓ) (a b : Br ℓ p → V ℓ) → ((z : Br ℓ p) → a z ≡ b z) → Ω p a ≈ Ω p b
Ω≡ p a b e = Ω≼ (λ z → ≼Ω z (subst (λ t → a z ≼ t) (e z) (≼-refl (a z))))
           , Ω≼ (λ z → ≼Ω z (subst (λ t → b z ≼ t) (sym (e z)) (≼-refl (b z))))

mapUp : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) → VW ℓ (val ℓ x)
      → {v : V (chL ℓ c)} → VW (chL ℓ c) v → VW ℓ (val ℓ x ⊹ emb ℓ c v)
mapUp ℓ c x vx (vz e) = reidx (F≈ ℓ c (val ℓ x) e) vx
mapUp ℓ c x vx (vs y _ e) =
  vs (upz ℓ c x y) tt
     (subst (λ t → (val ℓ x ⊹ emb ℓ c _) ≈ suc t) (sym (val-upz ℓ c x y)) (F≈ ℓ c (val ℓ x) e))
mapUp ℓ c x vx (vl f _ st e) =
  vl (λ n → upz ℓ c x (f n)) (λ n → tt)
     (λ n → subst₂ _◁_ (sym (val-upz ℓ c x (f n))) (sym (val-upz ℓ c x (f (suc n))))
                       (⊹-mono◁ (val ℓ x) (emb-mono◁ ℓ c (st n))))
     (≈-trans (F≈ ℓ c (val ℓ x) e)
              (lim≡ _ _ (λ n → sym (val-upz ℓ c x (f n)))))
mapUp ℓ c x vx (vΩ p g _ e) =
  vΩ (chP ℓ c p) (λ z → upz ℓ c x (g (chBr ℓ c p z))) (λ z _ → tt)
     (≈-trans (F≈ ℓ c (val ℓ x) e)
              (Ω≡ (chP ℓ c p) _ _ (λ z → sym (val-upz ℓ c x (g (chBr ℓ c p z))))))

view : (ℓ : L) (x : Tr ℓ) → VW ℓ (val ℓ x)
view ℓ zero      = vz (≈-refl zero)
view ℓ (suc x)   = vs x tt (≈-refl _)
view ℓ (lim f a) = vl f (λ n → tt) (λ n → val-mono ℓ (a n)) (≈-refl _)
view ℓ (Ω p g)   = vΩ p g (λ z _ → tt) (≈-refl _)
view zero     (up x () y e)
view (nd s h) (up x c y e) = mapUp (nd s h) c x (view (nd s h) x) (view (h c) y)

brwView : BrwView SigY Tr (λ {i} x → val i x) (λ _ → ⊤)
brwView = record { view = λ {i} x _ → view i x }
```
