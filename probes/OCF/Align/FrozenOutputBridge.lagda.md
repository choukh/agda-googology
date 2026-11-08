# 实际输出与带种子模型的桥

固定第二分量，不选择层号或更新槽；Same 只用作固定类型的结构证据。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenOutputBridge where
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (Lv; mul)
open import OCF.Lean.Fold1Base using (updAt)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Align.FrozenInnerOuter using (same-refl; same-mul)
open import OCF.Align.FrozenOutputIf using (Mode; changing; frozen; update)
import OCF.Align.FrozenOutputIf as If
open import OCF.Align.FrozenOutputModel using (same-trans)
open import OCF.Align.FrozenSupportExt using (Ext; old-ext; frozen-ext)
import OCF.Align.FrozenValueFirst as A
import OCF.Align.FrozenValueSecond as S
import OCF.Align.FrozenOutputSim as CS
import OCF.Lean.Fold1Fold as O
import OCF.Lean.SupCollapseFrozen as N
import OCF.Lean.SupCollapseClosed as C
import OCF.Lean.Fold1 as Original

data Entry : Set where
  outer inner first : Entry
pos : Entry → hz ⊲ C.ω
pos outer = z⊲ᴮ C.ω
pos inner = hlim 2 (hsuc (hsuc hself))
pos first = hlim 1 (hsuc hself)

fold : Mode → Entry → Wd (Lv C.ω) → HB (Lv C.ω) → Cd
fold changing e w c = O.Φ C.ω C.legal-ω hz (pos e) w c
fold frozen e w c = N.Φ C.ω C.legal-ω hz (pos e) w c
H : Mode → Entry → Wd (Lv C.ω) → HB (step S⊥) → Cd
H m e w c = fold m e w (S.branch c)
V : Mode → Entry → Wd (Lv C.ω) → Cd → Cd
V m e w c = fold m e w (hz ⊞ ι 1 (up c))

vz : ∀ m e w → V m e w hz ≡ hs hz
vz changing e w = refl
vz frozen e w = refl
vs : ∀ m e w c → V m e w (hs c) ≡ hl (mul (V m e w c))
vs changing e w c = refl
vs frozen e w c = refl
vl : ∀ m e w f → V m e w (hl f) ≡ hl (λ n → V m e w (f n))
vl changing e w f = refl
vl frozen e w f = refl

pure-reference : ∀ m e w v {a b} → Same a b → Same (V m e w a) (A.F v b)
pure-reference m e w v zz rewrite vz m e w = ss zz
pure-reference m e w v (ss {a} p) rewrite vs m e w a = ll (same-mul (pure-reference m e w v p))
pure-reference m e w v (ll {f} p) rewrite vl m e w f = ll (λ n → pure-reference m e w v (p n))
pure-reference m e w v (oo {κ = ()} p)

writeOne : Mode → Wd (Lv C.ω) → Cd → Wd (Lv C.ω)
writeOne changing w e = updAt w 1 (proj₁ (w 1) , e)
writeOne frozen w e = w
writeTwo : Mode → Wd (Lv C.ω) → Cd → Wd (Lv C.ω)
writeTwo changing = S.writeLow
writeTwo frozen = λ w e → w

Co : Mode → (w : Wd (Lv C.ω)) → Cd →
  (Wd (Lv C.ω) → Cd → Wd (Lv C.ω)) →
  (Wd (Lv C.ω) → Cd → Cd) → (Wd (Lv C.ω) → Cd → Cd) → ℕ → Cd
Co changing = O.Col.oO _⊞_ _⊞_
Co frozen = N.Col.oO _⊞_ _⊞_

sums-same : ∀ {B : Set} m (R : Wd (Lv C.ω) → B → Set)
  w v → R w v → ∀ a b → Same a b →
  ∀ u u′ → (∀ {w v x y} → R w v → Same x y → R (u w x) (u′ v y)) →
  ∀ fx gx ft gt →
  (∀ {w v x y} → R w v → Same x y → Same (fx w x) (gx v y)) →
  (∀ {w v x y} → R w v → Same x y → Same (ft w x) (gt v y)) →
  ∀ n → Same (Co m w a u fx ft n) (O.Col.oO _⊞_ _⊞_ v b u′ gx gt n)
sums-same changing R w v rw a b ab u u′ ru fx gx ft gt rx rt =
  CS.Sim.sums R w v rw a b ab u u′ ru fx gx ft gt rx rt
sums-same frozen R w v rw a b ab u u′ ru fx gx ft gt rx rt =
  CS.SimN.sums R w v rw a b ab u u′ ru fx gx ft gt rx rt

prefix-eq : ∀ m e w → H m e w hz ≡ hl
  (Co m w (proj₂ (w 1)) (writeOne m) (V m first) (V m e))
prefix-eq changing outer w = refl
prefix-eq changing inner w = refl
prefix-eq changing first w = refl
prefix-eq frozen outer w = refl
prefix-eq frozen inner w = refl
prefix-eq frozen first w = refl

prefix-reference : ∀ m e w → proj₂ (w 1) ≡ hz → Same (H m e w hz) Original.TΩ1
prefix-reference m e w low rewrite prefix-eq m e w | low = ll
  (sums-same m (λ _ _ → ⊤) w (tt , hz) tt hz hz zz
    (writeOne m) (λ w e → proj₁ w , e) (λ r p → tt)
    (V m first) A.F (V m e) A.F
    (λ {w} {v} r p → pure-reference m first w v p)
    (λ {w} {v} r p → pure-reference m e w v p))

hs-eq : ∀ m e w c → H m e w (hs c) ≡ hl (mul (H m e w c))
hs-eq changing e w c = refl
hs-eq frozen e w c = refl
hl-eq : ∀ m e w f → H m e w (hl f) ≡ hl (λ n → H m e w (f n))
hl-eq changing e w f = refl
hl-eq frozen e w f = refl
omega-eq : ∀ m e w g → H m e w (hΩ (inj₂ tt) g) ≡ hl
  (Co m w (proj₂ (proj₁ (w 2))) (writeTwo m)
    (λ v c → H m inner v (g c)) (λ v c → H m e v (g c)))
omega-eq changing outer w g = refl
omega-eq changing inner w g = refl
omega-eq changing first w g = refl
omega-eq frozen outer w g = refl
omega-eq frozen inner w g = refl
omega-eq frozen first w g = refl

Rel : Wd (Lv C.ω) → Cd → Set
Rel w b = (proj₂ (w 1) ≡ hz) × Same (proj₂ (proj₁ (w 2))) b
rel-update : ∀ m {w b x y} → Rel w b → Same x y → Rel (writeTwo m w x) (update m b y)
rel-update changing (p , q) r = p , r
rel-update frozen (p , q) r = p , q

open If.Model Original.TΩ1
normalize : ∀ m e w c → Ext c → ∀ {d} → Same c d → ∀ {b} → Rel w b →
  Same (H m e w c) (run m b d)
normalize m e w hz ec zz (p , q) = prefix-reference m e w p
normalize m e w (hs c) ec (ss p) r rewrite hs-eq m e w c =
  ll (same-mul (normalize m e w c ec p r))
normalize m e w (hl f) ec (ll p) r rewrite hl-eq m e w f =
  ll (λ n → normalize m e w (f n) (ec n) (p n) r)
normalize m e w (hΩ (inj₁ ()) g) ec p r
normalize m e w (hΩ (inj₂ tt) g) (respect , eg) (oo {g = h} p) {b} r
  rewrite omega-eq m e w g = ll
    (sums-same m Rel w b r (proj₂ (proj₁ (w 2))) b (proj₂ r)
      (writeTwo m) (update m) (rel-update m)
      (λ v c → H m inner v (g c)) (λ v c → run m v (h c))
      (λ v c → H m e v (g c)) (λ v c → run m v (h c))
      (rec-step inner) (rec-step e))
  where
  rec-step : ∀ e {w b x y} → Rel w b → Same x y → Same (H m e w (g x)) (run m b (h y))
  rec-step e {w} {x = x} {y} r xy = normalize m e w (g x) (eg x)
    (same-trans (respect xy) (p y)) r

old-output-model : ∀ n → Same (S.Old.oo n) (run changing hz (S.Old.ce n))
old-output-model n = normalize changing outer (S.Old.cw n) _ (old-ext n)
  (same-refl _) (low1 n , low2 n)
  where
  low1 : ∀ n → proj₂ (S.Old.cw n 1) ≡ hz
  low1 Data.Nat.zero = refl
  low1 (Data.Nat.suc n) = refl
  low2 : ∀ n → Same (proj₂ (proj₁ (S.Old.cw n 2))) hz
  low2 Data.Nat.zero = zz
  low2 (Data.Nat.suc n) = zz

frozen-output-model : ∀ n → Same (S.Frozen.oo n) (run frozen hz (S.Frozen.ce n))
frozen-output-model n = normalize frozen outer (S.Frozen.cw n) _ (frozen-ext n)
  (same-refl _) (low1 n , low2 n)
  where
  low1 : ∀ n → proj₂ (S.Frozen.cw n 1) ≡ hz
  low1 Data.Nat.zero = refl
  low1 (Data.Nat.suc n) = refl
  low2 : ∀ n → Same (proj₂ (proj₁ (S.Frozen.cw n 2))) hz
  low2 Data.Nat.zero = zz
  low2 (Data.Nat.suc n) = zz
```
