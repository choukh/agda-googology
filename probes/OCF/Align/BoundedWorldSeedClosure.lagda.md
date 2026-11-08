# 坐标膨胀证书的实际闭包

仅使用已有有向关系闭包；中Ω坐标始终携带Seed0实例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldSeedClosure where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Align.BoundedCompletionUniformIf
open import OCF.Align.BoundedCompletionUniformClosure using (add-rel; right-rel; pure-up; up-value; floor-value)
open import OCF.Lean.TwoSlotValueClosure using (act-mono; act-inflate)
open import OCF.Lean.TwoSlotValueRun using (value-repeat)
open import OCF.Align.BoundedWorldCoverIf using (act)
open import OCF.Align.BoundedWorldValueTwoSlot using (U; V)
open import OCF.Align.BoundedWorldSeedIf
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)

self0 : ∀ {a} → Seed0 a → Value hz a a
self0 {a = hz} s = proj₁ s
self0 {a = hs a} s = proj₁ s
self0 {a = hl f} s = proj₁ s
self0 {a = hΩ (inj₁ ()) g} s
self0 {a = hΩ (inj₂ _) g} s = proj₁ s
self1 : ∀ {a} → Seed1 a → Value (hs hz) a a
self1 {a = hz} s = proj₁ s
self1 {a = hs a} s = proj₁ s
self1 {a = hl f} s = proj₁ s
self1 {a = hΩ (inj₁ (inj₁ ())) g} s
self1 {a = hΩ (inj₁ (inj₂ _)) g} s = proj₁ s
self1 {a = hΩ (inj₂ _) g} s = proj₁ s

add0 : ∀ {a b} → Seed0 a → Seed0 b → Seed0 (a ⊞ b)
add0 {b = hz} sa sb = sa
add0 {b = hs b} sa (bb , sb) = add-rel (self0 sa) bb , add0 sa sb
add0 {b = hl f} sa (bb , sb) = add-rel (self0 sa) bb , (λ n → add0 sa (sb n))
add0 {b = hΩ (inj₁ ()) g} sa sb
add0 {a = a} {b = hΩ (inj₂ _) g} sa (bb , inf , sb) =
  add-rel (self0 sa) bb , (λ c → right-rel a (inf c)) , (λ c → add0 sa (sb c))
add1 : ∀ {a b} → Seed1 a → Seed1 b → Seed1 (a ⊞ b)
add1 {b = hz} sa sb = sa
add1 {b = hs b} sa (bb , sb) = add-rel (self1 sa) bb , add1 sa sb
add1 {b = hl f} sa (bb , sb) = add-rel (self1 sa) bb , (λ n → add1 sa (sb n))
add1 {b = hΩ (inj₁ (inj₁ ())) g} sa sb
add1 {a = a} {b = hΩ (inj₁ (inj₂ _)) g} sa (bb , inf , sb) =
  add-rel (self1 sa) bb , (λ c → right-rel a (inf c)) , (λ c → add1 sa (sb c))
add1 {a = a} {b = hΩ (inj₂ _) g} sa (bb , inf , sb) =
  add-rel (self1 sa) bb , (λ e se → right-rel a (inf e se)) , (λ e se → add1 sa (sb e se))

mul0 : ∀ {a} → Seed0 a → ∀ n → Seed0 (mul a n)
mul0 sa zero = sa
mul0 sa (suc n) = add0 (mul0 sa n) sa
mul1 : ∀ {a} → Seed1 a → ∀ n → Seed1 (mul a n)
mul1 sa zero = sa
mul1 sa (suc n) = add1 (mul1 sa n) sa

act0 : ∀ {a} → Seed0 a → Seed0 (act a)
act0 {a = hz} sa = vs vz , (vz , tt)
act0 {a = hs a} (aa , sa) = value-repeat (act-mono (self0 sa)) , mul0 (act0 sa)
act0 {a = hl f} (aa , sa) = act-mono aa , (λ n → act0 (sa n))
act0 {a = hΩ (inj₁ ()) g} sa
act0 {a = hΩ (inj₂ _) g} (aa , inf , sa) =
  act-mono aa , (λ c → act-inflate (inf c)) , (λ c → act0 (sa c))
act1 : ∀ {a} → Seed1 a → Seed1 (act a)
act1 {a = hz} sa = vs vz , (vz , tt)
act1 {a = hs a} (aa , sa) = value-repeat (act-mono (self1 sa)) , mul1 (act1 sa)
act1 {a = hl f} (aa , sa) = act-mono aa , (λ n → act1 (sa n))
act1 {a = hΩ (inj₁ (inj₁ ())) g} sa
act1 {a = hΩ (inj₁ (inj₂ _)) g} (aa , inf , sa) =
  act-mono aa , (λ c → act-inflate (inf c)) , (λ c → act1 (sa c))
act1 {a = hΩ (inj₂ _) g} (aa , inf , sa) =
  act-mono aa , (λ e se → act-inflate (inf e se)) , (λ e se → act1 (sa e se))

up0 : ∀ (c : Cd) → Seed0 (up c)
up0 hz = vz , tt
up0 (hs c) = pure-up (≤-refl (hs c)) , up0 c
up0 (hl f) = pure-up (≤-refl (hl f)) , (λ n → up0 (f n))
up1 : ∀ {a} → Seed0 a → Seed1 (up a)
up1 {a = hz} s = vz , tt
up1 {a = hs a} s = up-value hz (self0 s) , up1 (proj₂ s)
up1 {a = hl f} s = up-value hz (self0 s) , (λ n → up1 (proj₂ s n))
up1 {a = hΩ (inj₁ ()) g} s
up1 {a = hΩ (inj₂ _) g} (aa , inf , s) =
  up-value hz aa , (λ c → up-value hz (inf c)) , (λ c → up1 (s c))

floor0 : Seed0 (floor zero)
floor0 = floor-value zero , (λ c → pure-up (≤-refl c)) , up0
floor1 : Seed1 (floor 1)
floor1 = floor-value 1 , (λ e se → up-value hz (self0 se)) , (λ e se → up1 se)
```
