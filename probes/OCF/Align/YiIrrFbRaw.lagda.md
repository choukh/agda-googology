# YiIrrFb：新块上一般层的第一位置传递与合法性回传

**档位：编译定理，机械搬运。** `LevelFixCore` §3 的 `Cp-tr`, `Dn-cp`, `lgl-cp` 搬到无关证据块
([RR5IrrCore](RR5IrrCore.lagda.md))，对一切层号；`lc` 模式多两个无关参数，其余逐行相同。
`cmpC` (公共界下的比较) 没有搬：本轮的派发不用它。入口 [YiIrrFb](YiIrrFb.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrFbRaw where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore

Cp-tr : ∀ y {a b d} → Cp y a b → Cp y b d → Cp y a d
Dn-cp : ∀ y {a b} d → Cp y a b → Dn y b d → Dn y a d
Dn-tr : ∀ y {a b d} → Dn y a b → Dn y b d → Dn y a d
DnK-tr : ∀ y i₁ i₂ i₃ {a b d} →
  DnK y i₁ i₂ a b → DnK y i₂ i₃ b d → DnK y i₁ i₃ a d

Cp-tr y (inj₁ refl) q = q
Cp-tr y (inj₂ p) (inj₁ refl) = inj₂ p
Cp-tr y (inj₂ p) (inj₂ q) = inj₂ (Dn-tr y p q)

Dn-tr y {d = d} p q = Dn-cp y d (inj₂ p) q

Dn-cp y (G.suc d) p q = Cp-tr y p q
Dn-cp y (G.lim f) p (n , q) = n , Cp-tr y p q
Dn-cp y (G.lc r c t g) p q = Cp-tr y p q
Dn-cp y (G.em i T) (inj₁ refl) q = q
Dn-cp y {a = G.em i₁ _} {G.em i₂ _} (G.em i T) (inj₂ p) q =
  DnK-tr y i₁ i₂ i p q
Dn-cp y G.top (inj₁ refl) q = q
Dn-cp (suc k) {G.em _ _} {G.em _ _} G.top (inj₂ p) q = Cp-tr k (inj₂ p) q
Dn-cp (lc k c w₀ b₀ t g) {G.em (inj₂ (inj₁ _)) _} {G.em (inj₂ (inj₁ _)) _}
  G.top (inj₂ p) q = Cp-tr t (inj₂ p) q

DnK-tr (suc k) _ _ _ p q = Dn-tr k p q
DnK-tr (lim f) n .n m (refl , p) (refl , q) = refl , Dn-tr (f n) p q
DnK-tr (lc k c w₀ b₀ t g) (inj₁ _) (inj₁ _) (inj₁ _) p q = Dn-tr k p q
DnK-tr (lc k c w₀ b₀ t g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) p q =
  Dn-tr t p q
DnK-tr (lc k c w₀ b₀ t g) (inj₂ (inj₂ (η , e))) (inj₂ (inj₂ .(η , e)))
  (inj₂ (inj₂ .(η , e))) (refl , p) (refl , q) = refl , Dn-tr (g η e) p q

lgl-cp : ∀ y {a b} → Cp y a b → Lgl y b → Lgl y a
lgl-dn : ∀ y {a} b → Dn y a b → Lgl y b → Lgl y a
lgl-k : ∀ y i₁ i₂ {a b} → DnK y i₁ i₂ a b → LglK y i₂ b → LglK y i₁ a
lgl-cp y (inj₁ refl) w = w
lgl-cp y {b = b} (inj₂ p) w = lgl-dn y b p w
lgl-dn y (G.suc b) p w = lgl-cp y p w
lgl-dn y (G.lim f) (n , p) (st , w) = lgl-cp y p (w n)
lgl-dn y (G.lc r c t g) p (tg , dir , irr , lt , lg) = lgl-cp y p lt
lgl-dn y {a = G.em i₁ _} (G.em i T) p w = lgl-k y i₁ i p w
lgl-dn (suc k) {G.em _ _} G.top p w = lgl-cp k p tt
lgl-dn (lc k c w₀ b₀ t g) {G.em (inj₂ (inj₁ _)) _} G.top p w = lgl-cp t p tt
lgl-k (suc k) _ _ {b = b} p w = lgl-dn k b p w
lgl-k (lim f) n .n {b = b} (refl , p) w = lgl-dn (f n) b p w
lgl-k (lc k c w₀ b₀ t g) (inj₁ _) (inj₁ _) {b = b} p w = lgl-dn k b p w
lgl-k (lc k c w₀ b₀ t g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) {b = b} p w =
  lgl-dn t b p w
lgl-k (lc k c w₀ b₀ t g) (inj₂ (inj₂ (η , e))) (inj₂ (inj₂ .(η , e))) {b = b}
  (refl , p) w = lgl-dn (g η e) b p w
```
