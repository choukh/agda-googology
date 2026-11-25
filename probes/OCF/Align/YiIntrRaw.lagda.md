# YiIntr：骨架上的 Raw 位置运算

本篇只平行有限构造需要的第一位置传递、合法性回传与有公共界比较。
证明来源是 LevelFixCore 第 3 节；所有新 lc 模式增加三个证据参数，
没有把坐标证据当作可判等对象。字节重生成配方见 YiIntr。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIntrRaw where

open import OCF.Align.YiIntrCore
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import Data.Empty using (⊥-elim)

Cp-tr : ∀ y {a b d} → Cp y a b → Cp y b d → Cp y a d
Dn-cp : ∀ y {a b} d → Cp y a b → Dn y b d → Dn y a d
Dn-tr : ∀ y {a b d} → Dn y a b → Dn y b d → Dn y a d
DnK-tr : ∀ y i₁ i₂ i₃ {a b d} → DnK y i₁ i₂ a b → DnK y i₂ i₃ b d → DnK y i₁ i₃ a d

Cp-tr y (inj₁ refl) q = q
Cp-tr y (inj₂ p) (inj₁ refl) = inj₂ p
Cp-tr y (inj₂ p) (inj₂ q) = inj₂ (Dn-tr y p q)

Dn-tr y {d = d} p q = Dn-cp y d (inj₂ p) q

Dn-cp y (G.suc d) p q = Cp-tr y p q
Dn-cp y (G.lim f) p (n , q) = n , Cp-tr y p q
Dn-cp y (G.lc r c t g) p q = Cp-tr y p q
Dn-cp y (G.em i T) (inj₁ refl) q = q
Dn-cp y {a = G.em i₁ _} {G.em i₂ _} (G.em i T) (inj₂ p) q = DnK-tr y i₁ i₂ i p q

Dn-cp y G.top (inj₁ refl) q = q
Dn-cp (suc k) {G.em _ _} {G.em _ _} G.top (inj₂ p) q = Cp-tr k (inj₂ p) q
Dn-cp (lc k c w₀ b₀ t p₀ g) {G.em (inj₂ (inj₁ _)) _} {G.em (inj₂ (inj₁ _)) _} G.top (inj₂ p) q = Cp-tr t (inj₂ p) q

DnK-tr (suc k) _ _ _ p q = Dn-tr k p q
DnK-tr (lim f) n .n m (refl , p) (refl , q) = refl , Dn-tr (f n) p q
DnK-tr (lc k c w₀ b₀ t p₀ g) (inj₁ _) (inj₁ _) (inj₁ _) p q = Dn-tr k p q
DnK-tr (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) p q = Dn-tr t p q
DnK-tr (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₂ (η , e))) (inj₂ (inj₂ .(η , e))) (inj₂ (inj₂ .(η , e))) (refl , p) (refl , q) = refl , Dn-tr (g η e) p q

Cp-suc : ∀ y {x d} → Cp y (G.suc x) d → Dn y x d
Dn-suc : ∀ y {x} d → Dn y (G.suc x) d → Dn y x d
Cp-suc y (inj₁ refl) = inj₁ refl
Cp-suc y {d = d} (inj₂ p) = Dn-suc y d p
Dn-suc y (G.suc b) (inj₁ refl) = inj₂ (inj₁ refl)
Dn-suc y (G.suc b) (inj₂ p) = inj₂ (Dn-suc y b p)
Dn-suc y (G.lim f) (n , p) = n , inj₂ (Cp-suc y p)
Dn-suc y (G.lc r c t g) p = inj₂ (Cp-suc y p)
Dn-suc y (G.em i T) ()
Dn-suc (suc k) G.top ()
Dn-suc (lc k c w₀ b₀ t p₀ g) G.top ()

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
lgl-dn (lc k c w₀ b₀ t p₀ g) {G.em (inj₂ (inj₁ _)) _} G.top p w = lgl-cp t p tt
lgl-k (suc k) _ _ {b = b} p w = lgl-dn k b p w
lgl-k (lim f) n .n {b = b} (refl , p) w = lgl-dn (f n) b p w
lgl-k (lc k c w₀ b₀ t p₀ g) (inj₁ _) (inj₁ _) {b = b} p w = lgl-dn k b p w
lgl-k (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) {b = b} p w = lgl-dn t b p w
lgl-k (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₂ (η , e))) (inj₂ (inj₂ .(η , e))) {b = b} (refl , p) w = lgl-dn (g η e) b p w

stepsC : ∀ y {f : ℕ → Raw y} → (∀ n → Cp y (f n) (f (suc n))) → ∀ {n m} → n <ᴺ m → Cp y (f n) (f m)
stepsC y s zero = s _
stepsC y s (suc q) = Cp-tr y (stepsC y s q) (s _)

liftS : ∀ k {a b} → Cp k a b → Cp (suc k) (G.em tt a) (G.em tt b)
liftS k (inj₁ refl) = inj₁ refl
liftS k (inj₂ p) = inj₂ p

mapS : ∀ {A B C D : Set} → (A → C) → (B → D) → A ⊎ B → C ⊎ D
mapS f g (inj₁ x) = inj₁ (f x)
mapS f g (inj₂ x) = inj₂ (g x)

cmpC : ∀ y {a b} X → Cp y a X → Cp y b X → Lgl y X → (Cp y a b) ⊎ (Cp y b a)
cmpD : ∀ y {a b} X → Dn y a X → Dn y b X → Lgl y X → (Cp y a b) ⊎ (Cp y b a)
cmpK : ∀ y i₁ i₂ i {a b T} → DnK y i₁ i a T → DnK y i₂ i b T → LglK y i T →
       (Cp y (G.em i₁ a) (G.em i₂ b)) ⊎ (Cp y (G.em i₂ b) (G.em i₁ a))

cmpC y X (inj₁ refl) q w = inj₂ q
cmpC y X (inj₂ p) (inj₁ refl) w = inj₁ (inj₂ p)
cmpC y X (inj₂ p) (inj₂ q) w = cmpD y X p q w

cmpD y (G.suc X) p q w = cmpC y X p q w
cmpD y (G.lim f) (n , p) (m , q) (st , w) with <ᴺ-dec n m
... | injᵃ n<m = cmpC y (f m) (Cp-tr y p (stepsC y st n<m)) q (w m)
... | injᵇ m<n = cmpC y (f n) p (Cp-tr y q (stepsC y st m<n)) (w n)
... | injᶜ refl = cmpC y (f n) p q (w n)
cmpD y (G.lc r c t g) p q (tg , dir , irr , lt , lg) = cmpC y t p q lt
cmpD y {a = G.em i₁ _} {G.em i₂ _} (G.em i T) p q w = cmpK y i₁ i₂ i p q w
cmpD (suc k) {G.em _ _} {G.em _ _} G.top p q w = mapS (liftS k) (liftS k) (cmpC k G.top p q tt)
cmpD (lc k c w₀ b₀ t p₀ g) {G.em (inj₂ (inj₁ _)) _} {G.em (inj₂ (inj₁ _)) _} G.top p q w = mapS lif lif (cmpC t G.top p q tt)
  where
  lif : ∀ {a b} → Cp t a b → Cp (lc k c w₀ b₀ t p₀ g) (G.em (inj₂ (inj₁ tt)) a) (G.em (inj₂ (inj₁ tt)) b)
  lif (inj₁ refl) = inj₁ refl
  lif (inj₂ d) = inj₂ d


cmpK (suc k) _ _ _ {T = T} p q w = mapS (liftS k) (liftS k) (cmpD k T p q w)
cmpK (lim f) n .m m {T = T} (refl , p) (refl , q) w = mapS lifL lifL (cmpD (f m) T p q w)
  where
  lifL : ∀ {a b} → Cp (f m) a b → Cp (lim f) (G.em m a) (G.em m b)
  lifL (inj₁ refl) = inj₁ refl
  lifL (inj₂ d) = inj₂ (refl , d)
cmpK (lc k c w₀ b₀ t p₀ g) (inj₁ _) (inj₁ _) (inj₁ _) {T = T} p q w = mapS lif lif (cmpD k T p q w)
  where
  lif : ∀ {a b} → Cp k a b → Cp (lc k c w₀ b₀ t p₀ g) (G.em (inj₁ tt) a) (G.em (inj₁ tt) b)
  lif (inj₁ refl) = inj₁ refl
  lif (inj₂ d) = inj₂ d
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) {T = T} p q w = mapS lif lif (cmpD t T p q w)
  where
  lif : ∀ {a b} → Cp t a b → Cp (lc k c w₀ b₀ t p₀ g) (G.em (inj₂ (inj₁ tt)) a) (G.em (inj₂ (inj₁ tt)) b)
  lif (inj₁ refl) = inj₁ refl
  lif (inj₂ d) = inj₂ d
cmpK (lc k c w₀ b₀ t p₀ g) (inj₁ _) (inj₂ (inj₁ _)) (inj₁ _) p () w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₁ _) (inj₂ (inj₂ _)) (inj₁ _) p () w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₁ _)) (inj₁ _) (inj₁ _) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) (inj₁ _) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₁ _)) (inj₂ (inj₂ _)) (inj₁ _) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₂ _)) (inj₁ _) (inj₁ _) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₂ _)) (inj₂ (inj₁ _)) (inj₁ _) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₂ _)) (inj₂ (inj₂ _)) (inj₁ _) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₁ _) (inj₁ _) (inj₂ (inj₁ _)) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₁ _) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₁ _) (inj₂ (inj₂ _)) (inj₂ (inj₁ _)) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₁ _)) (inj₁ _) (inj₂ (inj₁ _)) p () w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₁ _)) (inj₂ (inj₂ _)) (inj₂ (inj₁ _)) p () w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₂ _)) (inj₁ _) (inj₂ (inj₁ _)) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₂ _)) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₂ _)) (inj₂ (inj₂ _)) (inj₂ (inj₁ _)) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₁ _) (inj₁ _) (inj₂ (inj₂ _)) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₁ _) (inj₂ (inj₁ _)) (inj₂ (inj₂ _)) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₁ _) (inj₂ (inj₂ _)) (inj₂ (inj₂ _)) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₁ _)) (inj₁ _) (inj₂ (inj₂ _)) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) (inj₂ (inj₂ _)) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₁ _)) (inj₂ (inj₂ _)) (inj₂ (inj₂ _)) () q w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₂ _)) (inj₁ _) (inj₂ (inj₂ _)) p () w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₂ _)) (inj₂ (inj₁ _)) (inj₂ (inj₂ _)) p () w
cmpK (lc k c w₀ b₀ t p₀ g) (inj₂ (inj₂ .(η , e))) (inj₂ (inj₂ .(η , e))) (inj₂ (inj₂ (η , e))) {T = T} (refl , p) (refl , q) w = mapS lif lif (cmpD (g η e) T p q w)
  where
  lif : ∀ {a b} → Cp (g η e) a b → Cp (lc k c w₀ b₀ t p₀ g) (G.em (inj₂ (inj₂ (η , e))) a) (G.em (inj₂ (inj₂ (η , e))) b)
  lif (inj₁ refl) = inj₁ refl
  lif (inj₂ d) = inj₂ (refl , d)
```
