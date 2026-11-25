# YiXVCountableBase
> 验收文件。档位：编译定理。沿原 Ordᴵ 的字面子项递归给辅助合法性、比较及有限与 ω 层闭实例。
> 推广 YiXVFiniteFamily/Level 的结构递归；共享映射证明供搬运与加法复用。未证明可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableBase where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import OCF.Align.Level as L

Up : ∀ {a κ} → a L.◃₁ κ → L.Ordᶜ a → L.Ordᶜ κ
Up r X = L.up r (L.into (L.◃₁→◃ r) X)
raise : ∀ {a b κ} → a L.◃₁ κ → b L.<ᴵ a → b L.<ᴵ κ
raise L.zero q = L.suc q
raise (L.self n) q = L.lim n q

module Layer (κ : L.Ordᴵ)
  (G< : ∀ i (r : i L.◃ κ) → L.U i r → Set)
  (R< : ∀ i (r : i L.◃ κ) → L.U i r → L.U i r → Set) where
  one : L.Ordᶜ κ
  one = L.suc L.zero
  GU : ∀ {i} → i L.<ᴵ κ → L.Ordᶜ i → Set
  GU {i} q X = G< i (L.<→◃ q) (L.into (L.<→◃ q) X)
  RU : ∀ {i} → i L.<ᴵ κ → L.Ordᶜ i → L.Ordᶜ i → Set
  RU {i} q X Y = R< i (L.<→◃ q) (L.into (L.<→◃ q) X) (L.into (L.<→◃ q) Y)
  Floor : ∀ {i} → i L.<ᴵ κ → L.Ordᶜ i → Set
  Floor {i} q X = RU q (L.Ω i) X
  mutual
    data Gd : L.Ordᶜ κ → Set
    data Le : L.Ordᶜ κ → L.Ordᶜ κ → Set
    data Step : L.Ordᶜ κ → L.Ordᶜ κ → Set
    record SC {i} (q : i L.<ᴵ κ) (f : L.U i (L.<→◃ q) → L.Ordᶜ κ) : Set where
      inductive
      constructor sc
      field
        mo : ∀ X Y → GU q X → GU q Y → Floor q X → RU q X Y → Le (f (L.into (L.<→◃ q) X)) (f (L.into (L.<→◃ q) Y))
        db : ∀ X → GU q X → Floor q X → Le (L.suc (f (L.into (L.<→◃ q) X))) (f (L.into (L.<→◃ q) (L.suc X)))
        po : Le one (f (L.into (L.<→◃ q) (L.Ω i)))
    data Gd where
      gz : Gd L.zero
      gs : ∀ {X} → Gd X → Gd (L.suc X)
      gl : ∀ {f} → (∀ n → Gd (f n)) → Gd (L.lim f)
      gn : ∀ {i} {q : i L.<ᴵ κ} {f} → L.limᵢ q f L.≅ L.limᵢ q f → SC q f → (∀ X → GU q X → Floor q X → Gd (f (L.into (L.<→◃ q) X))) → Gd (L.limᵢ q f)
      gu : ∀ {i} (r : i L.◃₁ κ) {X} → G< i (L.◃₁→◃ r) (L.into (L.◃₁→◃ r) X) → Gd (Up r X)
    data Le where
      pack : ∀ {X Y} → Gd X → Gd Y → Step X Y → Le X Y
    data Step where
      ce : ∀ {X Y} → X L.≅ Y → Step X Y
      rr : ∀ {X} → Step X X
      zz : ∀ {Y} → Step L.zero Y
      ss : ∀ {X Y} → Le X Y → Step (L.suc X) (L.suc Y)
      ws : ∀ {X Y} → Le X Y → Step X (L.suc Y)
      ll : ∀ {f Y} → (∀ n → Le (f n) Y) → Step (L.lim f) Y
      lr : ∀ {X f} n → Le X (f n) → Step X (L.lim f)
      nn : ∀ {i} {q r : i L.<ᴵ κ} {f : L.U i (L.<→◃ q) → L.Ordᶜ κ} {g : L.U i (L.<→◃ r) → L.Ordᶜ κ} →
        (∀ X Y → GU q X → GU r Y → Floor q X → RU q X Y →
          Le (f (L.into (L.<→◃ q) X)) (g (L.into (L.<→◃ r) Y))) → Step (L.limᵢ q f) (L.limᵢ r g)
      aa : ∀ {i X} {q : i L.<ᴵ κ} {f} → Le X (f (L.into (L.<→◃ q) (L.Ω i))) → Step X (L.limᵢ q f)
      uu : ∀ {i X Y} (r : i L.◃₁ κ) → R< i (L.◃₁→◃ r) (L.into (L.◃₁→◃ r) X) (L.into (L.◃₁→◃ r) Y) → Step (Up r X) (Up r Y)
      uS : ∀ {i X} (r : i L.◃₁ κ) → G< i (L.◃₁→◃ r) (L.into (L.◃₁→◃ r) X) → Step (L.suc (Up r X)) (Up r (L.suc X))
      uS⁻ : ∀ {i X} (r : i L.◃₁ κ) → G< i (L.◃₁→◃ r) (L.into (L.◃₁→◃ r) X) → Step (Up r (L.suc X)) (L.suc (Up r X))
      uZ : ∀ {i} (r : i L.◃₁ κ) → Step (Up r L.zero) L.zero
      uZ⁻ : ∀ {i} (r : i L.◃₁ κ) → Step L.zero (Up r L.zero)
      uL : ∀ {i f} (r : i L.◃₁ κ) → (∀ n → G< i (L.◃₁→◃ r) (L.into (L.◃₁→◃ r) (f n))) → Step (Up r (L.lim f)) (L.lim (λ n → Up r (f n)))
      uL⁻ : ∀ {i f} (r : i L.◃₁ κ) → (∀ n → G< i (L.◃₁→◃ r) (L.into (L.◃₁→◃ r) (f n))) → Step (L.lim (λ n → Up r (f n))) (Up r (L.lim f))
      uN : ∀ {i j} (r : i L.◃₁ κ) (q : j L.<ᴵ i) {f : L.U j (L.<→◃ q) → L.Ordᶜ i} →
        G< i (L.◃₁→◃ r) (L.into (L.◃₁→◃ r) (L.limᵢ q f)) →
        Step (Up r (L.limᵢ q f)) (L.limᵢ (raise r q) (λ u → Up r (f (L.coe (L.<→◃ (raise r q)) (L.<→◃ q) u))))
      uN⁻ : ∀ {i j} (r : i L.◃₁ κ) (q : j L.<ᴵ i) {f : L.U j (L.<→◃ q) → L.Ordᶜ i} →
        G< i (L.◃₁→◃ r) (L.into (L.◃₁→◃ r) (L.limᵢ q f)) →
        Step (L.limᵢ (raise r q) (λ u → Up r (f (L.coe (L.<→◃ (raise r q)) (L.<→◃ q) u)))) (Up r (L.limᵢ q f))
      tr : ∀ {X Y Z} → Le X Y → Le Y Z → Step X Z

  left : ∀ {X Y} → Le X Y → Gd X
  left (pack gx gy p) = gx
  right : ∀ {X Y} → Le X Y → Gd Y
  right (pack gx gy p) = gy
  rfl : ∀ {X} → Gd X → Le X X
  rfl gx = pack gx gx rr
  trans : ∀ {X Y Z} → Le X Y → Le Y Z → Le X Z
  trans t u = pack (left t) (right u) (tr t u)

mutual
  Gd< : ∀ {κ} i (r : i L.◃ κ) → L.U i r → Set
  Gd< i L.zero X = Layer.Gd i Gd< Le< X
  Gd< i (L.suc r) X = Gd< i r X
  Gd< _ (L.self {f} n) X = Layer.Gd (f n) Gd< Le< X
  Gd< i (L.lim n r) X = Gd< i r X
  Le< : ∀ {κ} i (r : i L.◃ κ) → L.U i r → L.U i r → Set
  Le< i L.zero X Y = Layer.Le i Gd< Le< X Y
  Le< i (L.suc r) X Y = Le< i r X Y
  Le< _ (L.self {f} n) X Y = Layer.Le (f n) Gd< Le< X Y
  Le< i (L.lim n r) X Y = Le< i r X Y
Gd : ∀ {κ} → L.Ordᶜ κ → Set
Gd {κ} = Layer.Gd κ Gd< Le<
Le : ∀ {κ} → L.Ordᶜ κ → L.Ordᶜ κ → Set
Le {κ} = Layer.Le κ Gd< Le<

good-in : ∀ {κ i} (r : i L.◃ κ) {X} → Gd X → Gd< i r (L.into r X)
good-in L.zero h = h
good-in (L.suc r) h = good-in r h
good-in (L.self n) h = h
good-in (L.lim n r) h = good-in r h
good-out : ∀ {κ i} (r : i L.◃ κ) {X} → Gd< i r (L.into r X) → Gd X
good-out L.zero h = h
good-out (L.suc r) h = good-out r h
good-out (L.self n) h = h
good-out (L.lim n r) h = good-out r h
le-in : ∀ {κ i} (r : i L.◃ κ) {X Y} → Le X Y → Le< i r (L.into r X) (L.into r Y)
le-in L.zero h = h
le-in (L.suc r) h = le-in r h
le-in (L.self n) h = h
le-in (L.lim n r) h = le-in r h
le-out : ∀ {κ i} (r : i L.◃ κ) {X Y} → Le< i r (L.into r X) (L.into r Y) → Le X Y
le-out L.zero h = h
le-out (L.suc r) h = le-out r h
le-out (L.self n) h = h
le-out (L.lim n r) h = le-out r h

module Basics (κ : L.Ordᴵ) where
  module D = Layer κ Gd< Le<
  z≤ : ∀ {X} → Gd X → Le (L.zero {ℓ = κ}) X
  z≤ gx = D.pack D.gz gx D.zz
  s≤ : ∀ {X Y} → Le {κ} X Y → Le (L.suc X) (L.suc Y)
  s≤ t = D.pack (D.gs (D.left t)) (D.gs (D.right t)) (D.ss t)
  up : ∀ {i X} (r : i L.◃₁ κ) → Gd X → Gd (Up r X)
  up r gx = D.gu r (good-in (L.◃₁→◃ r) gx)
  up-mono : ∀ {i X Y} (r : i L.◃₁ κ) → Le X Y → Le (Up r X) (Up r Y)
  up-mono {i} r t = D.pack (up r (Layer.left i Gd< Le< t)) (up r (Layer.right i Gd< Le< t))
    (D.uu r (le-in (L.◃₁→◃ r) t))
  up-suc : ∀ {i X} (r : i L.◃₁ κ) → Gd X → Le (L.suc (Up r X)) (Up r (L.suc X))
  up-suc {i} r gx = D.pack (D.gs (up r gx)) (up r (Layer.gs gx)) (D.uS r (good-in (L.◃₁→◃ r) gx))
  one-up : ∀ {i X} (r : i L.◃₁ κ) → Le (L.suc L.zero) X → Le D.one (Up r X)
  one-up {i} {X} r t = D.trans (D.trans (s≤ (z≤ (up r (Layer.gz {κ = i})))) (up-suc r (Layer.gz {κ = i})))
    (up-mono r t)

module Zero = Layer L.zero Gd< Le<
module One = Layer (L.suc L.zero) Gd< Le<
module Omega = Layer L.ωᴵ Gd< Le<

model : ∀ κ → Gd (L.Ω κ) × Le (L.suc L.zero) (L.Ω κ)
model L.zero = h , Layer.rfl L.zero Gd< Le< h
  where h = Layer.gs Layer.gz
model (L.suc κ) = node , D.pack (D.gs D.gz) node (D.aa (Basics.one-up (L.suc κ) L.zero (proj₂ (model κ))))
  where
  module D = Layer (L.suc κ) Gd< Le<
  node : Gd (L.Ω (L.suc κ))
  node = D.gn (L.Ω-≅ (L.s≅ (L.≅ᴵ-refl κ))) (D.sc
    (λ X Y gx gy o t → Basics.up-mono (L.suc κ) L.zero t)
    (λ X gx o → Basics.up-suc (L.suc κ) L.zero gx)
    (Basics.one-up (L.suc κ) L.zero (proj₂ (model κ))))
    (λ X gx o → Basics.up (L.suc κ) L.zero gx)
model (L.lim f s) = node , D.pack (D.gs D.gz) node (D.lr 0 (Basics.one-up (L.lim f s) (L.self 0) (proj₂ (model (f 0)))))
  where
  module D = Layer (L.lim f s) Gd< Le<
  node : Gd (L.Ω (L.lim f s))
  node = D.gl (λ n → Basics.up (L.lim f s) (L.self n) (proj₁ (model (f n))))

groundΩ : Gd (L.Ω L.zero)
groundΩ = proj₁ (model L.zero)
ground-pos : Le (L.suc L.zero) (L.Ω L.zero)
ground-pos = proj₂ (model L.zero)
oneΩ : Gd (L.Ω (L.suc L.zero))
oneΩ = proj₁ (model (L.suc L.zero))
one-pos : Le (L.suc L.zero) (L.Ω (L.suc L.zero))
one-pos = proj₂ (model (L.suc L.zero))
finiteΩ : ∀ n → Gd (L.Ω (L.natᴵ n)) × Le (L.suc L.zero) (L.Ω (L.natᴵ n))
finiteΩ n = model (L.natᴵ n)
omegaΩ : Gd (L.Ω L.ωᴵ)
omegaΩ = proj₁ (model L.ωᴵ)
omega-pos : Le (L.suc L.zero) (L.Ω L.ωᴵ)
omega-pos = proj₂ (model L.ωᴵ)

self : ∀ {κ} {X : L.Ordᶜ κ} → Gd X → X L.≅ X
self Layer.gz = L.z≅
self (Layer.gs gx) = L.s≅ (self gx)
self (Layer.gl gf) = L.l≅ (λ n → self (gf n))
self (Layer.gn ex law gb) = ex
self (Layer.gu L.zero gx) = L.upˡ (L.upʳ (self gx))
self (Layer.gu (L.self n) gx) = L.upˡ (L.upʳ (self gx))
```
