# YiXVSourceCoordinates
> 验收文件。档位：编译定理。有限源坐标换型、Ω 折叠与嵌入折叠的对齐。
> 接 YiXVSourceSem、SourceAffine*、Finite*，有限搬运比较参照 YiXVCan2Embed；未交完整外层链或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceCoordinates where
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Data.Product using (Σ; _,_)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as P
import OCF.Lean.YiLegFold as Fold
open import OCF.Lean.YiASIface using (Sbᶠ; s0; ss)
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceSlots as Slots
import OCF.Lean.YiXVSourceSelfInput as Default
import OCF.Lean.YiXVSourceCast as C
import OCF.Lean.YiXVSourceFinitePath as F
import OCF.Lean.YiXVSourceEmbed as E

back : ∀ {a n j} → a ≡ J.nat n → J.nat j P.≤ J.nat n → J.nat j P.≤ a
back {j = j} e w = subst (J.nat j P.≤_) (sym e) w
path : ∀ {a b n m} → a ≡ J.nat n → b ≡ J.nat m → b P.≤ a → J.nat m P.≤ J.nat n
path e d w = subst₂ P._≤_ d e w
  where
  subst₂ : ∀ {A B : Set} (R : A → B → Set) {x x′ y y′} → x ≡ x′ → y ≡ y′ → R x y → R x′ y′
  subst₂ R refl refl r = r
bcast : ∀ {a b} (e : a ≡ b) (B : Fold.Base a) → Fold.b⊥ (subst Fold.Base e B) ≡ Fold.b⊥ B
bcast refl B = refl
scast : ∀ {a n} (e : a ≡ J.nat n) (B : Fold.Base a) j w →
  Fold.bs (subst Fold.Base e B) (J.nat j) w ≡ Fold.bs B (J.nat j) (back e w)
scast refl B j w = refl
B₀cast : ∀ {a b} (e : a ≡ b) → subst Fold.Base e (Fold.B₀ a) ≡ Fold.B₀ b
B₀cast refl = refl
botΩ : ∀ n {a} (e : a ≡ J.nat n) ε ρ B →
  Fold.ψ⊥ a ε ρ B (O.Ωt a) ≡ Fold.ψ⊥ (J.nat n) (Default.ev n) (Default.rt n) (subst Fold.Base e B) (O.Ωt (J.nat n))
botΩ n refl ε ρ B rewrite C.ev n ε | C.rt n ρ = refl
slotΩ : ∀ n j {a} (e : a ≡ J.nat n) (s : Sbᶠ n j) ε ρ B (w : J.nat j P.≤ a) β nβ →
  Fold.ψs a ε ρ B (J.nat j) w β nβ (O.Ωt a) ≡
    Fold.ψs (J.nat n) (Default.ev n) (Default.rt n) (subst Fold.Base e B) (J.nat j) (Slots.pth s) β nβ (O.Ωt (J.nat n))
slotΩ n j refl s ε ρ B w β nβ rewrite C.ev n ε | C.rt n ρ | F.thin s w = refl
slotEmb : ∀ n m j {a b} (e : a ≡ J.nat n) (d : b ≡ J.nat m) (s : Sbᶠ n j) (t : Sbᶠ n m)
  ε ρ B (w : J.nat j P.≤ a) β nβ (v : b P.≤ a) →
  Fold.ψs a ε ρ B (J.nat j) w β nβ (P.emb a ε v (O.Ωt b) (O.Ωt-nz b)) ≡
    Fold.ψs (J.nat n) (Default.ev n) (Default.rt n) (subst Fold.Base e B) (J.nat j) (Slots.pth s) β nβ
      (P.emb (J.nat n) (Default.ev n) (Slots.pth t) (O.Ωt (J.nat m)) (O.Ωt-nz (J.nat m)))
slotEmb n m j refl refl s t ε ρ B w β nβ v rewrite C.ev n ε | C.rt n ρ | F.thin s w | F.thin t v = refl

weight : ∀ {n m} (s : Sbᶠ n m) → E.weight s ≤ suc (suc n)
weight s0 = s≤s (s≤s z≤n)
weight (ss s) = s≤s (weight s)
raise : ∀ {n m} → Sbᶠ n m → Sbᶠ (suc n) (suc m)
raise s0 = s0
raise (ss s) = ss (raise s)
from≤ : ∀ {m n} → m ≤ n → Sbᶠ n m
from≤ {m = zero} {n = zero} z≤n = s0
from≤ {m = zero} {n = suc n} z≤n = ss (from≤ {m = zero} {n = n} z≤n)
from≤ {m = suc m} {n = suc n} (s≤s t) = raise (from≤ t)
```
