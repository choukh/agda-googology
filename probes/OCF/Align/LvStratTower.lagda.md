# 分层的 $\approx$: 加一层地板, 层号可以含 `limᴼ` (底座)

> 底座, 不含记号. 结论写在 [LvStrat](LvStrat.lagda.md). 由 [LevelKTower](LevelKTower.lagda.md) 改写. `Next`: 给阶段 `St`, 新层 `new` (不要 `NoO`) 与好层号 $L$. 新的低层是 **$\approx$ `new` 的全部层号**, 不只字面的 `new`: 这是 `low≈` 要的, 也是丰富的世界里躲不开的 (`at (limᴼ 0 toLv) (x , r)` 随 $x$ 取到 $\approx$ 而不字面相同的层). 新地板: "层 $\approx$ `new`, 树可容许, 层号 $\approx$ $L$ 的某个可容许字面前驱". 比较仍是 $L$ 的 `<-decᴬ`, 只比较同一个上界之下的元.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvStratTower where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <⇒≤; m≤n⇒m<n∨m≡n; <-irrefl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; Tree; limᵢ; up; Ω; toLv; σ-id; add; intoL)
open import OCF.Align.InaccFloorTree using (Sib; natL; fin; module PF)
open import OCF.Align.LvStratBase using (AdmOf; LoOf; tr; Fl; module Leaf; Stage; Ext; module Move)
open import OCF.Align.LvStratTr using (module TrSpec)
open import OCF.Align.LvStratFin using (IsK; module Fin; at-nat; natL-inj)
```

## §1 第 0 阶段: 没有地板

```agda
fl₀ : Fl
fl₀ = record { Lw = λ _ → ⊥ ; A = λ _ _ → ⊥ ; A→Lw = λ _ _ () ; low-at = λ _ () ; low-lo = λ _ () }

St₀ : Stage
St₀ = record
  { fl = fl₀ ; low≈ = λ () ; tr-A = λ () ; low-cx = λ _ () ; ΩA = λ _ () ; pΩ = λ _ () ; cmpA = λ _ _ _ () ; cxA = λ _ _ () ; twA = λ _ _ () }

isK₀ : IsK 0 St₀
isK₀ = record { lw⇒ = λ _ () ; ⇐lw = λ _ () }
```

## §2 加一层地板

```agda
record NewLevel (St : Stage) (new : Lv) : Set where
  open Stage St
  open Leaf fl
  field
    nw-lo  : Lo new
    nw-cx  : Cx new
    nw-at  : BL new
    nw-≉   : ∀ {b} → Lw b → new ≈ᴮ b → ⊥
    nw-pΩ  : new ≺ᴬ toLv (Ω new)

record World (St : Stage) (new : Lv) : Set where
  open Stage St
  open Leaf fl
  field
    L   : Lv
    loL : Lo L
    cxL : Cx L
    hΩ  : toLv (Ω new) ≺ᴬ L

module Next (St : Stage) (new : Lv) (N : NewLevel St new) (W : World St new) where
  open Stage St
  open Leaf fl
  open NewLevel N
  open World W
  open TrSpec St using (trOK)

  A′ : (j : Lv) → Ordᴸ j → Set
  A′ j x = A j x ⊎ (j ≈ᴮ new × Tw j x × Σ (Pre L) λ p → Adm L p × toLv x ≈ᴮ at L p)

  Lw′ : Lv → Set
  Lw′ j = Lw j ⊎ j ≈ᴮ new

  ¬old : ∀ {j} → Lw j → j ≈ᴮ new → ⊥
  ¬old l e = nw-≉ l (≈ᴮ-sym e)

  A⊃′ : ∀ {j x} → Lw j → A′ j x → A j x
  A⊃′ l (inj₁ a) = a
  A⊃′ l (inj₂ (e , _)) = ⊥-elim (¬old l e)

  adm′↓ : ∀ c → Lo c → ∀ r → AdmOf A′ c r → Adm c r
  adm′↓ (suc k)    l (inj₁ _)        d = tt
  adm′↓ (suc k)    l (inj₂ r)        d = adm′↓ k l r d
  adm′↓ (lim f)    l (n , r)         d = adm′↓ (f n) (l n) r d
  adm′↓ (limᴼ k g) l (inj₁ (inj₁ _)) d = tt
  adm′↓ (limᴼ k g) l (inj₁ (inj₂ r)) d = adm′↓ k (low-lo k (proj₁ l)) r d
  adm′↓ (limᴼ k g) l (inj₂ (x , r)) (a , d) =
    let ax = A⊃′ (proj₁ l) a in ax , adm′↓ (g x) (proj₂ l x ax) r d

  lo′ : ∀ a → Lo a → LoOf Lw′ A′ a
  lo′ zero       l = tt
  lo′ (suc k)    l = lo′ k l
  lo′ (lim f)    l = λ n → lo′ (f n) (l n)
  lo′ (limᴼ k g) (lk , lg) = inj₁ lk , (λ x a → lo′ (g x) (lg x (A⊃′ lk a)))

  bl-copy : ∀ {j} → j ≈ᴮ new → BL j
  bl-copy {j} e r d with path≈ e r (Adm→B j r d)
  ... | r′ , d′ , e′ = low≈ (blL nw-at r′ d′) (≈ᴮ-sym e′)

  lo-copy : ∀ {j} → j ≈ᴮ new → Lo j
  lo-copy e = lo≈ e nw-lo

  fl′ : Fl
  fl′ = record
    { Lw = Lw′
    ; A = A′
    ; A→Lw = λ { k x (inj₁ a) → inj₁ (A→Lw k x a) ; k x (inj₂ (e , _)) → inj₂ e }
    ; low-at = λ { j (inj₁ l) r d → inj₁ (low-at j l r (adm′↓ j (low-lo j l) r d))
                 ; j (inj₂ e) r d → inj₁ (bl-copy e r (adm′↓ j (lo-copy e) r d)) }
    ; low-lo = λ { j (inj₁ l) → lo′ j (low-lo j l)
                 ; j (inj₂ e) → lo′ j (lo-copy e) }
    }

  ext : Ext fl fl′
  ext = record { low⊂ = inj₁ ; A⊂ = inj₁ ; A⊃ = A⊃′ }

  loA : ∀ {j x} → A j x → Lo (toLv x)
  loA {j} {x} a = lo-toLv (lw→bl (A→Lw j x a)) x (twA j x a)

  open Move fl fl′ ext low≈ loA public

  -- 新地板元的 Rp, Cx: 来自世界
  cx-new : ∀ {k} (x : Ordᴸ k) → (Σ (Pre L) λ p → Adm L p × toLv x ≈ᴮ at L p) → Cx (toLv x)
  cx-new x (p , dp , e) = cx≈ e (cx-at low-cx L loL cxL p dp)

  ΩL : ∀ {j} → j ≈ᴮ new → Σ (Pre L) λ p → Adm L p × toLv (Ω j) ≈ᴮ at L p
  ΩL e with Ωlv A-tr (bl-copy e) nw-at e | hΩ
  ... | t | viaᴬ p d e′ = p , d , ≈ᴮ-trans t e′

  tr-A′ : ∀ {j j′} → Lw′ j → j L′.≈ᴮ j′ → ∀ z → A′ j z → A′ j′ (tr j j′ z) × toLv z L′.≈ᴮ toLv (tr j j′ z)
  tr-A′ {j} {j′} (inj₁ l) e z (inj₁ a) =
    let e₀ = ≈↓ (low-lo j l) e
        i  = tr-A l e₀ z a
    in inj₁ (proj₁ i) , ≈↑ (proj₂ i)
  tr-A′ (inj₁ l) e z (inj₂ (e₁ , _)) = ⊥-elim (¬old l e₁)
  tr-A′ (inj₂ e₁) e z (inj₁ a) = ⊥-elim (¬old (A→Lw _ z a) e₁)
  tr-A′ {j} {j′} (inj₂ e₁) e z (inj₂ (_ , tz , p , dp , ez)) =
    let e₀  = ≈↓ (lo-copy e₁) e
        e₂  = ≈ᴮ-trans (≈ᴮ-sym e₀) e₁
        cj′ = cx≈ e₂ nw-cx
        i   = trOK (bl-copy e₁) (lo-copy e₁) (proj₁ (proj₂ cj′)) e₀ z tz (proj₁ (proj₂ (cx-new z (p , dp , ez))))
    in inj₂ (e₂ , proj₁ i , p , dp , ≈ᴮ-trans (≈ᴮ-sym (proj₂ i)) ez) , ≈↑ (proj₂ i)

  cmp′ : ∀ j x y → A′ j x → A′ j y → L′.Tri (toLv x) (toLv y)
  cmp′ j x y (inj₁ a) (inj₁ a′) = Tri↑ (cmpA j x y a a′)
  cmp′ j x y (inj₁ a) (inj₂ (e , _)) = ⊥-elim (¬old (A→Lw j x a) e)
  cmp′ j x y (inj₂ (e , _)) (inj₁ a′) = ⊥-elim (¬old (A→Lw j y a′) e)
  cmp′ j x y (inj₂ (_ , _ , p , dp , e)) (inj₂ (_ , _ , q , dq , e′)) =
    Tri↑ (shL e (shR e′ (<-decᴬ L (proj₁ cxL) p q dp dq)))

  cx′ : ∀ j x → A′ j x → L′.Cx (toLv x)
  cx′ j x (inj₁ a) = Cx↑ (toLv x) (loA a) (cxA j x a)
  cx′ j x (inj₂ (e , t , w)) = Cx↑ (toLv x) (lo-toLv (bl-copy e) x t) (cx-new x w)

  tw′ : ∀ j x → A′ j x → L′.Tw j x
  tw′ j x (inj₁ a) = tw↑ j (lw→bl (A→Lw j x a)) x (twA j x a)
  tw′ j x (inj₂ (e , t , _)) = tw↑ j (bl-copy e) x t

  St′ : Stage
  St′ = record
    { fl = fl′
    ; low≈ = λ { (inj₁ l) e → inj₁ (low≈ l (≈↓ (low-lo _ l) e))
               ; (inj₂ e₁) e → inj₂ (≈ᴮ-trans (≈ᴮ-sym (≈↓ (lo-copy e₁) e)) e₁) }
    ; tr-A = tr-A′
    ; low-cx = λ { j (inj₁ l) → Cx↑ j (low-lo j l) (low-cx j l)
                 ; j (inj₂ e) → Cx↑ j (lo-copy e) (cx≈ e nw-cx) }
    ; ΩA = λ { j (inj₁ l) → inj₁ (ΩA j l)
             ; j (inj₂ e) → inj₂ (e , tw-Ω twA j (bl-copy e) , ΩL e) }
    ; pΩ = λ { j (inj₁ l) → ≺↑ (pΩ j l)
             ; j (inj₂ e) → ≺↑ (≺ᴬ-respˡ e (≺ᴬ-respʳ nw-pΩ (≈ᴮ-sym (Ωlv A-tr (bl-copy e) nw-at e)))) }
    ; cmpA = cmp′
    ; cxA = cx′
    ; twA = tw′
    }
```

## §3 自然数的塔

```agda
module NatStep (K : ℕ) (St : Stage) (isK : IsK K St) where
  open Stage St
  open Leaf fl
  open IsK isK

  Big : Set
  Big = ∀ m → m < K → ∀ n → Σ (Ordᴸ (natL m)) λ z → A (natL m) z × natL n ≺ᴬ toLv z

  One : Set
  One = ∀ m → m < K → A (natL m) (Tree.suc Tree.zero)

  nat≈ : ∀ n {b} → natL n ≈ᴮ b → natL n ≡ b
  nat≈ zero z≈ = refl
  nat≈ (suc n) (s≈ e) = cong Lv.suc (nat≈ n e)

  lo-nat : ∀ n → Lo (natL n)
  lo-nat zero    = tt
  lo-nat (suc n) = lo-nat n

  cx-nat : ∀ n → Cx (natL n)
  cx-nat zero    = tt , tt , tt
  cx-nat (suc n) = cx-nat n

  lw-K : Lw (natL K) → ⊥
  lw-K l with lw⇒ _ l
  ... | m , p , e = <-irrefl (natL-inj m K (sym e)) p

  bigΩ : Big → ∀ k → k < K → ∀ n → natL n ≺ᴬ toLv (Ω (natL (suc k)))
  bigΩ b k p n with b k p n
  ... | z , az , viaᴬ q d e = viaᴬ (inj₂ (z , q)) (az , d) e

  module WithBig (bg : Big) where
    pΩ-K : natL K ≺ᴬ toLv (Ω (natL K))
    pΩ-K = go K ≤-refl where
      go : ∀ k → k ≤ K → natL k ≺ᴬ toLv (Ω (natL k))
      go zero    _ = viaᴬ (inj₁ tt) tt z≈
      go (suc k) p = bigΩ bg k p (suc k)

    new : NewLevel St (natL K)
    new = record
      { nw-lo = lo-nat K
      ; nw-cx = cx-nat K
      ; nw-at = λ r _ → let m , p , e = at-nat K r in subst Lw (sym e) (⇐lw m p)
      ; nw-≉ = λ l e → lw-K (subst Lw (sym (nat≈ K e)) l)
      ; nw-pΩ = pΩ-K
      }

-- 世界: 第 0 层要含全部自然数
record WorldK (K : ℕ) (St : Stage) : Set where
  open Stage St
  open Leaf fl
  field
    w   : World St (natL K)
    b0  : K ≡ 0 → ∀ n → natL n ≺ᴬ World.L w

Twr : ℕ → Set₁
Twr K = Σ Stage λ St → Σ (IsK K St) λ isK → NatStep.Big K St isK × NatStep.One K St isK

nt : ℕ → Ordᴸ zero
nt zero    = Tree.zero
nt (suc n) = Tree.suc (nt n)

nt≡ : ∀ n → toLv (nt n) ≡ natL n
nt≡ zero    = refl
nt≡ (suc n) = cong Lv.suc (nt≡ n)

module Step (K : ℕ) (St : Stage) (isK : IsK K St) (bg : NatStep.Big K St isK) (on : NatStep.One K St isK) (WK : WorldK K St) where
  open NatStep K St isK
  open WithBig bg
  open WorldK WK
  open Next St (natL K) new w public

  isK′ : IsK (suc K) St′
  isK′ = record
    { lw⇒ = λ { j (inj₁ l) → let m , p , e = IsK.lw⇒ isK j l in m , ≤-trans p (<⇒≤ ≤-refl) , e
              ; j (inj₂ e) → K , ≤-refl , sym (nat≈ K (L.≈ᴮ-sym e)) }
    ; ⇐lw = λ m p → go m p
    }
    where
    go : ∀ m → m < suc K → Fl.Lw fl′ (natL m)
    go m (s≤s p) with m≤n⇒m<n∨m≡n p
    ... | inj₁ q = inj₁ (IsK.⇐lw isK m q)
    ... | inj₂ refl = inj₂ (L.≈ᴮ-refl _)

  bg′ : NatStep.Big (suc K) St′ isK′
  bg′ m (s≤s p) n with m≤n⇒m<n∨m≡n p
  ... | inj₁ q = let z , az , h = bg m q n in z , inj₁ az , ≺↑ h
  ... | inj₂ refl = top K refl n
    where
    tw-z : ∀ n → L.Tw zero (nt n)
    tw-z zero    = tt
    tw-z (suc n) = tw-z n
    top : ∀ K₀ → K₀ ≡ K → ∀ n → Σ (Ordᴸ (natL K)) λ z → A′ (natL K) z × natL n L′.≺ᴬ toLv z
    top zero    e n with sym e
    ... | refl with b0 refl (suc n)
    ...   | Leaf.viaᴬ q d h =
      nt (suc n) , inj₂ (L.≈ᴮ-refl _ , tw-z (suc n) , q , d , subst (λ u → u L.≈ᴮ at (World.L w) q) (sym (nt≡ (suc n))) h) ,
      L′.viaᴬ (inj₁ tt) tt (L′.≡→≈′ (sym (nt≡ n)))
    top (suc k) refl n =
      Ω (natL (suc k)) , Stage.ΩA St′ _ (inj₂ (L.≈ᴮ-refl _)) , ≺↑ (bigΩ bg k ≤-refl n)

  on′ : NatStep.One (suc K) St′ isK′
  on′ m (s≤s p) with m≤n⇒m<n∨m≡n p
  ... | inj₁ q = inj₁ (on m q)
  ... | inj₂ refl = inj₂ (L.≈ᴮ-refl _ , tt , top K refl)
    where
    top : ∀ K₀ → K₀ ≡ K → Σ (Pre (World.L w)) λ q → L.Adm (World.L w) q × Lv.suc Lv.zero L.≈ᴮ at (World.L w) q
    top zero e with sym e
    ... | refl with b0 refl 1
    ...   | Leaf.viaᴬ q d h = q , d , h
    top (suc k) refl with L.≺⊑ (bigΩ bg k ≤-refl 1) (L.≺→⊑ (World.hΩ w))
    ... | Leaf.viaᴬ q d h = q , d , h

  next : Twr (suc K)
  next = St′ , isK′ , bg′ , on′
```

## §4 世界的选择

```agda
module W-ω₀ where
  open Stage St₀
  open Leaf fl
  open NatStep 0 St₀ isK₀

  ω : Lv
  ω = lim natL

  W-ω : WorldK 0 St₀
  W-ω = record
    { w = record
        { L = ω
        ; loL = lo-nat
        ; cxL = ((λ n r d → viaᴬ (inj₂ r) d (≈ᴮ-refl _)) , (λ n → proj₁ (cx-nat n))) ,
                (λ n → proj₁ (proj₂ (cx-nat n))) ,
                (λ n → proj₂ (proj₂ (cx-nat n)))
        ; hΩ = viaᴬ (2 , inj₁ tt) tt (≈ᴮ-refl _)
        }
    ; b0 = λ _ n → viaᴬ (suc n , inj₁ tt) tt (≈ᴮ-refl _)
    }
open W-ω₀ using (W-ω; ω) public

module Worlds (S : Sib) (k : ℕ) (St : Stage) (isK : IsK (suc k) St) where
  open Fin S St
  K : ℕ
  K = suc k
  open K-stage K isK

  ΩK : Ordᴸ (natL K)
  ΩK = Ω (natL K)

  ΩK-self : Eq (natL K) ΩK ΩK
  ΩK-self = Ω-self (natL K) (proj₁ (lvp-nat K)) (proj₁ (proj₂ (lvp-nat K)))

  W-Ω : WorldK K St
  W-Ω = record
    { w = record
        { L = suc (toLv ΩK)
        ; loL = lo-toLv bl-K ΩK (eq→tw bl-K ΩK ΩK-self)
        ; cxL = cx-tree bl-K GΩ-K ΩK-self
        ; hΩ = viaᴬ (inj₁ tt) tt (≈ᴮ-refl _)
        }
    ; b0 = λ ()
    }

  module WF (one : ∀ m → m < K → A (natL m) (Tree.suc Tree.zero)) (θ : Lv) (p : LvP θ) where
    Ω≺ψ₁ : toLv ΩK ≺ᴬ toLv (ψⁿ K (Ω zero))
    Ω≺ψ₁ = viaᴬ (2 , inj₂ (Tree.suc Tree.zero , inj₁ tt)) (one k ≤-refl , tt) (≈ᴮ-refl _)

    w₀ : Ordᴸ (natL K)
    w₀ = ψⁿ K (Ω θ)

    w₀-self : Eq (natL K) w₀ w₀
    w₀-self = Eq-ψᴷ (Ω-self θ (proj₁ p) (proj₁ (proj₂ p)))

    ψ₁⊑ψ : toLv (ψⁿ K (Ω zero)) ⊑ᴬ toLv (ψⁿ K (Ω θ))
    ψ₁⊑ψ = Ω0 θ (ψo (fin K refl) (fin K refl) tt (ok-K θ) Ti-K (idO {b = bl-K} {b′ = bl-K}))

    W-F : WorldK K St
    W-F = record
      { w = record
          { L = suc (toLv w₀)
          ; loL = lo-toLv bl-K w₀ (eq→tw bl-K w₀ w₀-self)
          ; cxL = cx-tree bl-K (Good-F θ p) w₀-self
          ; hΩ = pth (≺⊑ Ω≺ψ₁ ψ₁⊑ψ)
          }
      ; b0 = λ ()
      }
      where
      pth : toLv ΩK ≺ᴬ toLv w₀ → toLv ΩK ≺ᴬ suc (toLv w₀)
      pth (viaᴬ q d e) = viaᴬ (inj₂ q) d e
```

## §5 塔

```agda
Choice : Set₁
Choice = ∀ k (t : Twr (suc k)) → WorldK (suc k) (proj₁ t)

tower : WorldK 0 St₀ → Choice → ∀ K → Twr K
tower W₀ ch zero = St₀ , isK₀ , (λ _ ()) , (λ _ ())
tower W₀ ch (suc zero) = Step.next 0 St₀ isK₀ (λ _ ()) (λ _ ()) W₀
tower W₀ ch (suc (suc k)) =
  let t = tower W₀ ch (suc k)
  in Step.next (suc k) (proj₁ t) (proj₁ (proj₂ t)) (proj₁ (proj₂ (proj₂ t))) (proj₂ (proj₂ (proj₂ t))) (ch k t)

canon : Sib → Choice
canon S k t = Worlds.W-Ω S k (proj₁ t) (proj₁ (proj₂ t))
```
