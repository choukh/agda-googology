# 分层的 $\approx$: 阶段序列的并 (底座)

> 底座, 不含记号. 结论写在 [LvStrat](LvStrat.lagda.md). 任何一列用 `Ext` 接起来的阶段都可以取并: 低层是某一阶段的低层, 地板元是某一阶段的地板元. 地板对读它的阶段无关, 这正是 `Ext` 说的. [LevelKOmega](LevelKOmega.lagda.md) 的 `Union` 只对自然数的塔; 这里没有对阶段分情况, 所以 $\Omega+n$ 的塔也能用.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvStratUnion where

open import Data.Nat using (ℕ; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-total; +-identityʳ; +-suc)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.InaccTreeBase using (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; toLv; Tree; Ω)
open import OCF.Align.LvStratBase using (AdmOf; LoOf; tr; Fl; module Leaf; Stage; Ext; module Move)

Ext∘ : ∀ {F G H} → Ext F G → Ext G H → Ext F H
Ext∘ X Y = record
  { low⊂ = λ l → Ext.low⊂ Y (Ext.low⊂ X l)
  ; A⊂ = λ a → Ext.A⊂ Y (Ext.A⊂ X a)
  ; A⊃ = λ l a → Ext.A⊃ X l (Ext.A⊃ Y (Ext.low⊂ X l) a)
  }

Ext-id : ∀ {F} → Ext F F
Ext-id = record { low⊂ = λ l → l ; A⊂ = λ a → a ; A⊃ = λ _ a → a }

le-add : ∀ {m n} → m ≤ n → Σ ℕ λ d → n ≡ d + m
le-add {n = n} z≤n = n , sym (+-identityʳ n)
le-add {m = ℕ.suc m} (s≤s p) with le-add p
... | d , refl = d , sym (+-suc d m)

module UnionG (Sᴷ : ℕ → Stage) (ext-suc : ∀ K → Ext (Stage.fl (Sᴷ K)) (Stage.fl (Sᴷ (ℕ.suc K)))) where
  Flᴷ : ℕ → Fl
  Flᴷ K = Stage.fl (Sᴷ K)

  Lwᴷ : ℕ → Lv → Set
  Lwᴷ K = Fl.Lw (Flᴷ K)

  Aᴷ : ℕ → (j : Lv) → Ordᴸ j → Set
  Aᴷ K = Fl.A (Flᴷ K)

  ext-add : ∀ d K → Ext (Flᴷ K) (Flᴷ (d + K))
  ext-add ℕ.zero    K = Ext-id
  ext-add (ℕ.suc d) K = Ext∘ (ext-add d K) (ext-suc (d + K))

  ext≤ : ∀ {m n} → m ≤ n → Ext (Flᴷ m) (Flᴷ n)
  ext≤ {m} {n} p with le-add p
  ... | d , refl = ext-add d m

  Lw∞ : Lv → Set
  Lw∞ j = Σ ℕ λ K → Lwᴷ K j

  A∞ : (j : Lv) → Ordᴸ j → Set
  A∞ j x = Σ ℕ λ K → Aᴷ K j x

  A⊃∞ : ∀ {n j x} → Lwᴷ n j → A∞ j x → Aᴷ n j x
  A⊃∞ {n} l (m , a) with ≤-total m n
  ... | inj₁ p = Ext.A⊂ (ext≤ p) a
  ... | inj₂ p = Ext.A⊃ (ext≤ p) l a

  adm∞↓ : ∀ n c → Fl.Lo (Flᴷ n) c → ∀ r → AdmOf A∞ c r → AdmOf (Aᴷ n) c r
  adm∞↓ n (suc k)    l (inj₁ _)        d = tt
  adm∞↓ n (suc k)    l (inj₂ r)        d = adm∞↓ n k l r d
  adm∞↓ n (lim f)    l (m , r)         d = adm∞↓ n (f m) (l m) r d
  adm∞↓ n (limᴼ k g) l (inj₁ (inj₁ _)) d = tt
  adm∞↓ n (limᴼ k g) l (inj₁ (inj₂ r)) d = adm∞↓ n k (Fl.low-lo (Flᴷ n) k (proj₁ l)) r d
  adm∞↓ n (limᴼ k g) l (inj₂ (x , r)) (a , d) =
    let ax = A⊃∞ (proj₁ l) a in ax , adm∞↓ n (g x) (proj₂ l x ax) r d

  lo∞ : ∀ n a → Fl.Lo (Flᴷ n) a → LoOf Lw∞ A∞ a
  lo∞ n zero       l = tt
  lo∞ n (suc k)    l = lo∞ n k l
  lo∞ n (lim f)    l = λ m → lo∞ n (f m) (l m)
  lo∞ n (limᴼ k g) (lk , lg) = (n , lk) , (λ x a → lo∞ n (g x) (lg x (A⊃∞ lk a)))

  fl∞ : Fl
  fl∞ = record
    { Lw = Lw∞
    ; A = A∞
    ; A→Lw = λ { k x (m , a) → m , Fl.A→Lw (Flᴷ m) k x a }
    ; low-at = λ { j (n , l) r d → n , Fl.low-at (Flᴷ n) j l r (adm∞↓ n j (Fl.low-lo (Flᴷ n) j l) r d) }
    ; low-lo = λ { j (n , l) → lo∞ n j (Fl.low-lo (Flᴷ n) j l) }
    }

  ext∞ : ∀ n → Ext (Flᴷ n) fl∞
  ext∞ n = record { low⊂ = λ l → n , l ; A⊂ = λ a → n , a ; A⊃ = A⊃∞ }

  loAᴷ : ∀ n {j x} → Aᴷ n j x → Fl.Lo (Flᴷ n) (toLv x)
  loAᴷ n {j} {x} a = Fl.lo-toLv (Flᴷ n) (Fl.lw→bl (Flᴷ n) (Fl.A→Lw (Flᴷ n) j x a)) x (Stage.twA (Sᴷ n) j x a)

  module M∞ (n : ℕ) = Move (Flᴷ n) fl∞ (ext∞ n) (Stage.low≈ (Sᴷ n)) (loAᴷ n)
  open Leaf fl∞

  St∞ : Stage
  St∞ = record
    { fl = fl∞
    ; low≈ = λ { (n , l) e → n , Stage.low≈ (Sᴷ n) l (M∞.≈↓ n (Fl.low-lo (Flᴷ n) _ l) e) }
    ; tr-A = λ { {j} {j′} (n , l) e z a →
        let e₀ = M∞.≈↓ n (Fl.low-lo (Flᴷ n) j l) e
            i  = Stage.tr-A (Sᴷ n) l e₀ z (A⊃∞ l a)
        in (n , proj₁ i) , M∞.≈↑ n (proj₂ i) }
    ; low-cx = λ { j (n , l) → M∞.Cx↑ n j (Fl.low-lo (Flᴷ n) j l) (Stage.low-cx (Sᴷ n) j l) }
    ; ΩA = λ { j (n , l) → n , Stage.ΩA (Sᴷ n) j l }
    ; pΩ = λ { j (n , l) → M∞.≺↑ n (Stage.pΩ (Sᴷ n) j l) }
    ; cmpA = cmp∞
    ; cxA = λ { j x (m , a) → M∞.Cx↑ m (toLv x) (loAᴷ m a) (Stage.cxA (Sᴷ m) j x a) }
    ; twA = λ { j x (m , a) → M∞.tw↑ m j (Fl.lw→bl (Flᴷ m) (Fl.A→Lw (Flᴷ m) j x a)) x (Stage.twA (Sᴷ m) j x a) }
    }
    where
    cmp∞ : ∀ j x y → A∞ j x → A∞ j y → Tri (toLv x) (toLv y)
    cmp∞ j x y (m , a) b =
      M∞.Tri↑ m (Stage.cmpA (Sᴷ m) j x y a (A⊃∞ (Fl.A→Lw (Flᴷ m) j x a) b))
```
