# 高度抽象: 实例 ω+ω, ∞ 作节点高度

> **判决: HOLDS (实例闭合).** 结论写在 [LadderInf](LadderInf.lagda.md). 高度是 `fin n` ($n<\omega$) 与 `top n` ($\omega+n$). `top 0` 就是 [LadderInfTop](LadderInfTop.lagda.md) 的 ∞, 链行; `top (n+1)` 是闭包行, 节点高度可以是 `top n`. 所以 `top 1` 的第 0 行是 $\sup_\eta \iota_\downarrow(\dot\Omega_{\infty}\,\eta)$, 读作 $\Omega_{\psi_1(1)+\Omega}$ (判断, 没有标签). 字段全部成立, 没有假设; 闭包定理不用改一行.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderInfTop2 where

open import Agda.Primitive using (Level)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.LadderInfBase
open import OCF.Align.LadderNFTree using (_<ᴸ_; zero; suc; dn; z<s; s<s) renaming (tr< to trℕ)
import OCF.Align.LadderNFTree as NF

data H : Set where
  fin : ℕ → H
  top : ℕ → H

infix 4 _<₂_
data _<₂_ : H → H → Set where
  fin : ∀ {n m} → n <ᴸ m → fin n <₂ fin m
  sw  : ∀ n m → fin n <₂ top m
  top : ∀ {n m} → n <ᴸ m → top n <₂ top m

tr₂ : ∀ {a b c} → a <₂ b → b <₂ c → a <₂ c
tr₂ (fin x) (fin y) = fin (trℕ x y)
tr₂ (fin {n} x) (sw _ m) = sw n m
tr₂ (sw n _) (top {m = m} y) = sw n m
tr₂ (top x) (top y) = top (trℕ x y)

irrℕ : ∀ {m} → m <ᴸ m → ⊥
irrℕ {suc m} q = irrℕ (dn q)

irr₂ : ∀ {m} → m <₂ m → ⊥
irr₂ (fin q) = irrℕ q
irr₂ (top q) = irrℕ q

tri₂ : ∀ a b → Tri _<₂_ a b
tri₂ (fin a) (fin b) with NF.tri a b
... | NF.tlt p = tlt (fin p)
... | NF.teq refl = teq refl
... | NF.tgt p = tgt (fin p)
tri₂ (fin a) (top b) = tlt (sw a b)
tri₂ (top a) (fin b) = tgt (sw b a)
tri₂ (top a) (top b) with NF.tri a b
... | NF.tlt p = tlt (top p)
... | NF.teq refl = teq refl
... | NF.tgt p = tgt (top p)

bot₂ : ∀ i → (fin 0 ≡ i) ⊎ (fin 0 <₂ i)
bot₂ (fin zero) = inj₁ refl
bot₂ (fin (suc i)) = inj₂ (fin (z<s i))
bot₂ (top i) = inj₂ (sw 0 i)

recF : ∀ {ℓ : Level} (X : H → Set ℓ) (F : ∀ m → (∀ {n} → n <₂ m → X n) → X m) → ∀ m {n} → n <₂ fin m → X n
recF X F (suc m) (fin zero)    = F (fin m) (recF X F m)
recF X F (suc m) (fin (suc q)) = recF X F m (fin q)

recT : ∀ {ℓ : Level} (X : H → Set ℓ) (F : ∀ m → (∀ {n} → n <₂ m → X n) → X m) → ∀ m {n} → n <₂ top m → X n
recT X F m (sw n _) = F (fin n) (recF X F n)
recT X F (suc m) (top zero)    = F (top m) (recT X F m)
recT X F (suc m) (top (suc q)) = recT X F m (top q)

rec₂ : ∀ {ℓ : Level} (X : H → Set ℓ) (F : ∀ m → (∀ {n} → n <₂ m → X n) → X m) → ∀ m {n} → n <₂ m → X n
rec₂ X F (fin m) q = recF X F m q
rec₂ X F (top m) q = recT X F m q

recF-β : ∀ {ℓ : Level} (X : H → Set ℓ) (F : ∀ m → (∀ {n} → n <₂ m → X n) → X m) → ∀ m {n} (q : n <₂ fin m) → recF X F m q ≡ F n (rec₂ X F n)
recF-β X F (suc m) (fin zero)    = refl
recF-β X F (suc m) (fin (suc q)) = recF-β X F m (fin q)

recT-β : ∀ {ℓ : Level} (X : H → Set ℓ) (F : ∀ m → (∀ {n} → n <₂ m → X n) → X m) → ∀ m {n} (q : n <₂ top m) → recT X F m q ≡ F n (rec₂ X F n)
recT-β X F m (sw n _) = refl
recT-β X F (suc m) (top zero)    = refl
recT-β X F (suc m) (top (suc q)) = recT-β X F m (top q)

rec₂-β : ∀ {ℓ : Level} (X : H → Set ℓ) (F : ∀ m → (∀ {n} → n <₂ m → X n) → X m) → ∀ m {n} (q : n <₂ m) → rec₂ X F m q ≡ F n (rec₂ X F n)
rec₂-β X F (fin m) q = recF-β X F m q
rec₂-β X F (top m) q = recT-β X F m q

view₂ : ∀ m → View _<₂_ (fin 0) m
view₂ (fin zero)    = base
view₂ (fin (suc m)) = clos (fin zero)
view₂ (top zero)    = chain fin (λ i → sw i 0)
view₂ (top (suc m)) = clos (top zero)

assocℕ : ∀ {a b c d} (x : a <ᴸ b) (y : b <ᴸ c) (z : c <ᴸ d) → trℕ (trℕ x y) z ≡ trℕ x (trℕ y z)
assocℕ x y zero    = refl
assocℕ x y (suc z) = cong suc (assocℕ x y z)

assoc₂ : ∀ {a b c d} (x : a <₂ b) (y : b <₂ c) (z : c <₂ d) → tr₂ (tr₂ x y) z ≡ tr₂ x (tr₂ y z)
assoc₂ (fin x) (fin y) (fin z) = cong fin (assocℕ x y z)
assoc₂ (fin x) (fin y) (sw _ _) = refl
assoc₂ (fin x) (sw _ _) (top z) = refl
assoc₂ (sw _ _) (top y) (top z) = refl
assoc₂ (top x) (top y) (top z) = cong top (assocℕ x y z)

step₂ : ∀ {m F} {qs : ∀ i → F i <₂ m} → view₂ m ≡ chain F qs → ∀ i →
        Σ (F i <₂ F (suc i)) λ r → (view₂ (F (suc i)) ≡ clos r) × (qs i ≡ tr₂ r (qs (suc i)))
step₂ {m = fin zero} ()
step₂ {m = fin (suc m)} ()
step₂ {m = top zero} refl i = fin zero , refl , refl
step₂ {m = top (suc m)} ()

HS₂ : HtS
HS₂ = record
  { Ht = H
  ; _<ᴸ_ = _<₂_
  ; h₀ = fin 0
  ; tr< = tr₂
  ; irr = irr₂
  ; no< = λ { (fin ()) }
  ; bot = bot₂
  ; tri = tri₂
  ; Rec = rec₂
  ; Rec-β = rec₂-β
  ; view = view₂
  ; tr-assoc = assoc₂
  ; view-step = step₂
  }
```
