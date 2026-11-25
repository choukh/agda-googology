# YiXVLiteralTri
> 验收文件。档位：编译定理。同一 Strong 上界内，现有比较器的代表给原下标的字面前驱或等式。
> 按 YiLSRead.St≺/st-dn/lt≺ 与 Level.sim/<ᴵ-dec 的现有计算证明；未交可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVLiteralTri where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import OCF.BTBO using (module Trich; injᵃ; injᵇ; injᶜ)
import OCF.Align.Level as L
import OCF.Lean.YiLSTw1 as T
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiXVLiteralSim as M
open import OCF.Lean.YiXVLvlSteps using (Strong; read-strong)

Exact : ∀ {a b} → (a L.≺ᴵ b ⊎ b L.≺ᴵ a ⊎ a L.≅ᴵ b) → Set
Exact (injᵃ p) = M.Literal p
Exact (injᵇ q) = M.Literal q
Exact {a} {b} (injᶜ e) = a ≡ b
left : ∀ {a a′ b} (e : a L.≅ᴵ a′) → a ≡ a′ → (p : a′ L.≺ᴵ b) → M.Literal p → M.Literal (L.≺ᴵ-respˡ e p)
left e h (L.via f r) hp = trans h hp
right : ∀ {a b b′} (p : a L.≺ᴵ b) (e : b L.≅ᴵ b′) → b ≡ b′ → M.Literal p → M.Literal (L.≺ᴵ-respʳ p e)
right (L.via f r) e h hp with L.<-≅ r e | M.moved r e h
... | L.via g s | hs = trans hp hs
steps : ∀ {f : ℕ → L.Ordᴵ} (s : ∀ n → f n L.⊑ᴵ f (suc n)) → (∀ n → M.LitSim (s n)) →
  ∀ {n m} (p : n Trich.< m) → M.LitSim (L.steps s p)
steps s h Trich.zero = h _
steps s h (Trich.suc p) = M.composition (L.steps s p) (s _) (steps s h p) (h _)

tri : ∀ {a b c} → Strong c → (p : a L.<ᴵ c) (q : b L.<ᴵ c) → Exact (L.<ᴵ-dec p q)
tri {c = L.suc c} sc L.zero L.zero = refl
tri {c = L.suc c} sc L.zero (L.suc q) = refl
tri {c = L.suc c} sc (L.suc p) L.zero = refl
tri {c = L.suc c} sc (L.suc p) (L.suc q) = tri sc p q
tri {c = L.lim f s} sc (L.lim n p) (L.lim m q) with Trich.<-dec n m
... | injᵃ lt with L.sim (L.steps s lt) p | steps s (proj₂ sc) lt p
...   | L.via e p′ | he with L.<ᴵ-dec p′ q | tri (proj₁ sc m) p′ q
...     | injᵃ r | hr = left e he r hr
...     | injᵇ r | hr = right r (L.≅ᴵ-sym e) (sym he) hr
...     | injᶜ r | hr = trans he hr
tri {c = L.lim f s} sc (L.lim n p) (L.lim m q) | injᵇ lt with L.sim (L.steps s lt) q | steps s (proj₂ sc) lt q
...   | L.via e q′ | he with L.<ᴵ-dec p q′ | tri (proj₁ sc n) p q′
...     | injᵃ r | hr = right r (L.≅ᴵ-sym e) (sym he) hr
...     | injᵇ r | hr = left e he r hr
...     | injᶜ r | hr = trans hr (sym he)
tri {c = L.lim f s} sc (L.lim n p) (L.lim m q) | injᶜ refl = tri (proj₁ sc n) p q

readback : ∀ x {a b} (p : a L.<ᴵ T.lvl x) (q : b L.<ᴵ T.lvl x) → Exact (L.<ᴵ-dec p q)
readback x p q = tri (read-strong x) p q

open import Relation.Binary.PropositionalEquality using (subst)
data Decision (a b : L.Ordᴵ) : Set where
  below : a L.<ᴵ b → Decision a b
  above : b L.<ᴵ a → Decision a b
  equal : a ≡ b → Decision a b
decide : ∀ {a b c} → Strong c → a L.<ᴵ c → b L.<ᴵ c → Decision a b
decide sc p q with L.<ᴵ-dec p q | tri sc p q
... | injᵃ (L.via e r) | same = below (subst (λ a → a L.<ᴵ _) (sym same) r)
... | injᵇ (L.via e r) | same = above (subst (λ a → a L.<ᴵ _) (sym same) r)
... | injᶜ e | same = equal same
actual : Exact (L.<ᴵ-dec (L.zero {a = T.lvl (S.suc S.zero)}) (L.suc L.zero))
actual = readback (S.suc (S.suc S.zero)) L.zero (L.suc L.zero)
```
