# YiXVFiniteCoerce
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteCoerce where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I

into-out : ∀ {i ℓ} (r : i L.◃ ℓ) (u : L.U i r) → L.into r (L.out r u) ≡ u
into-out L.zero u = refl
into-out (L.suc r) u = into-out r u
into-out (L.self n) u = refl
into-out (L.lim n r) u = into-out r u

coe-id : ∀ {i ℓ} (q : i L.<ᴵ ℓ) (u : L.U i (L.<→◃ q)) → L.coe (L.<→◃ q) (L.<→◃ q) u ≡ u
coe-id q u = into-out (L.<→◃ q) u

start : ∀ {i ℓ} (q : i L.<ᴵ ℓ) → L.U i (L.<→◃ q)
start {i} q = L.into (L.<→◃ q) (L.Ω i)
next : ∀ {i ℓ} (q : i L.<ᴵ ℓ) → L.U i (L.<→◃ q) → L.U i (L.<→◃ q)
next q u = L.into (L.<→◃ q) (L.suc (L.out (L.<→◃ q) u))
coe-start : ∀ {i a b} (p : i L.<ᴵ a) (q : i L.<ᴵ b) → L.coe (L.<→◃ p) (L.<→◃ q) (start p) ≡ start q
coe-start {i} p q = cong (L.into (L.<→◃ q)) (L.out-into (L.<→◃ p) (L.Ω i))
coe-next : ∀ {i a b} (p : i L.<ᴵ a) (q : i L.<ᴵ b) (u : L.U i (L.<→◃ p)) →
  L.coe (L.<→◃ p) (L.<→◃ q) (next p u) ≡ next q (L.coe (L.<→◃ p) (L.<→◃ q) u)
coe-next p q u = trans
  (cong (L.into (L.<→◃ q)) (L.out-into (L.<→◃ p) (L.suc (L.out (L.<→◃ p) u))))
  (sym (cong (λ v → L.into (L.<→◃ q) (L.suc v)) (L.out-into (L.<→◃ q) (L.out (L.<→◃ p) u))))

res-self : ∀ n {i} (q : i L.<ᴵ L.natᴵ n) →
  L.res q (L.≅ᴵ-refl (L.natᴵ n)) ≡ L.restr (L.≅ᴵ-refl i) q (L.tr⁻ (L.≅ᴵ-refl i))
res-self zero ()
res-self (suc n) L.zero = refl
res-self (suc n) (L.suc q) rewrite res-self n q = refl
res⁻-self : ∀ n {i} (q : i L.<ᴵ L.natᴵ n) →
  L.res⁻ q (L.≅ᴵ-refl (L.natᴵ n)) ≡ L.restr (L.≅ᴵ-sym (L.≅ᴵ-refl i)) q (L.tr (L.≅ᴵ-refl i))
res⁻-self zero ()
res⁻-self (suc n) L.zero = refl
res⁻-self (suc n) (L.suc q) rewrite res⁻-self n q = refl

cast-Ω : ∀ {i k} (e : i ≡ L.natᴵ k) → subst L.Ordᶜ e (L.Ω i) ≡ L.Ω (L.natᴵ k)
cast-Ω refl = refl
cast-tr : ∀ {i k} (e : i ≡ L.natᴵ k) (x : L.Ordᶜ i) →
  subst L.Ordᶜ e (L.tr (L.≅ᴵ-refl i) x) ≡ L.tr (L.≅ᴵ-refl (L.natᴵ k)) (subst L.Ordᶜ e x)
cast-tr refl x = refl
cast-tr⁻ : ∀ {i k} (e : i ≡ L.natᴵ k) (x : L.Ordᶜ i) →
  subst L.Ordᶜ e (L.tr⁻ (L.≅ᴵ-refl i) x) ≡ L.tr⁻ (L.≅ᴵ-refl (L.natᴵ k)) (subst L.Ordᶜ e x)
cast-tr⁻ refl x = refl
```
