# 字面上界: 编译的否定

> 不含记号. 结论写在 [InaccFloor](InaccFloor.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccFloorNeg where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-cancelʳ-≡)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.InaccTreeBase hiding (_⊑_; _≺_; via; up; ι; res; tr; _+_)
open import OCF.Align.InaccStrikeBase using (Funext)
open import OCF.Align.InaccModulusBase using (Reg; W; ws0)
open import OCF.Align.InaccSingularBase using (WLPO; bump; bump-false; bump-true)
open import OCF.Align.Level using (Ordᴵ; _<ᴵ_; natᴵ; natᴵ-step; ωᴵ; zero; suc; lim)
open import OCF.Align.InaccFloorBase
```

## §1 规整性不是分支的证据

把可容许集取成 "规整的树" (`Reg` 的全体): 证书假. 这与 `dir-dec` 不矛盾: `dir-dec` 要的是**同一个**规整上界. 所以 `Reg` 是树内的证据, 不是分支集.

```agda
nt : ℕ → Ordᴸ zero
nt zero    = zero
nt (suc n) = suc (nt n)

ω₀ ω₁ : Ordᴸ zero
ω₀ = lim nt
ω₁ = lim (λ n → nt (suc n))

Aᴿ : (k : Lv) → Ordᴸ k → Set
Aᴿ zero       x = Reg (toLv x)
Aᴿ (suc _)    _ = ⊥
Aᴿ (lim _)    _ = ⊥
Aᴿ (limᴼ _ _) _ = ⊥

Reg-nt : ∀ n → Reg (toLv (nt n))
Reg-nt zero    = tt
Reg-nt (suc n) = Reg-nt n

at-nt : ∀ n (r : Pre (toLv (nt n))) → Σ ℕ λ m → at (toLv (nt n)) r ≡ toLv (nt m)
at-nt (suc n) (inj₁ _) = n , refl
at-nt (suc n) (inj₂ r) = at-nt n r

lim≉ : ∀ {f} m → lim f ≈ toLv (nt m) → ⊥
lim≉ zero ()
lim≉ (suc m) ()

lim≉′ : ∀ {f} {c} m → c ≡ toLv (nt m) → lim f ≈ c → ⊥
lim≉′ m refl e = lim≉ m e

¬WF-Reg : Rel.WFᴬ Aᴿ (limᴼ zero toLv) → ⊥
¬WF-Reg w with Rel.<-decᴬ Aᴿ (limᴼ zero toLv) w
                 (inj₂ (suc ω₀ , inj₁ tt)) (inj₂ (suc ω₁ , inj₁ tt))
                 ((((λ n → ws0) , Reg-nt) , tt)) (((λ n → ws0) , (λ n → Reg-nt n)) , tt)
... | injᵃ (Rel.viaᴬ (n , r) _ e) = lim≉′ (proj₁ (at-nt (suc n) r)) (proj₂ (at-nt (suc n) r)) e
... | injᵇ (Rel.viaᴬ (n , r) _ e) = lim≉′ (proj₁ (at-nt n r)) (proj₂ (at-nt n r)) e
... | injᶜ (l≈ h) with h 0
...   | ()
```

## §2 证据不能从原始的树读出

`S` 拿到的是原始的树. 如果能判定 "$x$ 是 $\ell$ 的字面前驱的像", 就有 WLPO (`dec-A→WLPO`). 这里的 $\ell=\omega+1$ 是最小的非平凡的界. **所以世界 $\ell$ 的证据必须由树带着, 不能在折叠时测出来.**

```agda
τ : (ℕ → Bool) → Ordᴸ zero
τ s = lim (λ n → em (natᴵ (bump s n + n)))

em-nat-inj : ∀ a b → em (natᴵ a) ≡ em (natᴵ b) → a ≡ b
em-nat-inj zero    zero    _ = refl
em-nat-inj (suc a) (suc b) e = cong suc (em-nat-inj a b (suc-inj e)) where
  suc-inj : ∀ {x y : Ordᴸ zero} → Tree.suc x ≡ Tree.suc y → x ≡ y
  suc-inj refl = refl

lim-inj : ∀ {f g : ℕ → Ordᴸ zero} → Tree.lim f ≡ Tree.lim g → ∀ n → f n ≡ g n
lim-inj refl n = refl

ω≡τ : Funext → ∀ s → (∀ n → s n ≡ false) → em ωᴵ ≡ τ s
ω≡τ fe s a = cong lim (fe (λ n → cong (λ z → em (natᴵ (z + n))) (sym (bump-false s a n))))

nl : ∀ m {f st} → lim f st <ᴵ natᴵ m → ⊥
nl zero ()
nl (suc zero) (suc ())
nl (suc (suc m)) (suc q) = nl (suc m) q

A→false : ∀ s → Aℓ (suc ωᴵ) zero (τ s) → ∀ n → s n ≡ false
A→false s (lim f st , zero , e) n = go (s n) refl where
  k : bump s (suc n) ≡ 0
  k = +-cancelʳ-≡ (suc n) (bump s (suc n)) 0 (sym (em-nat-inj _ _ (lim-inj e (suc n))))
  go : ∀ b → s n ≡ b → b ≡ false
  go false _ = refl
  go true  q with () ← trans (sym (bump-true s n q)) k
A→false s (lim f st , suc (lim m q) , e) n = ⊥-elim (nl m q)

dec-A→WLPO : Funext → (∀ x → Dec (Aℓ (suc ωᴵ) zero x)) → WLPO
dec-A→WLPO fe d s with d (τ s)
... | yes a = inj₁ (A→false s a)
... | no ¬a = inj₂ (λ h → ¬a (ωᴵ , zero , ω≡τ fe s h))
```

## §3 世界 $\ell$ 只管第 0 层

`Aℓ` 在 $k\ne0$ 上空, 所以 $\Omega_{\Omega_2}$ 这样的层号没有证书 (`¬WF-L₂`). $\psi_1(\Omega_3)$ 的树 (`F (natL 3)`) 有定义且验收通过, 但它的输入是第 2 层的树, 节点的参数层是 1, 所以 [InaccFloorIter](InaccFloorIter.lagda.md) 的 `P̂` 与 `WFP̂` 不覆盖它. 这是证书一侧的第一个具体障碍.

```agda
module _ (ℓ : Ordᴵ) where
  open Rel (Aℓ ℓ)

  ¬WF-L₂ : WFᴬ (toLv (Ω (suc (suc zero)))) → ⊥
  ¬WF-L₂ (_ , (_ , () , _) , _)
```
