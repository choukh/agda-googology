# 第一个 `Ψ⁰-mono` 够不到的层号: $\omega+1$ 的累加形状

> 接 [BTBOValLe](BTBOValLe.lagda.md). 层号 $\mathrm{suc}\,\omega_D$ ($\omega_D=$ `τ (ordᴰ ω)`, 基本列 $0,2,5,9,\dots$) 与 $\mathrm{suc}\,\omega$ 的前驱都是自然数加顶. 它们不 $\sqsubseteq^\mathsf{I}$ 相关 (`¬⊑₁`, `¬⊑₂`), 所以 `Ψ⁰-mono` 不适用; 但保序嵌入显然有, 所以折叠值相等 (`ω+1≈`). 落回 src: `x-ω+1`.
>
> 这是累加层号越过极限点之后, 值相等的第一个实例. 证明里最后的 `Laws` 就是有限数上的恒等.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOValLeInst where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≤⇒≤′; m≤m+n; m≤n⇒m≤1+n)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich; module Trich)
module S = Ord-Ord
module B = BoundedTrich
open B using (cumsum)
open S using (ordᴰ)
open import OCF.Align.Level
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOValDn using (τ; τ-<; <→⊑ᴵ)
open import OCF.Align.BTBOValMain using (ψ₀≈; cum-K; K; τ-nat; nat<)
open import OCF.Align.BTBOValAbsorb using (seq₀)
open import OCF.Align.BTBOValLe using (module LeE; cl0)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans)
```

## §1 "有限数加一个顶" 的嵌入

`A = lim h t`, 各项有限; `A′` 的前驱含一切自然数. $E$: 同一个自然数相关; $A$ 与 $A'$ 相关.

```agda
nat-pred : ∀ {c m} → c <ᴵ natᴵ m → Σ ℕ (λ j → c ≅ᴵ natᴵ j)
nat-pred {m = suc m} zero    = m , ≅ᴵ-refl _
nat-pred {m = suc m} (suc q) = nat-pred q

⊑-≅ʳ : ∀ {a b c} → a ⊑ᴵ b → b ≅ᴵ c → a ⊑ᴵ c
⊑-≅ʳ z⊑ e′ = z⊑
⊑-≅ʳ (s⊑ e q) e′ with <-≅ q e′
... | via e″ q′ = s⊑ (≅ᴵ-trans e e″) q′
⊑-≅ʳ (l⊑ k) e′ = l⊑ (λ n → ⊑-≅ʳ (k n) e′)

module Ex {h : ℕ → Ordᴵ} {t : ∀ n → h n ⊑ᴵ h (suc n)} {A′ : Ordᴵ}
          (nA′ : ∀ k → natᴵ k ≺ᴵ A′) (sq : ∀ n → Σ ℕ (λ k → h n ≅ᴵ natᴵ k)) where

  A : Ordᴵ
  A = lim h t

  data E : Ordᴵ → Ordᴵ → Set where
    eN : ∀ {a a′} k → a ≅ᴵ natᴵ k → a′ ≅ᴵ natᴵ k → E a a′
    eT : ∀ {a a′} → a ≅ᴵ A → a′ ≅ᴵ A′ → E a a′

  E-resp : ∀ {a b a′ b′} → E a b → a ≅ᴵ a′ → b ≅ᴵ b′ → E a′ b′
  E-resp (eN k e e′) d d′ = eN k (≅ᴵ-trans (≅ᴵ-sym d) e) (≅ᴵ-trans (≅ᴵ-sym d′) e′)
  E-resp (eT e e′)   d d′ = eT (≅ᴵ-trans (≅ᴵ-sym d) e) (≅ᴵ-trans (≅ᴵ-sym d′) e′)

  open LeE E E-resp

  A≇nat : ∀ {j} → ¬ (A ≅ᴵ natᴵ j)
  A≇nat {j = zero}  ()
  A≇nat {j = suc j} ()

  ¬A≺nat : ∀ {m} → ¬ (A ≺ᴵ natᴵ m)
  ¬A≺nat (via e q) with nat-pred q
  ... | j , d = A≇nat (≅ᴵ-trans e d)

  nat⊑ : ∀ j → natᴵ j ⊑ᴵ A′
  nat⊑ zero    = z⊑
  nat⊑ (suc j) = s⊑′ (nA′ j)

  ℒ : Laws
  ℒ = record { lt-pres = lt′ ; eq-pres = eq′ ; suc⁻ = suc′ ; lim⁻ = lim′ }
    where
    lt′ : ∀ {a a′ b b′} → E a a′ → E b b′ → a ≺ᴵ b → a′ ≺ᴵ b′
    lt′ (eN k e e′) (eN m d d′) r = ≺ᴵ-respˡ e′ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym e) (≺ᴵ-respʳ r d)) (≅ᴵ-sym d′))
    lt′ (eN k e e′) (eT d d′)   r = ≺ᴵ-respˡ e′ (≺ᴵ-respʳ (nA′ k) (≅ᴵ-sym d′))
    lt′ (eT e e′)   (eN m d d′) r = ⊥-elim (¬A≺nat (≺ᴵ-respˡ (≅ᴵ-sym e) (≺ᴵ-respʳ r d)))
    lt′ (eT e e′)   (eT d d′)   r = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym e) (≺ᴵ-respʳ r d)))

    eq′ : ∀ {a a′ b b′} → E a a′ → E b b′ → a ≅ᴵ b → a′ ≅ᴵ b′
    eq′ (eN k e e′) (eN m d d′) r = ≅ᴵ-trans e′ (≅ᴵ-trans (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-trans r d)) (≅ᴵ-sym d′))
    eq′ (eN k e e′) (eT d d′)   r = ⊥-elim (A≇nat (≅ᴵ-trans (≅ᴵ-sym d) (≅ᴵ-trans (≅ᴵ-sym r) e)))
    eq′ (eT e e′)   (eN m d d′) r = ⊥-elim (A≇nat (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-trans r d)))
    eq′ (eT e e′)   (eT d d′)   r = ≅ᴵ-trans e′ (≅ᴵ-sym d′)

    suc′ : ∀ {c a′} → E (suc c) a′ → Σ Ordᴵ (λ c′ → E c c′ × c′ ≺ᴵ a′)
    suc′ (eN (suc j) (s≅ e) e′) = natᴵ j , eN j e (≅ᴵ-refl _) , ≺ᴵ-respʳ (via (≅ᴵ-refl _) zero) (≅ᴵ-sym e′)
    suc′ (eT () e′)

    lim′ : ∀ {f s a′} → E (lim f s) a′ → ∀ n → Σ Ordᴵ (λ b′ → E (f n) b′ × b′ ⊑ᴵ a′)
    lim′ (eN zero () e′)
    lim′ (eN (suc k) () e′)
    lim′ (eT (l≅ k₀) e′) n with sq n
    ... | j , d = natᴵ j , eN j (≅ᴵ-trans (k₀ n) d) (≅ᴵ-refl _) , ⊑-≅ʳ (nat⊑ j) (≅ᴵ-sym e′)

  open WithLaws ℒ

  top : ψ⁰ (Ω (suc A)) ≼ ψ⁰ (Ω (suc A′))
  top = Le-ψ⁰ (walk (suc A′) (≅ᴵ-refl _) (eT (≅ᴵ-refl A) (≅ᴵ-refl A′)) zero)
```

## §2 实例

```agda
g₀ : ℕ → S.Ord₀
g₀ = seq₀ S.ω

ω-e : ∀ n → τ (cumsum (ordᴰ ∘ g₀) n) ≡ natᴵ (K n)
ω-e n = trans (cong τ (cum-K g₀ refl (λ _ → refl) n)) (τ-nat (K n))

ωᴰ : Ordᴵ
ωᴰ = τ (ordᴰ S.ω)

nat≺ωᴵ : ∀ k → natᴵ k ≺ᴵ ωᴵ
nat≺ωᴵ k = via (≅ᴵ-refl _) (lim (suc k) zero)

nat≺ωᴰ : ∀ k → natᴵ k ≺ᴵ ωᴰ
nat≺ωᴰ k = via (≅ᴵ-refl _) (lim (suc k) (subst (natᴵ k <ᴵ_) (sym (ω-e (suc k))) (nat< (≤⇒≤′ (m≤n⇒m≤1+n (m≤m+n k (K k)))))))

module D₁ = Ex {h = τ ∘ cumsum (ordᴰ ∘ g₀)} {t = λ n → <→⊑ᴵ (τ-< (B.cumsum-mono (ordᴰ ∘ g₀) Trich.zero))} {A′ = ωᴵ} nat≺ωᴵ (λ n → K n , subst (_≅ᴵ natᴵ (K n)) (sym (ω-e n)) (≅ᴵ-refl _))
module D₂ = Ex {h = natᴵ} {t = natᴵ-step} {A′ = ωᴰ} nat≺ωᴰ (λ n → n , ≅ᴵ-refl _)

ω+1≈ : ψ⁰ (Ω (suc ωᴰ)) ≈ᵛ ψ⁰ (Ω (suc ωᴵ))
ω+1≈ = D₁.top , D₂.top

x-ω+1 : tr₀ (S.ψ₀ (S.Ω (B.suc (ordᴰ S.ω)))) ≈ᵛ ψ⁰ (Ω (suc ωᴵ))
x-ω+1 = ≼-trans (proj₁ (ψ₀≈ (B.suc (ordᴰ S.ω)))) (proj₁ ω+1≈) , ≼-trans (proj₂ ω+1≈) (proj₂ (ψ₀≈ (B.suc (ordᴰ S.ω))))
```

## §3 `Ψ⁰-mono` 不适用

两个方向的 $\sqsubseteq^\mathsf{I}$ 都不成立. 第 1 项 $2$ 对 $1$, 而自然数前驱都不是极限.

```agda
ωᴰ≇ωᴵ : ¬ (ωᴰ ≅ᴵ ωᴵ)
ωᴰ≇ωᴵ (l≅ h) with h 1
... | s≅ ()

lim≇nat : ∀ {f s j} → ¬ (lim f s ≅ᴵ natᴵ j)
lim≇nat {j = zero}  ()
lim≇nat {j = suc j} ()

¬⊑₁ : ¬ (suc ωᴰ ⊑ᴵ suc ωᴵ)
¬⊑₁ (s⊑ e zero) = ωᴰ≇ωᴵ e
¬⊑₁ (s⊑ e (suc (lim n q))) with nat-pred q
... | j , d = lim≇nat (≅ᴵ-trans e d)

¬⊑₂ : ¬ (suc ωᴵ ⊑ᴵ suc ωᴰ)
¬⊑₂ (s⊑ e zero) = ωᴰ≇ωᴵ (≅ᴵ-sym e)
¬⊑₂ (s⊑ e (suc (lim n q))) with nat-pred (subst (_ <ᴵ_) (ω-e n) q)
... | j , d = lim≇nat (≅ᴵ-trans e d)
```
