# 带切口的项: 读位置的结构证据, 对一切闭包

> 不含记号. 结论写在 [GuardRead](GuardRead.lagda.md). `Rs x`: 项 $x$ 里每个 `limᵢ` (每个闭包) 的函数 $f$ 带两条结构证据:
>
> - `Str`: $f\,z$ 是 $f(z+1)$ 的切口 ([GuardReadCut](GuardReadCut.lagda.md) 的 `Sp`), 对一切 $z\cong z$;
> - `Cont`: $f(\lim h)\cong\lim(f\circ h)$.
>
> 这是 [LvGuard](LvGuard.lagda.md) 提议的 `Str`, `Cont`, 但 `Str` 不是 "比较 $F\eta$ 与位置": 比较写不出 (`no-cut`, `no-fp-move`, [GuardReadNeg](GuardReadNeg.lagda.md)), 证据由结构给. 与 `Good` 同样分层 (`Rs₊`, `Rd`), 闭包性 `Rs-Ω`, `Rs-add`, `Rs-iter`, `Rs-ψ`, `Rs-ψ¹`, `Rs-tr`, `Rs-tr⁻` 与 `Good-*` 同形, 多两个字段.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardReadRs where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.GuardTightCum hiding (steps)
open Restr
open import OCF.Align.GuardTightLv using (Dom₀)
import OCF.Align.GuardTightUni as Uni
open Uni Dom₀ using (ψ¹; ψ¹-≅; em; em-self; chain; chain-≅; i-resp; self-tr; self-tr⁻; self-back; self-back⁻; ≅-reflˡ; ≅-reflʳ; s-inv; l-inv; u-refl)
open import OCF.Align.GuardReadCut
```

## §1 定义

```agda
module _ (ℓ : Ordᴵ) (G< : (i : Ordᴵ) (r : i ◃ ℓ) → U i r → Set) where
  data Rs₊ : Ordᶜ ℓ → Set where
    rz : Rs₊ zero
    rs : ∀ {a} → Rs₊ a → Rs₊ (suc a)
    rl : ∀ {h : ℕ → Ordᶜ ℓ} → (∀ n → Rs₊ (h n)) → Rs₊ (lim h)
    ri : ∀ {j} {p : j <ᴵ ℓ} {f : U j (<→◃ p) → Ordᶜ ℓ} →
         (∀ (z : Ordᶜ j) → z ≅ z → G< j (<→◃ p) (into (<→◃ p) z) → Rs₊ (f (into (<→◃ p) z))) →
         (∀ (z : Ordᶜ j) → z ≅ z → Sp (f (into (<→◃ p) z)) (f (into (<→◃ p) (suc z)))) →
         (∀ (h : ℕ → Ordᶜ j) → (∀ n → h n ≅ h n) → f (into (<→◃ p) (lim h)) ≅ lim (λ n → f (into (<→◃ p) (h n)))) →
         Rs₊ (limᵢ p f)
    ru : ∀ {k} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} → G< k (◃₁→◃ r) x → Rs₊ (up r x)

Rd : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → U i r → Set
Rd i zero         x = Rs₊ i Rd x
Rd i (suc r)      x = Rd i r x
Rd _ (self {f} n) x = Rs₊ (f n) Rd x
Rd i (lim n r)    x = Rd i r x

Rs : ∀ {ℓ} → Ordᶜ ℓ → Set
Rs {ℓ} = Rs₊ ℓ Rd

Rd→Rs : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordᶜ i} → Rd i r (into r x) → Rs x
Rd→Rs zero      g = g
Rd→Rs (suc r)   g = Rd→Rs r g
Rd→Rs (self n)  g = g
Rd→Rs (lim n r) g = Rd→Rs r g

Rs→Rd : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordᶜ i} → Rs x → Rd i r (into r x)
Rs→Rd zero      g = g
Rs→Rd (suc r)   g = Rs→Rd r g
Rs→Rd (self n)  g = g
Rs→Rd (lim n r) g = Rs→Rd r g

Rd-conv : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) (r′ : i ◃ ℓ′) {x : Ordᶜ i} → Rd i r (into r x) → Rd i r′ (into r′ x)
Rd-conv r r′ g = Rs→Rd r′ (Rd→Rs r g)

-- 经 into, out 的 Cont: 对 r 递归, 叶子上定义相等
cnt-oi : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) (F : Ordᶜ i → Ordᶜ ℓ′) (h : ℕ → Ordᶜ i) →
         F (lim h) ≅ lim (λ n → F (h n)) → F (out r (into r (lim h))) ≅ lim (λ n → F (out r (into r (h n))))
cnt-oi zero      F h c = c
cnt-oi (suc r)   F h c = cnt-oi r F h c
cnt-oi (self n)  F h c = c
cnt-oi (lim n r) F h c = cnt-oi r F h c

-- 经 into, out 的 Str
str-oi : ∀ {i ℓ k′ ℓ′} (r : i ◃ ℓ) (A : Ordᶜ i → Ordᶜ k′) (F : Ordᶜ i → Ordᶜ ℓ′) (z : Ordᶜ i) →
         Sp (A z) (F (suc z)) → Sp (A (out r (into r z))) (F (out r (into r (suc z))))
str-oi zero      A F z s = s
str-oi (suc r)   A F z s = str-oi r A F z s
str-oi (self n)  A F z s = s
str-oi (lim n r) A F z s = str-oi r A F z s

back-suc : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) (z : Ordᶜ (rep (res q e))) → back (res q e) (suc z) ≡ suc (back (res q e) z)
back-suc zero      (s≅ e) z = refl
back-suc (suc q)   (s≅ e) z = back-suc q e z
back-suc (lim n q) (l≅ f) z = back-suc q (f n) z

back⁻-suc : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) (z : Ordᶜ (rep (res⁻ q e))) → back (res⁻ q e) (suc z) ≡ suc (back (res⁻ q e) z)
back⁻-suc zero      (s≅ e) z = refl
back⁻-suc (suc q)   (s≅ e) z = back⁻-suc q e z
back⁻-suc (lim n q) (l≅ f) z = back⁻-suc q (f n) z

back-lim : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) (h : ℕ → Ordᶜ (rep (res q e))) → back (res q e) (lim h) ≡ lim (λ n → back (res q e) (h n))
back-lim zero      (s≅ e) h = refl
back-lim (suc q)   (s≅ e) h = back-lim q e h
back-lim (lim n q) (l≅ f) h = back-lim q (f n) h

back⁻-lim : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) (h : ℕ → Ordᶜ (rep (res⁻ q e))) → back (res⁻ q e) (lim h) ≡ lim (λ n → back (res⁻ q e) (h n))
back⁻-lim zero      (s≅ e) h = refl
back⁻-lim (suc q)   (s≅ e) h = back⁻-lim q e h
back⁻-lim (lim n q) (l≅ f) h = back⁻-lim q (f n) h
```

## §2 闭包性

```agda
Rs-tr    : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ a} → Rs x → x ≅ x → Rs (tr e x)
Rs-tr⁻   : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ b} → Rs x → x ≅ x → Rs (tr⁻ e x)
Rs-back  : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} → Rs u → u ≅ u → Rs (back (res q e) u)
Rs-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} → Rs u → u ≅ u → Rs (back (res⁻ q e) u)

Rs-tr e rz ex = rz
Rs-tr e (rs g) ex = rs (Rs-tr e g (s-inv ex))
Rs-tr e (rl hg) ex = rl (λ n → Rs-tr e (hg n) (l-inv ex n))
Rs-tr e (ri {p = q} {f = f} hb st ct) ex = ri
  (λ z ez g → oi (<→◃ (lt (res q e))) (λ w → Rs (tr e (f (into (<→◃ q) (back (res q e) w)))))
                 (Rs-tr e (hb (back (res q e) z) (self-back q e ez)
                              (Rs→Rd (<→◃ q) (Rs-back q e (Rd→Rs (<→◃ (lt (res q e))) g) ez)))
                          (i-resp ex (self-back q e ez))))
  (λ z ez → str-oi (<→◃ (lt (res q e))) (λ w → tr e (f (into (<→◃ q) (back (res q e) w)))) (λ w → tr e (f (into (<→◃ q) (back (res q e) w)))) z
              (subst (λ v → Sp (tr e (f (into (<→◃ q) (back (res q e) z)))) (tr e (f (into (<→◃ q) v)))) (sym (back-suc q e z))
                     (Sp-tr e e (i-resp ex (self-back q e ez)) (st (back (res q e) z) (self-back q e ez)))))
  (λ h he → cnt-oi (<→◃ (lt (res q e))) (λ w → tr e (f (into (<→◃ q) (back (res q e) w)))) h
              (subst (λ v → tr e (f (into (<→◃ q) v)) ≅ lim (λ n → tr e (f (into (<→◃ q) (back (res q e) (h n)))))) (sym (back-lim q e h))
                     (≅-tr e (tr-≅ e (ct (λ n → back (res q e) (h n)) (λ n → self-back q e (he n)))))))
Rs-tr (s≅ e) (ru {r = zero} g) ex = ru (Rs-tr e g (u-refl zero ex))
Rs-tr (l≅ f) (ru {r = self n} g) ex = ru (Rs-tr (f n) g (u-refl (self n) ex))

Rs-tr⁻ e rz ex = rz
Rs-tr⁻ e (rs g) ex = rs (Rs-tr⁻ e g (s-inv ex))
Rs-tr⁻ e (rl hg) ex = rl (λ n → Rs-tr⁻ e (hg n) (l-inv ex n))
Rs-tr⁻ e (ri {p = q} {f = f} hb st ct) ex = ri
  (λ z ez g → oi (<→◃ (lt (res⁻ q e))) (λ w → Rs (tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w)))))
                 (Rs-tr⁻ e (hb (back (res⁻ q e) z) (self-back⁻ q e ez)
                               (Rs→Rd (<→◃ q) (Rs-back⁻ q e (Rd→Rs (<→◃ (lt (res⁻ q e))) g) ez)))
                           (i-resp ex (self-back⁻ q e ez))))
  (λ z ez → str-oi (<→◃ (lt (res⁻ q e))) (λ w → tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w)))) (λ w → tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w)))) z
              (subst (λ v → Sp (tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) z)))) (tr⁻ e (f (into (<→◃ q) v)))) (sym (back⁻-suc q e z))
                     (Sp-tr⁻ e e (i-resp ex (self-back⁻ q e ez)) (st (back (res⁻ q e) z) (self-back⁻ q e ez)))))
  (λ h he → cnt-oi (<→◃ (lt (res⁻ q e))) (λ w → tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w)))) h
              (subst (λ v → tr⁻ e (f (into (<→◃ q) v)) ≅ lim (λ n → tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) (h n)))))) (sym (back⁻-lim q e h))
                     (≅-tr⁻ e (tr⁻-≅ e (ct (λ n → back (res⁻ q e) (h n)) (λ n → self-back⁻ q e (he n)))))))
Rs-tr⁻ (s≅ e) (ru {r = zero} g) ex = ru (Rs-tr⁻ e g (u-refl zero ex))
Rs-tr⁻ (l≅ f) (ru {r = self n} g) ex = ru (Rs-tr⁻ (f n) g (u-refl (self n) ex))

Rs-back zero      (s≅ e) g d = Rs-tr⁻ e g d
Rs-back (suc q)   (s≅ e) g d = Rs-back q e g d
Rs-back (lim n q) (l≅ f) g d = Rs-back q (f n) g d

Rs-back⁻ zero      (s≅ e) g d = Rs-tr e g d
Rs-back⁻ (suc q)   (s≅ e) g d = Rs-back⁻ q e g d
Rs-back⁻ (lim n q) (l≅ f) g d = Rs-back⁻ q (f n) g d

Rs-Ω : ∀ a → Rs (Ω a)
Rs-Ω zero      = rs rz
Rs-Ω (suc c)   = ri (λ z ez g → ru g)
                    (λ z ez → s-up (s-suc (Uni.up-l Dom₀ (Uni.≅→⊑ᵒ Dom₀ ez)) ez (s-eq (upˡ ez))))
                    (λ h he → upˡ (l≅ (λ n → upʳ (he n))))
Rs-Ω (lim g s) = rl (λ n → ru (Rs-Ω (g n)))

Rs-add : ∀ {k ℓ} {a : Ordᶜ ℓ} {σ : Simᴵ k ℓ} {b : Ordᶜ k} → Rs a → a ≅ a → Rs b → b ≅ b → Rs (add a σ b)
Rs-add ga ea rz eb = ga
Rs-add ga ea (rs g) eb = rs (Rs-add ga ea g (s-inv eb))
Rs-add ga ea (rl hg) eb = rl (λ n → Rs-add ga ea (hg n) (l-inv eb n))
Rs-add {a = a} {σ = σ} ga ea (ri {p = q} {f = f} hb st ct) eb = ri
  (λ z ez g → oi (<→◃ (σ q)) (λ u → Rs (add a σ (f (into (<→◃ q) u))))
                 (Rs-add ga ea (hb z ez (Rd-conv (<→◃ (σ q)) (<→◃ q) g)) (i-resp eb ez)))
  (λ z ez → str-oi (<→◃ (σ q)) (λ u → add a σ (f (into (<→◃ q) u))) (λ u → add a σ (f (into (<→◃ q) u))) z
              (Sp-add {σ₁ = σ} {σ₂ = σ} ea (i-resp eb ez) (st z ez)))
  (λ h he → cnt-oi (<→◃ (σ q)) (λ u → add a σ (f (into (<→◃ q) u))) h (add-≅ {σ = σ} {σ′ = σ} ea (ct h he)))
Rs-add ga ea (ru {r = zero} g) eb = Rs-add ga ea g (u-refl zero eb)
Rs-add ga ea (ru {r = self n} g) eb = Rs-add ga ea g (u-refl (self n) eb)

Rs-iter : ∀ {ℓ} {c : Ordᶜ ℓ} → Rs c → c ≅ c → ∀ n → Rs (iter (c +_) zero n)
Rs-iter gc ec zero    = rz
Rs-iter gc ec (suc n) = Rs-add gc ec (Rs-iter gc ec n) (iter-self ec n)

Rs-ψ : ∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordᶜ k} → Rs x → x ≅ x → Rs (ψ p σ x)
chain-rs : ∀ {j k} {q : j <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k} →
           (∀ (z : Ordᶜ j) → z ≅ z → Rd j (<→◃ q) (into (<→◃ q) z) → Rs (f (into (<→◃ q) z))) →
           limᵢ q f ≅ limᵢ q f → ∀ n → Rs (chain q f n)
chain-rs {j} hb e zero = Rs-Ω j
chain-rs {q = q} {f = f} hb e (suc n) =
  Rs-ψ (hb (chain q f n) (chain-≅ e n) (Rs→Rd (<→◃ q) (chain-rs hb e n))) (i-resp e (chain-≅ e n))

Rs-ψ {i} rz ex = Rs-Ω i
Rs-ψ {i} {p = p} {σ = σ} (rs {a} g) ex = rl (Rs-iter (Rs-ψ g ea) eψ)
  where ea = s-inv ex
        eψ = ψ-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl i) ea
Rs-ψ (rl hg) ex = rl (λ n → Rs-ψ (hg n) (l-inv ex n))
Rs-ψ {i} {p = p} {σ = σ} (ri {j = j} {p = q} {f = f} hb st ct) ex with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = ri
  (λ z ez g → oi (<→◃ r) (λ u → Rs (ψ p σ (f (into (<→◃ q) (tr⁻ e u)))))
                 (Rs-ψ (hb (tr⁻ e z) (self-tr⁻ e ez) (Rs→Rd (<→◃ q) (Rs-tr⁻ e (Rd→Rs (<→◃ r) g) ez)))
                       (i-resp ex (self-tr⁻ e ez))))
  (λ z ez → str-oi (<→◃ r) (λ u → ψ p σ (f (into (<→◃ q) (tr⁻ e u)))) (λ u → ψ p σ (f (into (<→◃ q) (tr⁻ e u)))) z
              (Sp-ψ {p₁ = p} {σ₁ = σ} {p₂ = p} {σ₂ = σ} (i-resp ex (self-tr⁻ e ez)) (st (tr⁻ e z) (self-tr⁻ e ez))))
  (λ h he → cnt-oi (<→◃ r) (λ u → ψ p σ (f (into (<→◃ q) (tr⁻ e u)))) h
              (ψ-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl i) (ct (λ n → tr⁻ e (h n)) (λ n → self-tr⁻ e (he n)))))
... | injᵇ _ = rl (λ n → Rs-ψ (hb (chain q f n) (chain-≅ ex n) (Rs→Rd (<→◃ q) (chain-rs hb ex n))) (i-resp ex (chain-≅ ex n)))
... | injᶜ _ = rl (λ n → Rs-ψ (hb (chain q f n) (chain-≅ ex n) (Rs→Rd (<→◃ q) (chain-rs hb ex n))) (i-resp ex (chain-≅ ex n)))
Rs-ψ (ru {r = zero} g) ex   = Rs-ψ g (u-refl zero ex)
Rs-ψ (ru {r = self n} g) ex = Rs-ψ g (u-refl (self n) ex)

Rs-ψ¹ : ∀ {k} {x : Ordᶜ k} → Rs x → x ≅ x → Rs (ψ¹ x)
Rs-ψ¹ rz ex = Rs-Ω (suc zero)
Rs-ψ¹ (rs {a} g) ex = rl (Rs-iter (Rs-ψ¹ g ea) (ψ¹-≅ ea))
  where ea = s-inv ex
Rs-ψ¹ (rl hg) ex = rl (λ n → Rs-ψ¹ (hg n) (l-inv ex n))
Rs-ψ¹ (ri {j = zero} {p = q} {f = f} hb st ct) ex =
  ri (λ z ez g → Rs-ψ¹ (hb z ez (Rs→Rd (<→◃ q) g)) (i-resp ex ez))
     (λ z ez → Sp-ψ¹ (i-resp ex ez) (st z ez))
     (λ h he → ψ¹-≅ (ct h he))
Rs-ψ¹ (ri {j = suc a} {p = q} {f = f} hb st ct) ex =
  rl (λ n → Rs-ψ¹ (hb (chain q f n) (chain-≅ ex n) (Rs→Rd (<→◃ q) (chain-rs hb ex n))) (i-resp ex (chain-≅ ex n)))
Rs-ψ¹ (ri {j = lim h s} {p = q} {f = f} hb st ct) ex =
  rl (λ n → Rs-ψ¹ (hb (chain q f n) (chain-≅ ex n) (Rs→Rd (<→◃ q) (chain-rs hb ex n))) (i-resp ex (chain-≅ ex n)))
Rs-ψ¹ (ru {r = zero} g) ex   = Rs-ψ¹ g (u-refl zero ex)
Rs-ψ¹ (ru {r = self n} g) ex = Rs-ψ¹ g (u-refl (self n) ex)

Rs-em : ∀ a → Rs (em a)
Rs-em zero      = rz
Rs-em (suc a)   = rs (Rs-em a)
Rs-em (lim f s) = rl (λ n → Rs-em (f n))
```
