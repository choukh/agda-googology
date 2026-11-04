# 前驱的保序映射给折叠单调

> 接 [BTBOFullLe](BTBOFullLe.lagda.md). `PEmb a b`: 从 $a$ 的前驱到 $b$ 的前驱的映射, 保 $\prec^\mathsf{I}$, 保 $\cong^\mathsf{I}$. 定理 `Ψ-emb`: 有 `PEmb a b` 就有 $\psi^0(\Omega_a)\preccurlyeq\psi^0(\Omega_b)$. 没有别的前提, $a$ 的 `lim` 不必严格.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOFullEmb where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; _×_)
open import OCF.Align.Level
open import OCF.Align.Value using (_≼_)
open import OCF.Align.BTBOFullLe using (module LeE)

record PEmb (a b : Ordᴵ) : Set where
  field
    map  : ∀ {c} → c ≺ᴵ a → Ordᴵ
    bnd  : ∀ {c} (r : c ≺ᴵ a) → map r ≺ᴵ b
    mono : ∀ {c d} (r : c ≺ᴵ a) (s : d ≺ᴵ a) → c ≺ᴵ d → map r ≺ᴵ map s
    coh  : ∀ {c d} (r : c ≺ᴵ a) (s : d ≺ᴵ a) → c ≅ᴵ d → map r ≅ᴵ map s

module PE {a b : Ordᴵ} (P : PEmb a b) where
  open PEmb P

  data E : Ordᴵ → Ordᴵ → Set where
    top : ∀ {x x′} → x ≅ᴵ a → x′ ≅ᴵ b → E x x′
    sub : ∀ {x x′} (r : x ≺ᴵ a) → x′ ≅ᴵ map r → E x x′

  E-resp : ∀ {x y x′ y′} → E x y → x ≅ᴵ x′ → y ≅ᴵ y′ → E x′ y′
  E-resp (top e e′) d d′ = top (≅ᴵ-trans (≅ᴵ-sym d) e) (≅ᴵ-trans (≅ᴵ-sym d′) e′)
  E-resp (sub r e′) d d′ = sub (≺ᴵ-respˡ (≅ᴵ-sym d) r) (≅ᴵ-trans (≅ᴵ-sym d′) (≅ᴵ-trans e′ (coh r (≺ᴵ-respˡ (≅ᴵ-sym d) r) d)))

  open LeE E E-resp ⊥

  lt′ : ∀ {x x′ y y′} → E x x′ → E y y′ → x ≺ᴵ y → x′ ≺ᴵ y′
  lt′ (top e e′) (top d d′) r = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym e) (≺ᴵ-respʳ r d)))
  lt′ (top e e′) (sub s d′) r = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans (≺ᴵ-respˡ (≅ᴵ-sym e) r) s))
  lt′ (sub s e′) (top d d′) r = ≺ᴵ-respˡ e′ (≺ᴵ-respʳ (bnd s) (≅ᴵ-sym d′))
  lt′ (sub s e′) (sub t d′) r = ≺ᴵ-respˡ e′ (≺ᴵ-respʳ (mono s t r) (≅ᴵ-sym d′))

  eq′ : ∀ {x x′ y y′} → E x x′ → E y y′ → x ≅ᴵ y → x′ ≅ᴵ y′
  eq′ (top e e′) (top d d′) r = ≅ᴵ-trans e′ (≅ᴵ-sym d′)
  eq′ (top e e′) (sub s d′) r = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym (≅ᴵ-trans (≅ᴵ-sym r) e)) s))
  eq′ (sub s e′) (top d d′) r = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym (≅ᴵ-trans r d)) s))
  eq′ (sub s e′) (sub t d′) r = ≅ᴵ-trans e′ (≅ᴵ-trans (coh s t r) (≅ᴵ-sym d′))

  low : ∀ {d c c′} → E c c′ → d ≺ᴵ c → Σ (d ≺ᴵ a) (λ r → map r ≺ᴵ c′)
  low (top e e′) q = let r = ≺ᴵ-respʳ q e in r , ≺ᴵ-respʳ (bnd r) (≅ᴵ-sym e′)
  low (sub s e′) q = let r = ≺ᴵ-trans q s in r , ≺ᴵ-respʳ (mono r s q) (≅ᴵ-sym e′)

  Ω′ : ∀ {x c c′} → x ⊑ᴵ c → E c c′ → Le (Ω x) (Ω c′)
  Ω′ {c′ = c′} z⊑ ec = Le-one c′ (≅ᴵ-refl c′)
  Ω′ {c′ = c′} (s⊑ e q) ec with low ec (via e q)
  ... | r , via e₂ q₂ = walk c′ (≅ᴵ-refl c′) (sub r e₂′) q₂
    where e₂′ = ≅ᴵ-sym e₂
  Ω′ (l⊑ k) ec = Lll (λ n → Lul (Ω′ (k n) ec))

  ℒ : Laws
  ℒ = record { lt-pres = lt′ ; eq-pres = eq′ ; Ωlaw = Ω′ ⊑ᴵ-refl ; Ωc = λ () }

  open WithLaws ℒ

  Ψ-emb′ : ψ⁰ (Ω a) ≼ ψ⁰ (Ω b)
  Ψ-emb′ = Ψ⁰-emb (top (≅ᴵ-refl a) (≅ᴵ-refl b))

Ψ-emb : ∀ {a b} → PEmb a b → ψ⁰ (Ω a) ≼ ψ⁰ (Ω b)
Ψ-emb P = PE.Ψ-emb′ P
```
