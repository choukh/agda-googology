# 统一形 (五): 层号 $(m,\alpha)$ 上的折叠

> 接 [Uniform5Syn](Uniform5Syn.lagda.md). 本文不导入记号. 结论先说:
>
> 1. **目标 `Tg m α`.** `ts q`: 同 $m$ 的目标 $\tau<\alpha$, 地板 `Fl`. `td p τ`: 低 $m$ 的目标 $(n,\tau)$, 地板多一项 `fk τ`, 证据 $\tau<\ell$.
> 2. **唯一的新比较 (`ψ≡`).** 节点 $(n,k)$ 与目标 $(n,\tau)$ 同 $m$ 且都低于当前的 $m$ 时, $k$ 与 $\tau$ 都不是任何字面 $\alpha$ 的子项 (否定见 Uniform5Wall `¬tri`). 但地板给 $k<\ell$ 与 $\tau<\ell$, 于是 `<ᴵ-dec` 在**环境 $\ell$** 之下可判定. 代价: 这个比较推迟到求值 (`oev`), 所以 `ψᵒ` 的输出依赖 $\ell$; 互模拟要证跨 $\ell$ 一致 (未写, 非对角同样由 `clash` 排除).
> 3. $m$ 不同时比较 ℕ, 不碰 `<ᴵ-dec`. 字面同 $m$ 的比较与 Uniform4Two 相同.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform5SynPsi where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ)
open import OCF.Align.Uniform3Base using
  (Flr; fz; fk; fb; _⊔_; Ev; Run; A; wk; limA; limᵢA; ŝA; ĉA; cloA; flo; cvFlo; toFlo; ∅ᴿ; sucRun)
open import OCF.Align.Uniform4Base using (Fl; asl; asr; swp; dupr; dupr2; _<ᴸ_; zero; suc; tr<; s<s; z<s)
open import OCF.Align.Uniform5Syn
```

## §1 目标

```agda
data Tg (m : ℕ) (α : Ordᴵ) : Set where
  ts : ∀ {τ} → τ <ᴵ α → Tg m α
  td : ∀ {n} → n <ᴸ m → (τ : Ordᴵ) → Tg m α

tm : ∀ {m α} → Tg m α → ℕ
tm {m} (ts _)      = m
tm (td {n} _ _)    = n

tτ : ∀ {m α} → Tg m α → Ordᴵ
tτ (ts {τ} _) = τ
tτ (td _ τ)   = τ

tf : ∀ {m α} → Tg m α → Flr
tf (ts _)   = Fl
tf (td _ τ) = Fl ⊔ fk τ

tfl : ∀ {m α} (g : Tg m α) {ℓ} → Ev ℓ (tf g) → Ev ℓ Fl
tfl (ts _)   e = e
tfl (td _ _) e = proj₁ e

akk : ∀ {k ℓ} → k <ᴵ ℓ → Simᴵ (suc k) ℓ
akk p zero    = p
akk p (suc q) = <ᴵ-trans q p

ak₂ : ∀ {k ℓ} → Ev ℓ Fl → k <ᴵ ℓ → Ev ℓ (Fl ⊔ fk k)
ak₂ f p = f , akk p

data Tri (a b : ℕ) : Set where
  tlt : a <ᴸ b → Tri a b
  teq : a ≡ b → Tri a b
  tgt : b <ᴸ a → Tri a b

tri : ∀ a b → Tri a b
tri zero    zero    = teq refl
tri zero    (suc b) = tlt (z<s b)
tri (suc a) zero    = tgt (z<s a)
tri (suc a) (suc b) with tri a b
... | tlt p = tlt (s<s p)
... | teq e = teq (cong suc e)
... | tgt p = tgt (s<s p)
```

## §2 折叠

`sub-ts`, `sub-td`: 链的目标. 与 Uniform4Two 一样, 链 `γ` 对分支 `h` 结构递归.

```agda
repᵒ : ∀ {m c φ} → Q m c φ → ℕ → Q m c φ
repᵒ x zero          = o0
repᵒ x (suc zero)    = x
repᵒ x (suc (suc m)) = owk (λ e → e , e) (repᵒ x (suc m) ⊕ x)

chainᵒ : ∀ {m k φ} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (Q m k φ → Q m k φ) → ℕ → Q m k φ
chainᵒ {m} {k} fe f zero    = owk fe (Ω̇ m k)
chainᵒ fe f (suc n) = f (chainᵒ fe f n)

ψᵒ : ∀ {m α} (g : Tg m α) {φ} → Q m α φ → Q (tm g) (tτ g) (tf g ⊔ φ)

-- 字面节点 k<α 上的链, 输出在 Q m k
chS : ∀ {m α k} (g : Tg m α) {φ} (r : k <ᴵ α) → (∀ ξ → Us m k (<→◃ r) ξ → Q m α (ξ ⊔ φ)) → ℕ → Q m k (tf g ⊔ φ)
chS g {φ} r h = chainᵒ (λ e → tfl g (proj₁ e)) (λ z → owk dupr2′ (ψᵒ (ts r) (h (tf g ⊔ φ) (intoU (<→◃ r) z))))
  where
  dupr2′ : ∀ {ℓ} → Ev ℓ (tf g ⊔ φ) → Ev ℓ (Fl ⊔ ((tf g ⊔ φ) ⊔ φ))
  dupr2′ e = tfl g (proj₁ e) , (e , proj₂ e)

-- 低 m 节点 (n′,k) 上的链, 输出在 Q n′ k
chD : ∀ {m α n′ k} (g : Tg m α) {φ} (qn : n′ <ᴸ m) → (∀ {ℓ} → Ev ℓ φ → k <ᴵ ℓ) → (∀ ξ → Vs m qn k ξ → Q m α (ξ ⊔ φ)) → ℕ → Q n′ k (tf g ⊔ φ)
chD {k = k} g {φ} qn ac h = chainᵒ (λ e → tfl g (proj₁ e)) (λ z → owk wkn (ψᵒ (td qn k) (h (tf g ⊔ φ) (intoV qn z))))
  where
  wkn : ∀ {ℓ} → Ev ℓ (tf g ⊔ φ) → Ev ℓ ((Fl ⊔ fk k) ⊔ ((tf g ⊔ φ) ⊔ φ))
  wkn e = (tfl g (proj₁ e) , akk (ac (proj₂ e))) , (e , proj₂ e)

ψ≡ : ∀ {m α n k φ τ} (p : n <ᴸ m) (qn : n <ᴸ m) (fe : ∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) (ac : ∀ {ℓ} → Ev ℓ φ → k <ᴵ ℓ) (h : ∀ ξ → Vs m qn k ξ → Q m α (ξ ⊔ φ)) →
     (k ≺ᴵ τ) ⊎ (τ ≺ᴵ k) ⊎ (k ≅ᴵ τ) → Q n τ ((Fl ⊔ fk τ) ⊔ φ)
ψ≡ {τ = τ} p qn fe ac h (inj₁ (via e′ s)) =
  oΩ (λ e → proj₁ (proj₁ e)) s (λ ξ y → owk swp (ψᵒ (td p τ) (h ξ (intoV qn (tr⁻O e′ (outU (<→◃ s) y))))))
ψ≡ {φ = φ} {τ = τ} p qn fe ac h (inj₂ _) =
  ol (λ n → owk dupr2 (ψᵒ (td p τ) (h ((Fl ⊔ fk τ) ⊔ φ) (intoV qn (chD (td p τ) qn ac h n)))))

ψᵒ {m} {α} g {φ} o0 = owk (λ e → tfl g (proj₁ e)) (Ω̇ (tm g) (tτ g))
ψᵒ g (os a) = ol (repᵒ (ψᵒ g a))
ψᵒ g (ol F) = ol (λ n → ψᵒ g (F n))
ψᵒ g (oi ac f) = oi (λ e → ac (proj₂ e)) (λ x → ψᵒ g (f x))
ψᵒ g (oŝ c₀ t h) = oŝ c₀ (ψᵒ g t) (λ η e → ψᵒ g (h η e))
ψᵒ g (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ψᵒ g o₀) (λ η e → ψᵒ g (o η e))
ψᵒ g (oclo t h) = owk asl (oclo (owk asr (ψᵒ g t)) (λ η → owk asr (ψᵒ g (h η))))
ψᵒ g (owk le x) = owk (λ e → proj₁ e , le (proj₂ e)) (ψᵒ g x)
ψᵒ g (oev f) = oev (λ e → ψᵒ g (f (proj₂ e)))
ψᵒ (ts q) {φ} (oΩ fe r h) with <ᴵ-dec r q
... | injᵃ (via e s) = oΩ proj₁ s (λ ξ y → owk swp (ψᵒ (ts q) (h ξ (intoU (<→◃ r) (tr⁻O e (outU (<→◃ s) y))))))
... | injᵇ _ = ol (λ n → owk dupr2 (ψᵒ (ts q) (h (Fl ⊔ φ) (intoU (<→◃ r) (chS (ts q) r h n)))))
... | injᶜ _ = ol (λ n → owk dupr2 (ψᵒ (ts q) (h (Fl ⊔ φ) (intoU (<→◃ r) (chS (ts q) r h n)))))
ψᵒ (td p τ) {φ} (oΩ fe r h) = ol (λ n → owk dupr2 (ψᵒ (td p τ) (h ((Fl ⊔ fk τ) ⊔ φ) (intoU (<→◃ r) (chS (td p τ) r h n)))))
ψᵒ (ts q) (oΩ↓ fe qn ac h) = oΩ↓ (λ e → fe (proj₂ e)) qn (λ e → ac (proj₂ e)) (λ ξ z → owk swp (ψᵒ (ts q) (h ξ z)))
ψᵒ (td {n} p τ) {φ} (oΩ↓ {n = n′} fe qn ac h) with tri n′ n
... | tlt s = oΩ↓ (λ e → fe (proj₂ e)) s (λ e → ac (proj₂ e)) (λ ξ z → owk swp (ψᵒ (td p τ) (h ξ (intoV qn (outV s z)))))
... | tgt _ = ol (λ n → owk dupr2 (ψᵒ (td p τ) (h ((Fl ⊔ fk τ) ⊔ φ) (intoV qn (chD (td p τ) qn ac h n)))))
... | teq refl = oev (λ e → ψ≡ p qn fe ac h (<ᴵ-dec (ac (proj₂ e)) (proj₂ (proj₁ e) zero)))

ψ̄ : ∀ {m c φ} → Q m c φ → Run φ
ψ̄ o0 = wk 0 (λ e → tt) ∅ᴿ
ψ̄ (os a) = sucRun (ψ̄ a)
ψ̄ (ol F) = limA 0 (λ n → ψ̄ (F n))
ψ̄ (oi ac f) = limᵢA 0 ac (λ x → ψ̄ (f x))
ψ̄ (oŝ c₀ t g) = ŝA 0 c₀ (ψ̄ t) (λ η e → ψ̄ (g η e))
ψ̄ (oĉ c₀ z zg o₀ o) = ĉA 0 c₀ z zg (ψ̄ o₀) (λ η e → ψ̄ (o η e))
ψ̄ (oclo t g) = cloA 0 (ψ̄ t) (λ η → ψ̄ (g η))
ψ̄ (owk le x) = wk 0 le (ψ̄ x)
ψ̄ {φ = φ} (oΩ fe r h) =
  limA 0 (λ n → wk 0 (λ v → v , v)
                (ψ̄ (h φ (intoU (<→◃ r) (chainᵒ fe (λ z → owk (λ v → fe v , (v , v)) (ψᵒ (ts r) (h φ (intoU (<→◃ r) z)))) n)))))
ψ̄ {φ = φ} (oΩ↓ {k = k} fe qn ac h) =
  limA 0 (λ n → wk 0 (λ v → v , v)
                (ψ̄ (h φ (intoV qn (chainᵒ fe (λ z → owk (λ v → ak₂ (fe v) (ac v) , (v , v)) (ψᵒ (td qn k) (h φ (intoV qn z)))) n)))))
ψ̄ (oev f) ev p = ψ̄ (f ev) ev p

-- ψ₀(Ω_{Ω·(m+1)+α})
TQ : ∀ m α → Run Fl
TQ m α = ψ̄ (Ω̇ m α)
```
