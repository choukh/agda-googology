> **机械克隆, 验收用.** 由 `LadderInfWRules3` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆, 验收用.** 由 `LadderInfRules3` 经 `Survey/scripts/laddernf/mk_infw.py` 复制, 只改导入, 落在标签阶梯的世界. 见 [LadderInfAccept](LadderInfAccept.lagda.md).

# 高度抽象: 地板规则

> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 对高度结构 `HtS` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFRules3](LadderNFRules3.lagda.md) 生成, 下面的说明是原文件的. 接 [LadderNFRules2](LadderNFRules2.lagda.md). `B1ᵀ`, `F0ᵀ`, `P0ᵀ`, `H0ᵀ`: 和与折叠压在左边或 $\dot\Omega$ 之上. `H0ᵀ` 是新的: 目标在高度 $H$ 时 $\Psi(x)\sqsupseteq\dot\Omega_t$. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderLabZInfWRules3 (𝕊 : HtS) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.LadderLabZNFWPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ; Ωˢ; addˢ; _+ˢ_; 𝟎ˢ)
open import OCF.Align.LadderLabZNFWEq using (≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; _≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; upˡ; upʳ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ; trˢ-≅; tr⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; addˢ-≅; s-invˢ; l-invˢ; i-respˢ; u-reflˢ; ŝ-refl₀; ĉ-refl₀; self-trˢ; self-tr⁻ˢ)
open import OCF.Align.LadderLabZNFWFloor using (_∼ᶠ_; ∼ᶠ-refl; fz∼; ⊔∼; Flr; fz; fk; Ev; Run; flo; cvFlo; toFlo; ∅ᴿ; _⊔_; bound)
open import OCF.Align.LadderLabZNFWForce using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Align.LadderLabZNFWFT using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderLabZInfWTree 𝕊
open import OCF.Align.LadderLabZInfWRel 𝕊
open import OCF.Align.LadderLabZInfWCx 𝕊
open import OCF.Align.LadderLabZInfWRules 𝕊
open import OCF.Align.LadderLabZInfWRules2 𝕊
open Ord-Ord using (iter)
open Restrˢ
open RestrQ
```

```agda
B1ᵀ : ∀ {m c c′ φ₀ χ₀ a b φ χ ψ ρ} {x : Q m c φ₀ χ₀} {W : Q m c a b} {t : Q m c φ χ} {t′ : Q m c′ ψ ρ} → Rq m c c′ t t′ → x ⊑ᵀ W → x ⊑ᵀ W ⊞ t
B1ᵀ rz h = wk-rᵀ h
B1ᵀ (rs s c r) h = suc-rᵀ (B1ᵀ r h)
B1ᵀ (rl f) h = lim-rᵀ 0 (B1ᵀ (f 0) h)
B1ᵀ (ri e f) h = qi-rᵀ (λ z d → B1ᵀ (f z (trˢ e z) (≅ˢ-sym (trˢ-≅ e (≅ˢ-reflˡ d)))) h)
B1ᵀ (rŝ e r f) h = ŝ-rᵀ (B1ᵀ r h)
B1ᵀ (rĉ e dz dg r f) h = ĉ-rᵀ (B1ᵀ r h)
B1ᵀ (rclo s r f) h = wk-rᵀ (clo-rᵀ (wk-rᵀ (B1ᵀ r h)))
B1ᵀ (rcl same s r f) h = cl-rᵀ (B1ᵀ r h)
B1ᵀ (rwkˡ r) h = wk-rᵀ (B1ᵀ r h)
B1ᵀ (rwkʳ r) h = B1ᵀ r h
B1ᵀ (rob e l r) h = B1ᵀ r h
B1ᵀ {W = W} (rΩ↓ {q = q} {h = h₀} same ek s c f) h = Ω↓-rᵀ {q = q} {h = λ ξ ζ z → qwk swp (λ i q₁ → swp) (W ⊞ h₀ ξ ζ z)} (λ ξ ζ z rz fz → wk-rᵀ (B1ᵀ (f ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) (Sim∼-refl ζ) z (trQ ek z) (intoVq q (R-trʳ ek rz))) h))
B1ᵀ {W = W} (rΩ {r = r} {h = h₀} ek s c f) h = Ω-rᵀ {h = λ ξ ζ z → qwk swp (λ i q → swp) (W ⊞ h₀ ξ ζ z)} (λ ξ ζ z rz fz → wk-rᵀ (B1ᵀ (f ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) z (trQ ek z) (intoRq (<→◃ r) (R-trʳ ek rz))) h))

F0ᵀ : ∀ {m c c′ φ χ ψ ρ i ℓ w} {x : Q m c φ χ} {x′ : Q m c′ ψ ρ} {ok : Ok w} {e : Eh h₀ m w χ} {ev : Ev ℓ φ} {p : i <ᴵ ℓ} → Rq m c c′ x x′ → Ωˢ i ⊑ᴱ ψ̄ᵠ ok e x ev p
F0ᵀ {i = i} rz = ≅→⊑ᴱ (Ωˢ-refl i)
F0ᵀ {x = qs a} {ok = ok} {e = e} {ev = ev} {p = p} (rs s c r) = lim-rᴱ {h = iter (ψ̄ᵠ ok e a ev p +ˢ_) Ord₊ˢ.zero} 1 (F0ᵀ r)
F0ᵀ {x = ql F} {ok = ok} {e = e} {ev = ev} {p = p} (rl f) = lim-rᴱ {h = λ n → ψ̄ᵠ ok e (F n) ev p} 0 (F0ᵀ (f 0))
F0ᵀ {i = i} {x = qi {j = j} ac f₀} {ok = ok} {e = e} {ev = ev} {p = p} (ri d f) with <ᴵ-dec (ac ev) p
... | injᵃ (via e₁ s) = limᵢ-rᴱ {q = s} {g = λ y → ψ̄ᵠ ok e (f₀ (tr⁻ˢ e₁ (outˢ (<→◃ s) y))) ev p} (λ z d₁ →
        subst (λ u → Ωˢ i ⊑ᴱ ψ̄ᵠ ok e (f₀ (tr⁻ˢ e₁ u)) ev p) (sym (out-intoˢ (<→◃ s) z))
              (F0ᵀ (f (tr⁻ˢ e₁ z) (trˢ d (tr⁻ˢ e₁ z)) (≅ˢ-sym (trˢ-≅ d (self-tr⁻ˢ e₁ (≅ˢ-reflˡ d₁)))))))
... | injᵇ _ = lim-rᴱ {h = λ n → ψ̄ᵠ ok e (f₀ (iter (λ w → ψ̄ᵠ ok e (f₀ w) ev (ac ev)) (Ωˢ j) n)) ev p} 0 (F0ᵀ (f (Ωˢ j) (trˢ d (Ωˢ j)) (≅ˢ-sym (trˢ-≅ d (Ωˢ-refl j)))))
... | injᶜ _ = lim-rᴱ {h = λ n → ψ̄ᵠ ok e (f₀ (iter (λ w → ψ̄ᵠ ok e (f₀ w) ev (ac ev)) (Ωˢ j) n)) ev p} 0 (F0ᵀ (f (Ωˢ j) (trˢ d (Ωˢ j)) (≅ˢ-sym (trˢ-≅ d (Ωˢ-refl j)))))
F0ᵀ {x = qŝ c₀ t g} {ok = ok} {e = e} {ev = ev} {p = p} (rŝ d r f) = ŝ-rᴱ {t₀ = ψ̄ᵠ ok e t ev p} (F0ᵀ r)
F0ᵀ {x = qĉ c₀ z zg o₀ o} {ok = ok} {e = e} {ev = ev} {p = p} (rĉ d dz dg r f) = ĉ-rᴱ {o₀ = ψ̄ᵠ ok e o₀ ev p} (F0ᵀ r)
F0ᵀ {x = qclo t g} {ok = ok} {e = e} {ev = ev} {p = p} (rclo s r f) = ŝ-rᴱ {t₀ = ψ̄ᵠ ok e t ev p} (F0ᵀ r)
F0ᵀ {x = qcl q ψ s₀ t g} {ok = ok} {e = e} {ev = ev} {p = p} (rcl same s r f) = ŝ-rᴱ {t₀ = ψ̄ᵠ ok e t ev p} (F0ᵀ r)
F0ᵀ (rwkˡ r) = F0ᵀ r
F0ᵀ (rwkʳ r) = F0ᵀ r
F0ᵀ (rob d l r) = F0ᵀ r
F0ᵀ {x = qΩ↓ {φ = φ} {χ = χ} {n = n} {k = k} q fe ac h} {ok = ok} {e = e} {ev = ev} {p = p} (rΩ↓ same ek s c f) =
  lim-rᴱ {h = λ i → ψ̄ᵠ ok (e⁺ n ok e) (h φ (Z* χ) (intoV q (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* n)) (Ψ q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) (h φ (Z* χ) (intoV q z)))) i))) (ev , ev) p} 0
    (F0ᵀ (f φ φ (Z* χ) (Z* χ) (∼ᶠ-refl φ) (Sim∼-refl _) (Sim∼-refl _) (qwk fe fc* (Ω̇ n k)) (trQ ek (qwk fe fc* (Ω̇ n k))) (intoVq q (R-trʳ ek (rwk (RΩ̇ n (≅ᴵ-refl k)))))))
F0ᵀ {m} {x = qΩ {φ = φ} {χ = χ} {k = k} fe r h} {ok = ok} {e = e} {ev = ev} {p = p} (rΩ ek s c f) =
  lim-rᴱ {h = λ i → ψ̄ᵠ ok (e⁺ m ok e) (h φ (Z* χ) (intoU (<→◃ r) (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* m)) (ψᵠ r (h φ (Z* χ) (intoU (<→◃ r) z)))) i))) (ev , ev) p} 0
    (F0ᵀ (f φ φ (Z* χ) (Z* χ) (∼ᶠ-refl φ) (Sim∼-refl _) (qwk fe fc* (Ω̇ m k)) (trQ ek (qwk fe fc* (Ω̇ m k))) (intoRq (<→◃ r) (R-trʳ ek (rwk (RΩ̇ m (≅ᴵ-refl k)))))))

P0ᵀ : ∀ {m c c′ t φ₀ χ₀ φ χ ψ ρ} {y : Q m t φ₀ χ₀} {q : t <ᴵ c} {x : Q m c φ χ} {x′ : Q m c′ ψ ρ} → Rq m c c′ x x′ → y ⊑ᵀ Ω̇ m t → y ⊑ᵀ ψᵠ q x
P0ᵀ {q = q} rz h = wk-rᵀ h
P0ᵀ {q = q} {x = qs a} (rs s c r) h = lim-rᵀ {F = repᵠ (ψᵠ q a)} 1 (P0ᵀ {q = q} r h)
P0ᵀ {q = q} (rl f) h = lim-rᵀ 0 (P0ᵀ {q = q} (f 0) h)
P0ᵀ {q = q} (ri e f) h = qi-rᵀ (λ z d → P0ᵀ {q = q} (f z (trˢ e z) (≅ˢ-sym (trˢ-≅ e (≅ˢ-reflˡ d)))) h)
P0ᵀ {q = q} (rŝ e r f) h = ŝ-rᵀ (P0ᵀ {q = q} r h)
P0ᵀ {q = q} (rĉ e dz dg r f) h = ĉ-rᵀ (P0ᵀ {q = q} r h)
P0ᵀ {q = q} (rclo s r f) h = wk-rᵀ (clo-rᵀ (wk-rᵀ (P0ᵀ {q = q} r h)))
P0ᵀ {q = q} (rcl same s r f) h = cl-rᵀ (P0ᵀ {q = q} r h)
P0ᵀ {q = q} (rwkˡ r) h = wk-rᵀ (P0ᵀ {q = q} r h)
P0ᵀ {q = q} (rwkʳ r) h = P0ᵀ {q = q} r h
P0ᵀ {q = q} (rob d l r) h = P0ᵀ {q = q} r h
P0ᵀ {q = q₀} (rΩ↓ {q = q} {h = h₀} same ek s c f) h = Ω↓-rᵀ {q = q} {h = λ ξ ζ z → qwk swp (λ i r′ → swp) (ψᵠ q₀ (h₀ ξ ζ z))} (λ ξ ζ z rz fz → wk-rᵀ (P0ᵀ {q = q₀} (f ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) (Sim∼-refl ζ) z (trQ ek z) (intoVq q (R-trʳ ek rz))) h))
P0ᵀ {m} {t = t} {y = y} {q = q} {x = qΩ {φ = φ} {χ = χ} {k = k₁} fe r h₀} (rΩ ek s c f) h with <ᴵ-dec r q
... | injᵃ (via e s₁) = Ω-rᵀ {h = λ ξ ζ z → qwk swp (λ i r′ → swp) (ψᵠ q (h₀ ξ ζ (intoU (<→◃ r) (tr⁻Q e (outU (<→◃ s₁) z)))))}
    (λ ξ ζ z rz fz → wk-rᵀ (subst (λ w → y ⊑ᵀ ψᵠ q (h₀ ξ ζ (intoU (<→◃ r) (tr⁻Q e w)))) (sym (out-intoU (<→◃ s₁) z))
       (P0ᵀ {q = q} (f ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) (tr⁻Q e z) (trQ ek (tr⁻Q e z)) (intoRq (<→◃ r) (R-trʳ ek (R-tr⁻ˡ e (R-tr⁻ʳ e rz))))) h)))
... | injᵇ _ = lim-rᵀ {F = λ n → qwk dupr2 (⇑ (cv* m)) (ψᵠ q (h₀ (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h₀ (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) n))))} 0
    (wk-rᵀ (P0ᵀ {q = q} (f (Fl ⊔ φ) (Fl ⊔ φ) (Z* χ) (Z* χ) (∼ᶠ-refl _) (Sim∼-refl _) (qwk proj₁ fc* (Ω̇ m k₁)) (trQ ek (qwk proj₁ fc* (Ω̇ m k₁))) (intoRq (<→◃ r) (R-trʳ ek (rwk (RΩ̇ m (≅ᴵ-refl k₁)))))) h))
... | injᶜ _ = lim-rᵀ {F = λ n → qwk dupr2 (⇑ (cv* m)) (ψᵠ q (h₀ (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h₀ (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) n))))} 0
    (wk-rᵀ (P0ᵀ {q = q} (f (Fl ⊔ φ) (Fl ⊔ φ) (Z* χ) (Z* χ) (∼ᶠ-refl _) (Sim∼-refl _) (qwk proj₁ fc* (Ω̇ m k₁)) (trQ ek (qwk proj₁ fc* (Ω̇ m k₁))) (intoRq (<→◃ r) (R-trʳ ek (rwk (RΩ̇ m (≅ᴵ-refl k₁)))))) h))

H0ᵀ : ∀ {H m c c′ t φ₀ χ₀ φ χ ψ ρ w} {y : Q H t φ₀ χ₀} {qH : H <ᴸ m} {ok : Ok w} {e : Eh H m w χ} {p : t <ᴵ w H} {x : Q m c φ χ} {x′ : Q m c′ ψ ρ} → Rq m c c′ x x′ → y ⊑ᵀ Ω̇ H t → y ⊑ᵀ Ψ qH ok e p x
H0ᵀ rz h = wk-rᵀ h
H0ᵀ {qH = qH} {ok = ok} {e = e} {p = p} {x = qs a} (rs s c r) h = lim-rᵀ {F = repᵠ (Ψ qH ok e p a)} 1 (H0ᵀ r h)
H0ᵀ (rl f) h = lim-rᵀ 0 (H0ᵀ (f 0) h)
H0ᵀ (ri e f) h = qi-rᵀ (λ z d → H0ᵀ (f z (trˢ e z) (≅ˢ-sym (trˢ-≅ e (≅ˢ-reflˡ d)))) h)
H0ᵀ (rŝ e r f) h = ŝ-rᵀ (H0ᵀ r h)
H0ᵀ (rĉ e dz dg r f) h = ĉ-rᵀ (H0ᵀ r h)
H0ᵀ (rclo s r f) h = wk-rᵀ (clo-rᵀ (wk-rᵀ (H0ᵀ r h)))
H0ᵀ (rwkˡ r) h = wk-rᵀ (H0ᵀ r h)
H0ᵀ (rwkʳ r) h = H0ᵀ r h
H0ᵀ (rob d l r) h = H0ᵀ r h
H0ᵀ {H} {qH = qH} {ok = ok} {e = e} {p = p} {x = qcl {n = n} q ψ s₀ t g} (rcl same s r f) h with tri n H
... | tlt l = cl-rᵀ (H0ᵀ r h)
... | teq refl = ŝ-rᵀ (H0ᵀ r h)
... | tgt l = ŝ-rᵀ (H0ᵀ r h)
H0ᵀ {H} {y = y} {qH = qH} {ok = ok} {e = e} {p = p} {x = qΩ↓ {φ = φ} {χ = χ} {n = n} {k = k} q fe ac h₀} (rΩ↓ same ek s c f) h with tri n H
... | tlt l = Ω↓-rᵀ {q = l} {h = λ ξ ζ z → qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ (inj₂ l) e) p (h₀ ξ ζ (intoV q (outV l z))))}
    (λ ξ ζ z rz fz → wk-rᵀ (subst (λ w → y ⊑ᵀ Ψ qH ok (e-lo ζ (inj₂ l) e) p (h₀ ξ ζ (intoV q w))) (sym (out-intoV l z))
       (H0ᵀ (f ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) (Sim∼-refl ζ) z (trQ ek z) (intoVq q (R-trʳ ek rz))) h)))
... | teq refl with <ᴵ-dec (ac (e n (inj₁ refl) q)) p
...   | injᵃ (via d s₁) = Ω-rᵀ {h = λ ξ ζ z → qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h₀ ξ ζ (intoV q (tr⁻Q d (outU (<→◃ s₁) z)))))}
    (λ ξ ζ z rz fz → wk-rᵀ (subst (λ w → y ⊑ᵀ Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h₀ ξ ζ (intoV q (tr⁻Q d w)))) (sym (out-intoU (<→◃ s₁) z))
       (H0ᵀ (f ξ ξ ζ ζ (∼ᶠ-refl ξ) (Sim∼-refl ζ) (Sim∼-refl ζ) (tr⁻Q d z) (trQ ek (tr⁻Q d z)) (intoVq q (R-trʳ ek (R-tr⁻ˡ d (R-tr⁻ʳ d rz))))) h)))
...   | injᵇ _ = lim-rᵀ {F = λ i → qwk dupr2 (⇑ (cv* n)) (Ψ qH ok (e⁺ n ok e) p (h₀ (Fl ⊔ φ) (Z* χ) (intoV q (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* n)) (Ψ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) (h₀ (Fl ⊔ φ) (Z* χ) (intoV q z)))) i))))} 0
    (wk-rᵀ (H0ᵀ (f (Fl ⊔ φ) (Fl ⊔ φ) (Z* χ) (Z* χ) (∼ᶠ-refl _) (Sim∼-refl _) (Sim∼-refl _) (qwk proj₁ fc* (Ω̇ n k)) (trQ ek (qwk proj₁ fc* (Ω̇ n k))) (intoVq q (R-trʳ ek (rwk (RΩ̇ n (≅ᴵ-refl k)))))) h))
...   | injᶜ _ = lim-rᵀ {F = λ i → qwk dupr2 (⇑ (cv* n)) (Ψ qH ok (e⁺ n ok e) p (h₀ (Fl ⊔ φ) (Z* χ) (intoV q (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* n)) (Ψ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) (h₀ (Fl ⊔ φ) (Z* χ) (intoV q z)))) i))))} 0
    (wk-rᵀ (H0ᵀ (f (Fl ⊔ φ) (Fl ⊔ φ) (Z* χ) (Z* χ) (∼ᶠ-refl _) (Sim∼-refl _) (Sim∼-refl _) (qwk proj₁ fc* (Ω̇ n k)) (trQ ek (qwk proj₁ fc* (Ω̇ n k))) (intoVq q (R-trʳ ek (rwk (RΩ̇ n (≅ᴵ-refl k)))))) h))
H0ᵀ {H} {y = y} {qH = qH} {ok = ok} {e = e} {p = p} {x = qΩ↓ {φ = φ} {χ = χ} {n = n} {k = k} q fe ac h₀} (rΩ↓ same ek s c f) h | tgt l =
  lim-rᵀ {F = λ i → qwk dupr2 (⇑ (cv* n)) (Ψ qH ok (e⁺ n ok e) p (h₀ (Fl ⊔ φ) (Z* χ) (intoV q (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* n)) (Ψ q ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q)) (h₀ (Fl ⊔ φ) (Z* χ) (intoV q z)))) i))))} 0
    (wk-rᵀ (H0ᵀ (f (Fl ⊔ φ) (Fl ⊔ φ) (Z* χ) (Z* χ) (∼ᶠ-refl _) (Sim∼-refl _) (Sim∼-refl _) (qwk proj₁ fc* (Ω̇ n k)) (trQ ek (qwk proj₁ fc* (Ω̇ n k))) (intoVq q (R-trʳ ek (rwk (RΩ̇ n (≅ᴵ-refl k)))))) h))
H0ᵀ {m = m} {qH = qH} {ok = ok} {e = e} {p = p} {x = qΩ {φ = φ} {χ = χ} {k = k} fe r h₀} (rΩ ek s c f) h =
  lim-rᵀ {F = λ i → qwk dupr2 (⇑ (cv* m)) (Ψ qH ok (e⁺ m ok e) p (h₀ (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h₀ (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) i))))} 0
    (wk-rᵀ (H0ᵀ (f (Fl ⊔ φ) (Fl ⊔ φ) (Z* χ) (Z* χ) (∼ᶠ-refl _) (Sim∼-refl _) (qwk proj₁ fc* (Ω̇ m k)) (trQ ek (qwk proj₁ fc* (Ω̇ m k))) (intoRq (<→◃ r) (R-trʳ ek (rwk (RΩ̇ m (≅ᴵ-refl k)))))) h))

add-rᴱ : ∀ {k ℓ ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ′} (b : Ordˢ k) → a ≅ˢ a′ → b ≅ˢ b → a ⊑ᴱ addˢ a′ σ b
add-rᴱ Ord₊ˢ.zero ea eb = ≅→⊑ᴱ ea
add-rᴱ {σ = σ} (Ord₊ˢ.suc b) ea eb = suc-rᴱ (add-rᴱ {σ = σ} b ea (s-invˢ eb))
add-rᴱ {σ = σ} (Ord₊ˢ.lim h) ea eb = lim-rᴱ 0 (add-rᴱ {σ = σ} (h 0) ea (l-invˢ eb 0))
add-rᴱ {a = a} {a′ = a′} {σ = σ} (Ord₊ˢ.limᵢ q g) ea eb = limᵢ-rᴱ (λ z d →
  subst (λ u → a ⊑ᴱ addˢ a′ σ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ q)) z))
        (add-rᴱ {σ = σ} (g (intoˢ (<→◃ q) z)) ea (i-respˢ eb (≅ˢ-reflˡ d))))
add-rᴱ {σ = σ} (Ord₊ˢ.up zero x)     ea eb = add-rᴱ {σ = λ q → σ (suc q)} x ea (u-reflˢ zero eb)
add-rᴱ {σ = σ} (Ord₊ˢ.up (self n) x) ea eb = add-rᴱ {σ = λ q → σ (lim n q)} x ea (u-reflˢ (self n) eb)
add-rᴱ {k = zero}    {σ = σ} (Ord₊ˢ.ŝ c t₀ g) ea eb = ĉ-rᴱ (add-rᴱ {σ = σ} t₀ ea (ŝ-refl₀ eb))
add-rᴱ {k = suc _}   {σ = σ} (Ord₊ˢ.ŝ c t₀ g) ea eb = ŝ-rᴱ (add-rᴱ {σ = σ} t₀ ea (ŝ-refl₀ eb))
add-rᴱ {k = lim _ _} {σ = σ} (Ord₊ˢ.ŝ c t₀ g) ea eb = ŝ-rᴱ (add-rᴱ {σ = σ} t₀ ea (ŝ-refl₀ eb))
add-rᴱ {σ = σ} (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) ea eb = ĉ-rᴱ (add-rᴱ {σ = σ} o₀ ea (ĉ-refl₀ eb))


zero-lᵀ : ∀ {m c φ χ ψ ρ φ₁ χ₁} {y : Q m c ψ ρ} {y′ : Q m c φ₁ χ₁} → Rq m c c y y′ → q0 {φ = φ} {χ = χ} ⊑ᵀ y
zero-lᵀ {y = y} r (top {ev′ = ev′} {p′ = p′} {ok′ = ok′} {e′ = e′} o) = F0ᵀ {x = y} {ok = ok′} {e = e′} {ev = ev′} {p = p′} r o
zero-lᵀ r (pa rW o) = B1ᵀ r (wk-lᵀ (R→⊑ᵀ rW)) o
zero-lᵀ {m} {y = y} r (pψ {t = t} {q = q} o) = P0ᵀ {y = qwk proj₁ fc* (Ω̇ m t)} {q = q} {x = y} r (wk-lᵀ (R→⊑ᵀ (RΩ̇ m (≅ᴵ-refl t)))) o
zero-lᵀ {y = y} r (pΨ {H = H} {t = t} o) = H0ᵀ {y = qwk proj₁ fc* (Ω̇ H t)} {x = y} r (wk-lᵀ (R→⊑ᵀ (RΩ̇ H (≅ᴵ-refl t)))) o
zero-lᵀ {y = y} r (pι {q = q} o) = zero-lᵀ {y = ι q y} (R-ι q q r) o
zero-lᵀ {y = y} r (pD {q = qd} o) = zero-lᵀ {y = ι↓ {α = zero} qd y} (R-ι↓ qd (≅ᴵ-refl _) r) o
zero-lᵀ {y = y} r (ptr {e′ = e} o) = zero-lᵀ {y = trQ e y} (R-trˡ e (R-trʳ e r)) o
zero-lᵀ {y = y} r (ptr⁻ {e′ = e} o) = zero-lᵀ {y = tr⁻Q e y} (R-tr⁻ˡ e (R-tr⁻ʳ e r)) o

zero-lᴱ : ∀ {k k′} {y : Ordˢ k′} → y ≅ˢ y → 𝟎ˢ {k} ⊑ᴱ y
zero-lᴱ ey idO G′ = gz , λ ()
zero-lᴱ {k′ = k′} {y = y} ey (tlo {ρ = ρ₀} o) = zero-lᵀ {y = tl {χ = ρ₀} (flo k′) (cvFlo k′) y} (R-tl {χ = ρ₀} {ρ = ρ₀} {cv = cvFlo k′} {cv′ = cvFlo k′} ey) o
zero-lᴱ {y = y} ey (addo {σ′ = σ′} o k ea) = add-rᴱ {σ = σ′} y ea ey o
zero-lᴱ ey (tro {b = b} {e′ = e′} o)  = zero-lᴱ {k = b} (self-trˢ e′ ey) o
zero-lᴱ ey (tr⁻o {a = a} {e′ = e′} o) = zero-lᴱ {k = a} (self-tr⁻ˢ e′ ey) o

Ω0ᴱ : ∀ b → Ωˢ zero ⊑ᴱ Ωˢ b
Ω0ᴱ zero      = ≅→⊑ᴱ (Ωˢ-refl zero)
Ω0ᴱ (suc b)   = limᵢ-rᴱ (λ z d → up-rᴱ {r = zero} {y = z} (⊑ᴱ-≅ʳ (Ω0ᴱ b) (≅ˢ-sym d)))
Ω0ᴱ (lim g s) = lim-rᴱ 0 (up-rᴱ {r = self 0} (Ω0ᴱ (g 0)))


add-floorᴱ : ∀ {k ℓ ℓ₀} {x : Ordˢ ℓ₀} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} (b : Ordˢ k) → x ⊑ᴱ a → b ≅ˢ b → x ⊑ᴱ addˢ a σ b
add-floorᴱ Ord₊ˢ.zero h eb = h
add-floorᴱ {σ = σ} (Ord₊ˢ.suc b) h eb = suc-rᴱ (add-floorᴱ {σ = σ} b h (s-invˢ eb))
add-floorᴱ {σ = σ} (Ord₊ˢ.lim f) h eb = lim-rᴱ 0 (add-floorᴱ {σ = σ} (f 0) h (l-invˢ eb 0))
add-floorᴱ {x = x} {a = a} {σ = σ} (Ord₊ˢ.limᵢ q g) h eb = limᵢ-rᴱ (λ z d →
  subst (λ u → x ⊑ᴱ addˢ a σ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ q)) z))
        (add-floorᴱ {σ = σ} (g (intoˢ (<→◃ q) z)) h (i-respˢ eb (≅ˢ-reflˡ d))))
add-floorᴱ {σ = σ} (Ord₊ˢ.up zero y) h eb     = add-floorᴱ {σ = λ q → σ (suc q)} y h (u-reflˢ zero eb)
add-floorᴱ {σ = σ} (Ord₊ˢ.up (self n) y) h eb = add-floorᴱ {σ = λ q → σ (lim n q)} y h (u-reflˢ (self n) eb)
add-floorᴱ {k = zero}    {σ = σ} (Ord₊ˢ.ŝ c t₀ g) h eb = ĉ-rᴱ (add-floorᴱ {σ = σ} t₀ h (ŝ-refl₀ eb))
add-floorᴱ {k = suc _}   {σ = σ} (Ord₊ˢ.ŝ c t₀ g) h eb = ŝ-rᴱ (add-floorᴱ {σ = σ} t₀ h (ŝ-refl₀ eb))
add-floorᴱ {k = lim _ _} {σ = σ} (Ord₊ˢ.ŝ c t₀ g) h eb = ŝ-rᴱ (add-floorᴱ {σ = σ} t₀ h (ŝ-refl₀ eb))
add-floorᴱ {σ = σ} (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) h eb = ĉ-rᴱ (add-floorᴱ {σ = σ} o₀ h (ĉ-refl₀ eb))


```
