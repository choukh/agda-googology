# 数据树上的无符号闭包定理 (三): 严格增长与上下文条件

> 接 [UniformNF4Rules](UniformNF4Rules.lagda.md). 结论先说:
>
> 1. **`≺ᵀ`, `≺ᴱ` 是对一切上下文量化的严格关系, 所以它对 $\psi$, $\oplus$, $\iota$ 的封闭是定义性的.** 旧的 `Rs` 要把 "$a+1\sqsubseteq y$" 一层一层搬过折叠, 每层再生 $+1$; `suc-fold₁` 要帧的 `stE`. 这里只有一个引理 `Sᵀ`: $C(a)\prec C'(a+1)$, 对一切上下文.
> 2. **`pψ` 子句是全文唯一读 $\psi$ 后继行的地方.** $\psi(a+1)=\lim\mathrm{rep}\,X\ni X\oplus X\sqsupseteq X\oplus 1=(X\oplus 0)+1$. 这里的 $X\oplus X$ 就是 "第 2 份", 不要任何帧条件. `Sᵀ` 累积弱化 $L$, 因为右侧的地板在 $\oplus$ 下变.
> 3. **`S1ᵀ`, `P0ᵀ`, `F0ᵀ`: 地板对一切树成立.** 旧的 `PFl`/`FFl` 字段全部变成定理: 不再有 "前缀的好条件".
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF4Strict where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ; Ωˢ; addˢ; _+ˢ_)
open Restrˢ
open import OCF.Align.UniformNF3Eq using (≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ʳ; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; upˡ; upʳ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ;
  trˢ-≅; tr⁻ˢ-≅; backˢ-≅; back⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; addˢ-≅; self-trˢ; self-tr⁻ˢ)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; Ev; flo; cvFlo; _⊔_; ∼ᶠ-refl)
open import OCF.Align.NotFree using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3NBase using (Goodᴺ-tr)
open import OCF.Align.Uniform4Base
open import OCF.Align.UniformNF4Base
open import OCF.Align.UniformNF4Rules
```

## §1 $1$ 与上下文条件

```agda
σ₀ : ∀ {ℓ} → Simᴵ zero ℓ
σ₀ ()

𝟏 : Ordˢ zero
𝟏 = Ord₊ˢ.suc Ord₊ˢ.zero

𝟏ᵀ : ∀ {c} → O c fz
𝟏ᵀ = os o0

Ω1ᴱ : ∀ b → 𝟏 ⊑ᴱ Ωˢ b
Ω1ᴱ zero      = ≅→⊑ᴱ (s≅ z≅ z≅)
Ω1ᴱ (suc b)   = limᵢ-rᴱ (λ z d → up-rᴱ {r = zero} {y = z} (⊑ᴱ-≅ʳ (Ω1ᴱ b) (≅ˢ-sym d)))
Ω1ᴱ (lim g s) = lim-rᴱ 0 (up-rᴱ {r = self 0} (Ω1ᴱ (g 0)))

NZ : Ordᴵ → Set
NZ zero      = ⊥
NZ (suc _)   = ⊤
NZ (lim _ _) = ⊤

record AFl {ℓ} (a : Ordˢ ℓ) : Set where
  constructor afl
  field
    ea  : a ≅ˢ a
    one : 𝟏 ⊑ᴱ a
    nzA : NZ ℓ

record WFl {c φ} (W : O c φ) : Set where
  constructor wfl
  field
    rW   : Rᵒ c W W
    oneW : 𝟏ᵀ ⊑ᵀ W

Ctx  : ∀ {k} → Obs k → Set
Ctxᶜ : ∀ {c φ} → Cx c φ → Set
Ctx idO          = ⊤
Ctx (tlo C)      = Ctxᶜ C
Ctx (addo O a σ) = AFl a × Ctx O
Ctx (tro O e)    = Ctx O
Ctx (tr⁻o O e)   = Ctx O
Ctxᶜ (top O ev p) = Ctx O
Ctxᶜ (pa W C)     = WFl W × Ctxᶜ C
Ctxᶜ (pψ q C)     = Ctxᶜ C
Ctxᶜ (pι q C)     = Ctxᶜ C

ctx-refl  : ∀ {k} (O : Obs k) → Ctx O → O ≈ᵒ O
ctxᶜ-refl : ∀ {c φ} (C : Cx c φ) → Ctxᶜ C → C ≈ᶜ C
ctx-refl idO _ = idO
ctx-refl (tlo C) c = tlo (ctxᶜ-refl C c)
ctx-refl (addo O a σ) (afl e _ _ , c) = addo (ctx-refl O c) (≅ᴵ-refl _) e
ctx-refl (tro O e) c = tro (ctx-refl O c)
ctx-refl (tr⁻o O e) c = tr⁻o (ctx-refl O c)
ctxᶜ-refl (top O ev p) c = top (ctx-refl O c)
ctxᶜ-refl (pa W C) (w , c) = pa (WFl.rW w) (ctxᶜ-refl C c)
ctxᶜ-refl (pψ q C) c = pψ (ctxᶜ-refl C c)
ctxᶜ-refl (pι q C) c = pι (ctxᶜ-refl C c)

⊑ᴱ-≅ˡ : ∀ {k k′} {x x′ : Ordˢ k} {y : Ordˢ k′} → x ≅ˢ x′ → x′ ⊑ᴱ y → x ⊑ᴱ y
⊑ᴱ-≅ˡ e h o G′ = proj₁ (≅→⊑ᴱ e (≈ᵒ-reflˡ o) (proj₁ (h o G′))) ,
                 ⊑-trans (proj₂ (≅→⊑ᴱ e (≈ᵒ-reflˡ o) (proj₁ (h o G′)))) (proj₂ (h o G′))

suc-iter : ∀ {ℓ} {w : Ordˢ ℓ} → w ≅ˢ w → 𝟏 ⊑ᴱ w → Ord₊ˢ.suc w ⊑ᴱ Ord₊ˢ.lim (iter (w +ˢ_) Ord₊ˢ.zero)
suc-iter {w = w} ew one =
  lim-rᴱ {h = iter (w +ˢ_) Ord₊ˢ.zero} 2
    (add-congᴱ {a = w} {a′ = w} {σ = σ₀} {σ′ = λ q → q} {x = 𝟏} {y = w} (≅ᴵ-refl _) ew one)

S1ᵀ : ∀ {c φ i ℓ} {t : O c φ} {ev : Ev ℓ φ} {p : i <ᴵ ℓ} → 𝟏ᵀ ⊑ᵀ t → Ord₊ˢ.suc (Ωˢ i) ⊑ᴱ ψ̄ t ev p
S1ᵀ {i = i} {t = t} {ev = ev} {p = p} h =
  ⊑ᴱ-trans (suc-iter {w = Ωˢ i} (Ωˢ-refl i) (Ω1ᴱ i)) (ψ̄-cong {x = 𝟏ᵀ} {y = t} {ev = tt} {ev′ = ev} {p = p} {p′ = p} h)

𝟏⊑Ω̇ : ∀ m → 𝟏ᵀ {m} ⊑ᵀ Ω̇ m
𝟏⊑Ω̇ zero = clo-rᵀ (oi-rᵀ (λ z d → wk-rᵀ (tl-cong {x = 𝟏} {y = z} (⊑ᴱ-≅ʳ (Ω1ᴱ zero) (≅ˢ-sym d)))))
𝟏⊑Ω̇ (suc m) = Ω-rᵀ (λ ξ z rz f → wk-rᵀ (ι-cong {q = zero} {x = 𝟏ᵀ {m}} {y = z} (f (𝟏⊑Ω̇ m))))
```

## §2 严格关系

`Sᵛ`, `Sᵀ`: $a$ 严格低于 $a+1$, 对一切上下文, 不要 `Ctx`.

```agda
infix 4 _≺ᴱ_ _≺ᵀ_
_≺ᴱ_ : ∀ {k k′} → Ordˢ k → Ordˢ k′ → Set
_≺ᴱ_ {k} {k′} x y = ∀ {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → Ctx O′ → (G′ : Goodᴺ (toZ (run O′ y))) →
  Σ (Goodᴺ (toZ (run O x))) λ G → forceᴺ _ G ≺ forceᴺ _ G′

_≺ᵀ_ : ∀ {c φ ψ} → O c φ → O c ψ → Set
_≺ᵀ_ {c} {φ} {ψ} x y = ∀ {C : Cx c φ} {C′ : Cx c ψ} → C ≈ᶜ C′ → Ctxᶜ C′ → (G′ : Goodᴺ (toZ (runᶜ C′ y))) →
  Σ (Goodᴺ (toZ (runᶜ C x))) λ G → forceᴺ _ G ≺ forceᴺ _ G′

Sᵛ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} {a : Ordˢ k} {a′ : Ordˢ k′} → O ≈ᵒ O′ → a ≅ˢ a′ → a′ ≅ˢ a′ →
     (G′ : Goodᴺ (toZ (run O′ (Ord₊ˢ.suc a′)))) → Σ (Goodᴺ (toZ (run O a))) λ G → forceᴺ _ G ≺ forceᴺ _ G′
Sᵀ : ∀ {c φ ψ χ} {C : Cx c φ} {C′ : Cx c ψ} {a : O c φ} {a′ : O c χ} → C ≈ᶜ C′ → (L : ∀ {ℓ} → Ev ℓ ψ → Ev ℓ χ) → Rᵒ c a a′ → Rᵒ c a′ a′ →
     (G′ : Goodᴺ (toZ (runᶜ (wkC L C′) (os a′)))) → Σ (Goodᴺ (toZ (runᶜ C a))) λ G → forceᴺ _ G ≺ forceᴺ _ G′
Sᵛ idO d d′ (gs H) = Goodᴺ-tr (≅ᶻ-sym (toZ-≅ d)) H , ≺z (forceᴺ-≅ (toZ-≅ d) (Goodᴺ-tr (≅ᶻ-sym (toZ-≅ d)) H) H)
Sᵛ {k′ = k′} {a′ = a′} (tlo {C′ = C′} o) d d′ G′ =
  let J = pull≡ (cong (λ D → runᶜ D (os (tl (flo k′) (cvFlo k′) a′))) (wkC-id C′)) G′
      K = Sᵀ o (λ e → e) (R-tl d) (R-tl d′) (proj₁ J)
  in proj₁ K , proj₂ J (proj₂ K)
Sᵛ (addo o k ee) d d′ G′ = Sᵛ o (addˢ-≅ k ee d) (addˢ-≅ (≅ᴵ-refl _) (≅ˢ-reflʳ ee) d′) G′
Sᵛ (tro {e = e} {e′ = e′} o) d d′ G′ = Sᵛ o (trˢ-≅ e (≅-trˢ e′ d)) (self-trˢ e′ d′) G′
Sᵛ (tr⁻o {e = e} {e′ = e′} o) d d′ G′ = Sᵛ o (tr⁻ˢ-≅ e (≅-tr⁻ˢ e′ d)) (self-tr⁻ˢ e′ d′) G′
Sᵀ {a = a} {a′ = a′} (top {i = i} {O = O} {O′ = O′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o) L ra ra′ G′ =
  proj₁ K , proj₂ J (proj₂ K)
  where
  w′ = ψ̄ a′ (L ev′) p′
  J = suc-iter {w = w′} (R→≈ ra′ _ _ _ _ (≅ᴵ-refl i)) (⊑ᴱ-trans (Ω1ᴱ i) (F0ᵀ ra′)) (≈ᵒ-reflʳ o) G′
  K = Sᵛ o (R→≈ ra ev p (L ev′) p′ (≅ᴵ-refl i)) (R→≈ ra′ _ _ _ _ (≅ᴵ-refl i)) (proj₁ J)
Sᵀ {a = a} {a′ = a′} (pa {a = α} {W = W} rW o) L ra ra′ G′ =
  Sᵀ o (λ e → proj₁ e , L (proj₂ e)) (R-⊕ (∼ᶠ-refl α) rW ra) (R-⊕ (∼ᶠ-refl α) rW ra′) G′
Sᵀ {χ = χ} {a = a} {a′ = a′} (pψ {q = q} {C = C₁} {C′ = C₁′} o) L ra ra′ G′ =
  proj₁ K , proj₂ J (proj₂ K)
  where
  X = ψᵒ q a′
  rX = R-ψ q q ra′
  M : ∀ {ℓ} → Ev ℓ _ → Ev ℓ (Fl ⊔ χ)
  M e = proj₁ e , L (proj₂ e)
  N : ∀ {ℓ} → Ev ℓ _ → Ev ℓ ((Fl ⊔ χ) ⊔ fz)
  N e = M e , tt
  J = lim-rᵀ {x = X ⊕ 𝟏ᵀ} {F = repᵒ X} 2 (wk-rᵀ (⊕-cong rX (P0ᵀ {q = q} ra′ (𝟏⊑Ω̇ _))))
             {C = wkC N C₁′} {C′ = wkC M C₁′} (≈ᶜ-wkˡ N (≈ᶜ-wkʳ M (≈ᶜ-reflʳ o))) G′
  K = Sᵀ {a = ψᵒ q a} {a′ = owk proj₁ X} o N (rwkʳ (R-ψ q q ra)) (rwk rX) (proj₁ J)
Sᵀ {a = a} {a′ = a′} (pι {q = q} o) L ra ra′ G′ = Sᵀ o L (R-ι q ra) (R-ι q ra′) G′

Rs : ∀ {k k′} {a : Ordˢ k} {y : Ordˢ k′} → a ≅ˢ a → Ord₊ˢ.suc a ⊑ᴱ y → a ≺ᴱ y
Rs ea sa o c G′ = proj₁ K , proj₂ J (proj₂ K)
  where
  J = sa o G′
  K = Sᵛ (≈ᵒ-reflˡ o) ea ea (proj₁ J)

Rsᵀ : ∀ {c φ ψ} {a : O c φ} {y : O c ψ} → Rᵒ c a a → os a ⊑ᵀ y → a ≺ᵀ y
Rsᵀ {a = a} ra sa {C = C} o c G′ = proj₁ K , proj₂ I (proj₂ J (proj₂ K))
  where
  I = sa o G′
  J = pull≡ (cong (λ D → runᶜ D (os a)) (wkC-id C)) (proj₁ I)
  K = Sᵀ (≈ᶜ-reflˡ o) (λ e → e) ra ra (proj₁ J)
```

## §3 `Climb`

对节点 $j$ 的 `limᵢ q f`/`oi ac f`: 若 "$z\sqsupseteq\Omega_j+1$ 推出 $x\prec f\,z$", 则 $x$ 严格低于这个节点. 严格关系对上下文量化, 所以穿过 $W\oplus$, $\psi$, $\iota$ 时 $h_2$ 不用搬: 换上下文就行. 第一个折叠节点取链的第 1 点, `S1ᵀ` 给 $z_1\sqsupseteq\Omega_j+1$.

```agda
back-sucᴱ : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} → u ≅ˢ u → Ord₊ˢ.suc (Ωˢ (repˢ (resˢ q e))) ⊑ᴱ u → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ backˢ (resˢ q e) u
back-sucᴱ {j} zero (s≅ e) eu h = ⊑ᴱ-≅ˡ {x′ = tr⁻ˢ e (Ord₊ˢ.suc (Ωˢ _))} (s≅ (≅ᴵ-refl _) (≅ˢ-sym (tr⁻ˢ-≅ e (Ωˢ-≅ (≅ᴵ-sym e))))) (tr⁻-congᴱ {e = e} {e′ = e} h)
back-sucᴱ (suc q)   (s≅ e) eu h = back-sucᴱ q e eu h
back-sucᴱ (lim n q) (l≅ f) eu h = back-sucᴱ q (f n) eu h

back⁻-sucᴱ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} → u ≅ˢ u → Ord₊ˢ.suc (Ωˢ (repˢ (res⁻ˢ q e))) ⊑ᴱ u → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ backˢ (res⁻ˢ q e) u
back⁻-sucᴱ {j} zero (s≅ e) eu h = ⊑ᴱ-≅ˡ {x′ = trˢ e (Ord₊ˢ.suc (Ωˢ _))} (s≅ (≅ᴵ-refl _) (≅ˢ-sym (trˢ-≅ e (Ωˢ-≅ e)))) (tr-congᴱ {e = e} {e′ = e} h)
back⁻-sucᴱ (suc q)   (s≅ e) eu h = back⁻-sucᴱ q e eu h
back⁻-sucᴱ (lim n q) (l≅ f) eu h = back⁻-sucᴱ q (f n) eu h

chainCᵀ : ∀ {c χ φ j i ℓ ℓ′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {f : Ordˢ j → O c φ} {x : O c χ} {ev : Ev ℓ χ} {ev′ : Ev ℓ′ φ} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} →
        (∀ {z z′} → z ≅ˢ z′ → Rᵒ c (f z) (f z′)) →
        (∀ z → z ≅ˢ Ωˢ j → 𝟏ᵀ ⊑ᵀ f z) →
        (∀ z → z ≅ˢ z → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ z → x ≺ᵀ f z) →
        ∀ {O O′ : Obs i} → O ≈ᵒ O′ → Ctx O′ →
        (G′ : Goodᴺ (toZ (run O′ (Ord₊ˢ.lim (λ m → ψ̄ (f (iter (λ w → ψ̄ (f w) ev′ (ac ev′)) (Ωˢ j) m)) ev′ p′))))) →
        Σ (Goodᴺ (toZ (run O (ψ̄ x ev p)))) λ G → forceᴺ _ G ≺ forceᴺ _ G′
chainCᵀ {j = j} {ac = ac} {f = f} {x = x} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} rf h1 h2 {O} {O′} o c G′ =
  proj₁ S , proj₂ L (proj₂ S)
  where
  z₁ = ψ̄ (f (Ωˢ j)) ev′ (ac ev′)
  ez₁ : z₁ ≅ˢ z₁
  ez₁ = R→≈ (rf (Ωˢ-refl j)) ev′ (ac ev′) ev′ (ac ev′) (≅ᴵ-refl j)
  sz₁ : Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ z₁
  sz₁ = S1ᵀ (h1 _ (Ωˢ-refl j))
  y₁ = ψ̄ (f z₁) ev′ p′
  ey₁ : y₁ ≅ˢ y₁
  ey₁ = R→≈ (rf ez₁) ev′ p′ ev′ p′ (≅ᴵ-refl _)
  L = lim-rᴱ {h = λ m → ψ̄ (f (iter (λ w → ψ̄ (f w) ev′ (ac ev′)) (Ωˢ j) m)) ev′ p′} 1 (≅→⊑ᴱ {x = y₁} ey₁) (≈ᵒ-reflʳ o) G′
  S = h2 z₁ ez₁ sz₁ (top {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o) c (proj₁ L)

Climbᵛ : ∀ {k k₀ j} {q : j <ᴵ k} {g : Uˢ j (<→◃ q) → Ordˢ k} {x : Ordˢ k₀} →
        (∀ {z z′} → z ≅ˢ z′ → g (intoˢ (<→◃ q) z) ≅ˢ g (intoˢ (<→◃ q) z′)) →
        (∀ z → z ≅ˢ Ωˢ j → 𝟏 ⊑ᴱ g (intoˢ (<→◃ q) z)) →
        (∀ z → z ≅ˢ z → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ z → x ≺ᴱ g (intoˢ (<→◃ q) z)) → x ≺ᴱ Ord₊ˢ.limᵢ q g
Climbᵀ : ∀ {c χ φ j} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {f : Ordˢ j → O c φ} {x : O c χ} →
        (∀ {z z′} → z ≅ˢ z′ → Rᵒ c (f z) (f z′)) →
        (∀ z → z ≅ˢ Ωˢ j → 𝟏ᵀ ⊑ᵀ f z) →
        (∀ z → z ≅ˢ z → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ z → x ≺ᵀ f z) → x ≺ᵀ oi ac f
Climbᵛ {q = ()} rf h1 h2 idO c G′
Climbᵛ {k = k} {k₀ = k₀} {q = q} {g = g} {x = x} rf h1 h2 (tlo o) c G′ =
  Climbᵀ {ac = λ e → cvFlo k e q} {f = λ y → tl (flo k) (cvFlo k) (g (intoˢ (<→◃ q) y))} {x = tl (flo k₀) (cvFlo k₀) x}
    (λ d → R-tl (rf d)) (λ z d → tl-cong (h1 z d)) (λ z ez sz o′ c′ G → h2 z ez sz (tlo o′) c′ G) o c G′
Climbᵛ {k = k} {j = j} {q = q} {g = g} {x = x} rf h1 h2 (addo {a = e} {a′ = e′} {σ = σ} {σ′ = σ′} o kk ee) (afl e₁ one nzA , c) G′ =
  Climbᵛ {q = σ′ q} {g = λ u → addˢ e′ σ′ (g (intoˢ (<→◃ q) (outˢ (<→◃ (σ′ q)) u)))} {x = addˢ e σ x}
    (λ {z} {z′} d → subst₂ (λ u v → addˢ e′ σ′ (g (intoˢ (<→◃ q) u)) ≅ˢ addˢ e′ σ′ (g (intoˢ (<→◃ q) v)))
                           (sym (out-intoˢ (<→◃ (σ′ q)) z)) (sym (out-intoˢ (<→◃ (σ′ q)) z′)) (addˢ-≅ (≅ᴵ-refl _) e₁ (rf d)))
    (λ z d → subst (λ u → 𝟏 ⊑ᴱ addˢ e′ σ′ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ′ q)) z))
                   (add-floorᴱ {σ = σ′} (g (intoˢ (<→◃ q) z)) one (rf (≅ˢ-reflˡ d))))
    (λ z ez sz → subst (λ u → addˢ e σ x ≺ᴱ addˢ e′ σ′ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ′ q)) z))
                       (λ o′ c′ G → h2 z ez sz (addo o′ kk ee) (afl e₁ one nzA , c′) G))
    o c G′
Climbᵛ {k = k} {q = q} {g = f} {x = x} rf h1 h2 (tro {e = e₀} {e′ = e} o) c G′ =
  Climbᵛ {q = ltˢ (resˢ q e)} {g = λ u → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) (outˢ (<→◃ (ltˢ (resˢ q e))) u))))} {x = trˢ e₀ x}
    (λ {z} {z′} d → subst₂ (λ u v → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) u))) ≅ˢ trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) v))))
       (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z′)) (trˢ-≅ e (≅-trˢ e (rf (≅ˢ-trans (backˢ-≅ q e d) (≅ˢ-sym (backˢ-≅ q e (≅ˢ-reflʳ d))))))))
    (λ z d → subst (λ u → 𝟏 ⊑ᴱ trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) u)))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z))
       (tr-congᴱ {e = z≅} {e′ = e} (h1 _ (≅ˢ-trans (backˢ-≅ q e d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (resˢ q e))))))))
    (λ z ez sz → subst (λ u → trˢ e₀ x ≺ᴱ trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) u)))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z))
       (λ o′ c′ G → h2 _ (≅ˢ-reflˡ (backˢ-≅ q e ez)) (back-sucᴱ q e ez sz) (tro {e = e₀} {e′ = e} o′) c′ G))
    o c G′
Climbᵛ {k = k} {q = q} {g = f} {x = x} rf h1 h2 (tr⁻o {e = e₀} {e′ = e} o) c G′ =
  Climbᵛ {q = ltˢ (res⁻ˢ q e)} {g = λ u → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) (outˢ (<→◃ (ltˢ (res⁻ˢ q e))) u))))} {x = tr⁻ˢ e₀ x}
    (λ {z} {z′} d → subst₂ (λ u v → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) u))) ≅ˢ tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) v))))
       (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z′)) (tr⁻ˢ-≅ e (≅-tr⁻ˢ e (rf (≅ˢ-trans (back⁻ˢ-≅ q e d) (≅ˢ-sym (back⁻ˢ-≅ q e (≅ˢ-reflʳ d))))))))
    (λ z d → subst (λ u → 𝟏 ⊑ᴱ tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) u)))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z))
       (tr⁻-congᴱ {e = z≅} {e′ = e} (h1 _ (≅ˢ-trans (back⁻ˢ-≅ q e d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (res⁻ˢ q e))))))))
    (λ z ez sz → subst (λ u → tr⁻ˢ e₀ x ≺ᴱ tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) u)))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z))
       (λ o′ c′ G → h2 _ (≅ˢ-reflˡ (back⁻ˢ-≅ q e ez)) (back⁻-sucᴱ q e ez sz) (tr⁻o {e = e₀} {e′ = e} o′) c′ G))
    o c G′
Climbᵀ {j = j} {ac = ac} {f = f} {x = x} rf h1 h2 (top {i = i} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o) c G′ with <ᴵ-dec (ac ev′) p′
... | injᵃ (via e s) =
  Climbᵛ {q = s} {g = λ u → ψ̄ (f (tr⁻ˢ e (outˢ (<→◃ s) u))) ev′ p′} {x = ψ̄ x ev p}
    (λ {z} {z′} d → subst₂ (λ u v → ψ̄ (f (tr⁻ˢ e u)) ev′ p′ ≅ˢ ψ̄ (f (tr⁻ˢ e v)) ev′ p′)
                           (sym (out-intoˢ (<→◃ s) z)) (sym (out-intoˢ (<→◃ s) z′))
                           (R→≈ (rf (tr⁻ˢ-≅ e (≅-tr⁻ˢ e d))) ev′ p′ ev′ p′ (≅ᴵ-refl _)))
    (λ z d → subst (λ u → 𝟏 ⊑ᴱ ψ̄ (f (tr⁻ˢ e u)) ev′ p′) (sym (out-intoˢ (<→◃ s) z))
                   (⊑ᴱ-trans (Ω1ᴱ i) (F0ᵀ (rf (self-tr⁻ˢ e (≅ˢ-reflˡ d))))))
    (λ z ez sz → subst (λ u → ψ̄ x ev p ≺ᴱ ψ̄ (f (tr⁻ˢ e u)) ev′ p′) (sym (out-intoˢ (<→◃ s) z))
                       (λ o′ c′ G → h2 (tr⁻ˢ e z) (self-tr⁻ˢ e ez)
                                     (⊑ᴱ-≅ˡ {x′ = tr⁻ˢ e (Ord₊ˢ.suc (Ωˢ _))} (s≅ (≅ᴵ-refl _) (≅ˢ-sym (tr⁻ˢ-≅ e (Ωˢ-≅ (≅ᴵ-sym e))))) (tr⁻-congᴱ {e = e} {e′ = e} sz))
                                     (top o′) c′ G))
    o c G′
... | injᵇ _ = chainCᵀ {j = j} {ac = ac} {f = f} {x = x} rf h1 h2 o c G′
... | injᶜ _ = chainCᵀ {j = j} {ac = ac} {f = f} {x = x} rf h1 h2 o c G′
Climbᵀ {ac = ac} {f = f} {x = x} rf h1 h2 (pa {a = α} {W = W} rW o) (w , c) G′ =
  Climbᵀ {ac = λ e → ac (proj₂ e)} {f = λ y → W ⊕ f y} {x = W ⊕ x}
    (λ d → R-⊕ (∼ᶠ-refl α) rW (rf d))
    (λ z d → B1ᵀ (rf (≅ˢ-reflˡ d)) (WFl.oneW w))
    (λ z ez sz o′ c′ G → h2 z ez sz (pa rW o′) (w , c′) G)
    o c G′
Climbᵀ {ac = ac} {f = f} {x = x} rf h1 h2 (pψ {t = t} {q = q} o) c G′ =
  Climbᵀ {ac = λ e → ac (proj₂ e)} {f = λ y → ψᵒ q (f y)} {x = ψᵒ q x}
    (λ d → R-ψ q q (rf d))
    (λ z d → P0ᵀ {q = q} (rf (≅ˢ-reflˡ d)) (𝟏⊑Ω̇ t))
    (λ z ez sz o′ c′ G → h2 z ez sz (pψ {q = q} o′) c′ G)
    o c G′
Climbᵀ {ac = ac} {f = f} {x = x} rf h1 h2 (pι {q = q} o) c G′ =
  Climbᵀ {ac = ac} {f = λ y → ι q (f y)} {x = ι q x}
    (λ d → R-ι q (rf d))
    (λ z d → ι-cong {q = q} (h1 z d))
    (λ z ez sz o′ c′ G → h2 z ez sz (pι {q = q} o′) c′ G)
    o c G′
```

## §4 $\Omega_j\prec\Omega_{j+1}$, 读数

```agda
Ω-strict : ∀ j → Ωˢ j ≺ᴱ Ωˢ (suc j)
Ω-strict j = Climbᵛ {q = zero} {g = Ord₊ˢ.up zero} {x = Ωˢ j} (λ d → upˡ {r = zero} (upʳ {r = zero} d))
                   (λ z d → up-rᴱ {r = zero} {y = z} (⊑ᴱ-≅ʳ (Ω1ᴱ j) (≅ˢ-sym d)))
                   (λ z ez sz → Rs (Ωˢ-refl j) (up-rᴱ {r = zero} {y = z} sz))

Ω<ᴱ : ∀ {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → Ωˢ (suc a) ⊑ᴱ Ωˢ b
Ω<ᴱ e zero      = ≅→⊑ᴱ (Ωˢ-≅ (s≅ e))
Ω<ᴱ e (suc q)   = limᵢ-rᴱ (λ z d → up-rᴱ {r = zero} {y = z} (⊑ᴱ-≅ʳ (Ω<ᴱ e q) (≅ˢ-sym d)))
Ω<ᴱ e (lim n q) = lim-rᴱ n (up-rᴱ {r = self n} (Ω<ᴱ e q))
```
