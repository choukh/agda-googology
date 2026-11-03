# 层号参数化的无符号闭包定理 (二): 保存在性前序

> 由 [UniformNF4Rules](UniformNF4Rules.lagda.md) 经脚本移植到 `Ordᴵ` 层号. 差别: `ptr`, `ptr⁻` 两行 (由 `pι` 行生成); `FlΩ̇` 带 $x$ 的自相关, 这样地板能沿层号搬运 (§3′); `Ω-rᵀ`, `P0ᵀ` 读三歧 `<ᴵ-dec`; `B1ᵀ`, `F0ᵀ`, `P0ᵀ` 的输入在右侧层号上取 `trO ek z`, 因为 `Rᵒ` 跨层.
>
> 接 [UniformNF5Base](UniformNF5Base.lagda.md). 结论先说:
>
> 1. **两层前序, 一套规则.** 值层 `⊑ᴱ` 由 [UniformNF3D1G](UniformNF3D1G.lagda.md) §1–§2 改写: `fo`/`fo1` 的子句换成一个 `tlo` 子句, 交给树层规则; 树层 `⊑ᵀ` 的 `top` 子句交回值层. 两层互递归, 只沿上下文走.
> 2. **`clo-rᵀ` 要带累积的弱化.** $W\oplus$ 与 $\psi$ 把 `oclo` 变成 `owk asl (oclo …)`, 所以走上下文时头上有 `owk`. 这是全文唯一要累积 `L` 的规则, `wkC-comp` 把它压成一个.
> 3. **`B1ᵀ`: $W\sqsubseteq W\oplus t$, 对 `Rᵒ` 的推导归纳**, 不反演 `Rᵒ x x`. `F0ᵀ`: $\Omega_i\sqsubseteq\bar\psi\,x$, `P0ᵀ`: $\Omega_{\Omega+t}\sqsubseteq\psi_{\Omega+t}\,x$, 空前缀的地板对一切树成立, 不要 `PFl`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF5Rules where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ; Ωˢ; addˢ; _+ˢ_)
open Restrˢ
open import OCF.Align.UniformNF3Eq using (kd; ≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; upˡ; upʳ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ;
  trˢ-≅; tr⁻ˢ-≅; backˢ-≅; back⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; addˢ-≅; s-invˢ; l-invˢ; i-respˢ; u-reflˢ; ŝ-refl₀; ĉ-refl₀; self-trˢ; self-tr⁻ˢ; 𝟎ˢ)
open import OCF.Align.Uniform3Base using (_∼ᶠ_; ∼ᶠ-refl; Flr; fz; fk; Ev; Run; flo; cvFlo; toFlo; ∅ᴿ; _⊔_; cloA; limᵢA; Bd; bound)
open import OCF.Align.NotFree using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3NBase using (Goodᴺ-tr)
open import OCF.Align.Uniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.Uniform4Two
open RestrO
open import OCF.Align.UniformNF5Base
```

## §1 两个前序

```agda
infix 4 _⊑ᴱ_ _⊑ᵀ_
_⊑ᴱ_ : ∀ {k k′} → Ordˢ k → Ordˢ k′ → Set
_⊑ᴱ_ {k} {k′} x y = ∀ {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → (G′ : Goodᴺ (toZ (run O′ y))) →
  Σ (Goodᴺ (toZ (run O x))) λ G → forceᴺ _ G ⊑ forceᴺ _ G′

_⊑ᵀ_ : ∀ {c φ ψ} → O c φ → O c ψ → Set
_⊑ᵀ_ {c} {φ} {ψ} x y = ∀ {C : Cx c φ} {C′ : Cx c ψ} → C ≈ᶜ C′ → (G′ : Goodᴺ (toZ (runᶜ C′ y))) →
  Σ (Goodᴺ (toZ (runᶜ C x))) λ G → forceᴺ _ G ⊑ forceᴺ _ G′

pull≡ : ∀ {u v : Ordˢ zero} → u ≡ v → (G′ : Goodᴺ (toZ v)) → Σ (Goodᴺ (toZ u)) λ G → forceᴺ _ G ⊑ forceᴺ _ G′
pull≡ refl G′ = G′ , (λ h → h)

≅→⊑ᴱ : ∀ {k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ≅ˢ y → x ⊑ᴱ y
≅→⊑ᴱ e o G′ = Goodᴺ-tr (≅ᶻ-sym d) G′ , ≅→⊑ (forceᴺ-≅ d (Goodᴺ-tr (≅ᶻ-sym d) G′) G′)
  where d = toZ-≅ (run-≅ o e)

R→⊑ᵀ : ∀ {c φ ψ} {x : O c φ} {y : O c ψ} → Rᵒ c c x y → x ⊑ᵀ y
R→⊑ᵀ e o G′ = Goodᴺ-tr (≅ᶻ-sym d) G′ , ≅→⊑ (forceᴺ-≅ d (Goodᴺ-tr (≅ᶻ-sym d) G′) G′)
  where d = toZ-≅ (runᶜ-≅ o e)

⊑ᴱ-≅ʳ : ∀ {k k′} {x : Ordˢ k} {y y′ : Ordˢ k′} → x ⊑ᴱ y → y ≅ˢ y′ → x ⊑ᴱ y′
⊑ᴱ-≅ʳ h e o G′ = proj₁ (h o Gm) , ⊑-trans (proj₂ (h o Gm)) (≅→⊑ (forceᴺ-≅ d Gm G′))
  where
  d = toZ-≅ (run-≅ (≈ᵒ-reflʳ o) e)
  Gm = Goodᴺ-tr (≅ᶻ-sym d) G′

⊑ᵀ-Rʳ : ∀ {c φ ψ} {x : O c φ} {y : O c ψ} {y′ : O c ψ} → x ⊑ᵀ y → Rᵒ c c y y′ → x ⊑ᵀ y′
⊑ᵀ-Rʳ h e o G′ = proj₁ (h o Gm) , ⊑-trans (proj₂ (h o Gm)) (≅→⊑ (forceᴺ-≅ d Gm G′))
  where
  d = toZ-≅ (runᶜ-≅ (≈ᶜ-reflʳ o) e)
  Gm = Goodᴺ-tr (≅ᶻ-sym d) G′

⊑ᴱ-trans : ∀ {k k′} {x : Ordˢ k} {y w : Ordˢ k′} → x ⊑ᴱ y → y ⊑ᴱ w → x ⊑ᴱ w
⊑ᴱ-trans h i o G′ = proj₁ (h o Gm) , ⊑-trans (proj₂ (h o Gm)) (proj₂ (i (≈ᵒ-reflʳ o) G′))
  where Gm = proj₁ (i (≈ᵒ-reflʳ o) G′)

⊑ᵀ-trans : ∀ {c φ ψ} {x : O c φ} {y w : O c ψ} → x ⊑ᵀ y → y ⊑ᵀ w → x ⊑ᵀ w
⊑ᵀ-trans h i o G′ = proj₁ (h o Gm) , ⊑-trans (proj₂ (h o Gm)) (proj₂ (i (≈ᶜ-reflʳ o) G′))
  where Gm = proj₁ (i (≈ᶜ-reflʳ o) G′)

≅→⊑ᵀ : ∀ {c φ ψ} {x : O c φ} {y : O c ψ} → Rᵒ c c x y → x ⊑ᵀ y
≅→⊑ᵀ = R→⊑ᵀ
```

## §2 同余与弱化

```agda
add-congᴱ : ∀ {k k′ ℓ ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} {x : Ordˢ k} {y : Ordˢ k′} →
           ℓ ≅ᴵ ℓ′ → a ≅ˢ a′ → x ⊑ᴱ y → addˢ a σ x ⊑ᴱ addˢ a′ σ′ y
add-congᴱ k e h o = h (addo o k e)

tr-congᴱ : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordˢ a} {y : Ordˢ a′} → x ⊑ᴱ y → trˢ e x ⊑ᴱ trˢ e′ y
tr-congᴱ h o = h (tro o)

tr⁻-congᴱ : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordˢ b} {y : Ordˢ b′} → x ⊑ᴱ y → tr⁻ˢ e x ⊑ᴱ tr⁻ˢ e′ y
tr⁻-congᴱ h o = h (tr⁻o o)

ψ̄-cong : ∀ {c φ ψ i ℓ ℓ′} {x : O c φ} {y : O c ψ} {ev : Ev ℓ φ} {ev′ : Ev ℓ′ ψ} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} → x ⊑ᵀ y → ψ̄ x ev p ⊑ᴱ ψ̄ y ev′ p′
ψ̄-cong h o = h (top o)

tl-cong : ∀ {c k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ⊑ᴱ y → tl {c = c} (flo k) (cvFlo k) x ⊑ᵀ tl {c = c} (flo k′) (cvFlo k′) y
tl-cong h o = h (tlo o)

⊕-cong : ∀ {c a φ ψ} {W : O c a} {x : O c φ} {y : O c ψ} → Rᵒ c c W W → x ⊑ᵀ y → W ⊕ x ⊑ᵀ W ⊕ y
⊕-cong r h o = h (pa r o)

ψ-cong : ∀ {c t φ ψ} {q : t <ᴵ c} {x : O c φ} {y : O c ψ} → x ⊑ᵀ y → ψᵒ q x ⊑ᵀ ψᵒ q y
ψ-cong {q = q} h o = h (pψ {q = q} o)

ι-cong : ∀ {c d φ ψ} {q : c ◃ d} {x : O c φ} {y : O c ψ} → x ⊑ᵀ y → ι q x ⊑ᵀ ι q y
ι-cong {q = q} h o = h (pι {q = q} o)

trᵀ-cong : ∀ {a b φ ψ} {e e′ : a ≅ᴵ b} {x : O a φ} {y : O a ψ} → x ⊑ᵀ y → trO e x ⊑ᵀ trO e′ y
trᵀ-cong h o = h (ptr o)

tr⁻ᵀ-cong : ∀ {a b φ ψ} {e e′ : a ≅ᴵ b} {x : O b φ} {y : O b ψ} → x ⊑ᵀ y → tr⁻O e x ⊑ᵀ tr⁻O e′ y
tr⁻ᵀ-cong h o = h (ptr⁻ o)

wk-lᵀ : ∀ {c φ φ′ ψ} {le : ∀ {L} → Ev L φ′ → Ev L φ} {x : O c φ} {y : O c ψ} → x ⊑ᵀ y → owk le x ⊑ᵀ y
wk-lᵀ {le = le} {x = x} h {C} o G′ = proj₁ L , ⊑-trans (proj₂ L) (proj₂ (h (≈ᶜ-wkˡ le o) G′))
  where L = pull≡ (sym (run-wkC le C x)) (proj₁ (h (≈ᶜ-wkˡ le o) G′))

wk-rᵀ : ∀ {c χ φ ψ} {le : ∀ {L} → Ev L ψ → Ev L φ} {x : O c χ} {y : O c φ} → x ⊑ᵀ y → x ⊑ᵀ owk le y
wk-rᵀ {φ = φ} {ψ = ψ} {le = le} {y = y} h {C′ = C′} o G′ = proj₁ K , ⊑-trans (proj₂ K) (proj₂ L)
  where
  L = pull≡ (run-wkC le C′ y) G′
  K = h {C′ = wkC le C′} (≈ᶜ-wkʳ le o) (proj₁ L)
```

## §3 右引入规则

值层规则的 `tlo` 子句交给树层, 树层的 `top` 子句交回值层. `lim`, `suc`, `ŝ`, `ĉ`, `limᵢ`, `up` 的值层其余子句逐字取自 D1G.

```agda
lim-rᴱ : ∀ {k k′} {x : Ordˢ k} {h : ℕ → Ordˢ k′} n → x ⊑ᴱ h n → x ⊑ᴱ Ord₊ˢ.lim h
lim-rᵀ : ∀ {c φ ψ} {x : O c φ} {F : ℕ → O c ψ} n → x ⊑ᵀ F n → x ⊑ᵀ ol F
lim-rᴱ n p idO (gl G′ st) = proj₁ (p idO (G′ n)) , ⊑-lim n (proj₂ (p idO (G′ n)))
lim-rᴱ {k′ = k′} {h = h} n p (tlo o) = lim-rᵀ {F = λ m → tl (flo k′) (cvFlo k′) (h m)} n (tl-cong p) o
lim-rᴱ {h = h} n p (addo {a′ = a′} {σ′ = σ′} o k a) = lim-rᴱ {h = λ m → addˢ a′ σ′ (h m)} n (add-congᴱ k a p) o
lim-rᴱ {h = h} n p (tro {e′ = e′} o)  = lim-rᴱ {h = λ m → trˢ e′ (h m)} n (tr-congᴱ p) o
lim-rᴱ {h = h} n p (tr⁻o {e′ = e′} o) = lim-rᴱ {h = λ m → tr⁻ˢ e′ (h m)} n (tr⁻-congᴱ p) o
lim-rᵀ {x = x} {F = F} n p (top {ev = ev} {ev′ = ev′} {p = p₀} {p′ = p′} o) = lim-rᴱ {x = ψ̄ x ev p₀} {h = λ m → ψ̄ (F m) ev′ p′} n (ψ̄-cong p) o
lim-rᵀ {F = F} n p (pa {W = W} r o) = lim-rᵀ {F = λ m → W ⊕ F m} n (⊕-cong r p) o
lim-rᵀ {F = F} n p (pψ {q = q} o) = lim-rᵀ {F = λ m → ψᵒ q (F m)} n (ψ-cong {q = q} p) o
lim-rᵀ {F = F} n p (pι {q = q} o) = lim-rᵀ {F = λ m → ι q (F m)} n (ι-cong {q = q} p) o
lim-rᵀ {F = F} n p (ptr {e = e₀} {e′ = ε} o) = lim-rᵀ {F = λ m → trO ε (F m)} n (trᵀ-cong {e = e₀} {e′ = ε} p) o
lim-rᵀ {F = F} n p (ptr⁻ {e = e₀} {e′ = ε} o) = lim-rᵀ {F = λ m → tr⁻O ε (F m)} n (tr⁻ᵀ-cong {e = e₀} {e′ = ε} p) o

suc-rᴱ : ∀ {k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ⊑ᴱ y → x ⊑ᴱ Ord₊ˢ.suc y
suc-rᵀ : ∀ {c φ ψ} {x : O c φ} {y : O c ψ} → x ⊑ᵀ y → x ⊑ᵀ os y
suc-rᴱ p idO (gs G′) = proj₁ (p idO G′) , λ h → ≺s (proj₂ (p idO G′) h)
suc-rᴱ {k′ = k′} {y = y} p (tlo o) = suc-rᵀ {y = tl (flo k′) (cvFlo k′) y} (tl-cong p) o
suc-rᴱ {y = y} p (addo {a′ = a′} {σ′ = σ′} o k a) = suc-rᴱ {y = addˢ a′ σ′ y} (add-congᴱ k a p) o
suc-rᴱ {y = y} p (tro {e′ = e′} o)  = suc-rᴱ {y = trˢ e′ y} (tr-congᴱ p) o
suc-rᴱ {y = y} p (tr⁻o {e′ = e′} o) = suc-rᴱ {y = tr⁻ˢ e′ y} (tr⁻-congᴱ p) o
suc-rᵀ {x = x} {y = y} p (top {ev = ev} {ev′ = ev′} {p = p₀} {p′ = p′} o) = lim-rᴱ {x = ψ̄ x ev p₀} {h = iter (ψ̄ y ev′ p′ +ˢ_) Ord₊ˢ.zero} 1 (ψ̄-cong p) o
suc-rᵀ {y = y} p (pa {W = W} r o) = suc-rᵀ {y = W ⊕ y} (⊕-cong r p) o
suc-rᵀ {y = y} p (pψ {q = q} o) = lim-rᵀ {F = repᵒ (ψᵒ q y)} 1 (ψ-cong {q = q} p) o
suc-rᵀ {y = y} p (pι {q = q} o) = suc-rᵀ {y = ι q y} (ι-cong {q = q} p) o
suc-rᵀ {y = y} p (ptr {e = e₀} {e′ = ε} o) = suc-rᵀ {y = trO ε y} (trᵀ-cong {e = e₀} {e′ = ε} p) o
suc-rᵀ {y = y} p (ptr⁻ {e = e₀} {e′ = ε} o) = suc-rᵀ {y = tr⁻O ε y} (tr⁻ᵀ-cong {e = e₀} {e′ = ε} p) o

ĉ-rᵀ : ∀ {c φ ψ c₀ z} {zg : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {x : O c φ} {o₀ : O c ψ} {o : (η : Ordᴵ) → c₀ ⊑ᴵ η → O c ψ} → x ⊑ᵀ o₀ → x ⊑ᵀ oĉ c₀ z zg o₀ o
ŝ-rᵀ : ∀ {c φ ψ c₀} {x : O c φ} {t : O c ψ} {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → O c ψ} → x ⊑ᵀ t → x ⊑ᵀ oŝ c₀ t g
ŝ-rᴱ : ∀ {k k′ c} {x : Ordˢ k} {t₀ : Ordˢ k′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k′} → x ⊑ᴱ t₀ → x ⊑ᴱ Ord₊ˢ.ŝ c t₀ g
ĉ-rᴱ : ∀ {k k′ c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {x : Ordˢ k} {o₀ : Ordˢ k′} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k′} →
      x ⊑ᴱ o₀ → x ⊑ᴱ Ord₊ˢ.ĉᴸ c t₀ g o₀ o
ŝ-rᴱ {k′ = zero} p idO (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = proj₁ (p idO Go₀) , ⊑-lim 0 (proj₂ (p idO Go₀))
ŝ-rᴱ {k′ = zero} {c = c} {t₀ = t₀} {g = g} p (tlo o) =
  ĉ-rᵀ {c₀ = c} {z = toZ t₀} {zg = λ η e → toZ (g η e)} {o₀ = tl (flo zero) (cvFlo zero) t₀} {o = λ η e → tl (flo zero) (cvFlo zero) (g η e)} (tl-cong p) o
ŝ-rᴱ {k′ = suc k₁} {c = c} {t₀ = t₀} {g = g} p (tlo o) =
  ŝ-rᵀ {c₀ = c} {t = tl (flo (suc k₁)) (cvFlo (suc k₁)) t₀} {g = λ η e → tl (flo (suc k₁)) (cvFlo (suc k₁)) (g η e)} (tl-cong p) o
ŝ-rᴱ {k′ = lim f s} {c = c} {t₀ = t₀} {g = g} p (tlo o) =
  ŝ-rᵀ {c₀ = c} {t = tl (flo (lim f s)) (cvFlo (lim f s)) t₀} {g = λ η e → tl (flo (lim f s)) (cvFlo (lim f s)) (g η e)} (tl-cong p) o
ŝ-rᴱ {k′ = zero} {c = c} {t₀ = t₀} {g = g} p (addo {a′ = a′} {σ′ = σ′} o k a) =
  ĉ-rᴱ {c = c} {t₀ = toZ t₀} {g = λ η e → toZ (g η e)} {o₀ = addˢ a′ σ′ t₀} {o = λ η e → addˢ a′ σ′ (g η e)} (add-congᴱ k a p) o
ŝ-rᴱ {k′ = suc _} {c = c} {t₀ = t₀} {g = g} p (addo {a′ = a′} {σ′ = σ′} o k a) =
  ŝ-rᴱ {c = c} {t₀ = addˢ a′ σ′ t₀} {g = λ η e → addˢ a′ σ′ (g η e)} (add-congᴱ k a p) o
ŝ-rᴱ {k′ = lim _ _} {c = c} {t₀ = t₀} {g = g} p (addo {a′ = a′} {σ′ = σ′} o k a) =
  ŝ-rᴱ {c = c} {t₀ = addˢ a′ σ′ t₀} {g = λ η e → addˢ a′ σ′ (g η e)} (add-congᴱ k a p) o
ŝ-rᴱ {c = c} {t₀ = t₀} {g = g} p (tro {e′ = e′} o)  = ŝ-rᴱ {c = c} {t₀ = trˢ e′ t₀} {g = λ η d → trˢ e′ (g η d)} (tr-congᴱ p) o
ŝ-rᴱ {c = c} {t₀ = t₀} {g = g} p (tr⁻o {e′ = e′} o) = ŝ-rᴱ {c = c} {t₀ = tr⁻ˢ e′ t₀} {g = λ η d → tr⁻ˢ e′ (g η d)} (tr⁻-congᴱ p) o
ĉ-rᴱ p idO (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = proj₁ (p idO Go₀) , ⊑-lim 0 (proj₂ (p idO Go₀))
ĉ-rᴱ {k′ = k′} {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (tlo o′) =
  ĉ-rᵀ {c₀ = c} {z = t₀} {zg = g} {o₀ = tl (flo k′) (cvFlo k′) o₀} {o = λ η e → tl (flo k′) (cvFlo k′) (o η e)} (tl-cong p) o′
ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (addo {a′ = a′} {σ′ = σ′} o′ k a) =
  ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = addˢ a′ σ′ o₀} {o = λ η e → addˢ a′ σ′ (o η e)} (add-congᴱ k a p) o′
ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (tro {e′ = e′} o′) =
  ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = trˢ e′ o₀} {o = λ η d → trˢ e′ (o η d)} (tr-congᴱ p) o′
ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (tr⁻o {e′ = e′} o′) =
  ĉ-rᴱ {c = c} {t₀ = t₀} {g = g} {o₀ = tr⁻ˢ e′ o₀} {o = λ η d → tr⁻ˢ e′ (o η d)} (tr⁻-congᴱ p) o′
ŝ-rᵀ {c₀ = c₀} {x = x} {t = t} {g = g} p (top {ev = ev} {ev′ = ev′} {p = p₀} {p′ = p′} o) = ŝ-rᴱ {c = c₀} {x = ψ̄ x ev p₀} {t₀ = ψ̄ t ev′ p′} {g = λ η e → ψ̄ (g η e) ev′ p′} (ψ̄-cong p) o
ŝ-rᵀ {c₀ = c₀} {t = t} {g = g} p (pa {W = W} r o) = ŝ-rᵀ {c₀ = c₀} {t = W ⊕ t} {g = λ η e → W ⊕ g η e} (⊕-cong r p) o
ŝ-rᵀ {c₀ = c₀} {t = t} {g = g} p (pψ {q = q} o) = ŝ-rᵀ {c₀ = c₀} {t = ψᵒ q t} {g = λ η e → ψᵒ q (g η e)} (ψ-cong {q = q} p) o
ŝ-rᵀ {c₀ = c₀} {t = t} {g = g} p (pι {q = q} o) = ŝ-rᵀ {c₀ = c₀} {t = ι q t} {g = λ η e → ι q (g η e)} (ι-cong {q = q} p) o
ŝ-rᵀ {c₀ = c₀} {t = t} {g = g} p (ptr {e = e₀} {e′ = ε} o) = ŝ-rᵀ {c₀ = c₀} {t = trO ε t} {g = λ η e → trO ε (g η e)} (trᵀ-cong {e = e₀} {e′ = ε} p) o
ŝ-rᵀ {c₀ = c₀} {t = t} {g = g} p (ptr⁻ {e = e₀} {e′ = ε} o) = ŝ-rᵀ {c₀ = c₀} {t = tr⁻O ε t} {g = λ η e → tr⁻O ε (g η e)} (tr⁻ᵀ-cong {e = e₀} {e′ = ε} p) o
ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {x = x} {o₀ = o₀} {o = o} p (top {ev = ev} {ev′ = ev′} {p = p₀} {p′ = p′} d) = ĉ-rᴱ {c = c₀} {t₀ = z} {g = zg} {x = ψ̄ x ev p₀} {o₀ = ψ̄ o₀ ev′ p′} {o = λ η e → ψ̄ (o η e) ev′ p′} (ψ̄-cong p) d
ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = o₀} {o = o} p (pa {W = W} r d) = ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = W ⊕ o₀} {o = λ η e → W ⊕ o η e} (⊕-cong r p) d
ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = o₀} {o = o} p (pψ {q = q} d) = ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = ψᵒ q o₀} {o = λ η e → ψᵒ q (o η e)} (ψ-cong {q = q} p) d
ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = o₀} {o = o} p (pι {q = q} d) = ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = ι q o₀} {o = λ η e → ι q (o η e)} (ι-cong {q = q} p) d
ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = o₀} {o = o} p (ptr {e = e₀} {e′ = ε} d) = ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = trO ε o₀} {o = λ η e → trO ε (o η e)} (trᵀ-cong {e = e₀} {e′ = ε} p) d
ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = o₀} {o = o} p (ptr⁻ {e = e₀} {e′ = ε} d) = ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = tr⁻O ε o₀} {o = λ η e → tr⁻O ε (o η e)} (tr⁻ᵀ-cong {e = e₀} {e′ = ε} p) d

limᵢ-rᴱ : ∀ {k k′ j} {x : Ordˢ k} {q : j <ᴵ k′} {g : Uˢ j (<→◃ q) → Ordˢ k′} →
         (∀ z → z ≅ˢ Ωˢ j → x ⊑ᴱ g (intoˢ (<→◃ q) z)) → x ⊑ᴱ Ord₊ˢ.limᵢ q g
oi-rᵀ : ∀ {c φ ψ j} {x : O c φ} {ac : ∀ {L} → Ev L ψ → j <ᴵ L} {f : Ordˢ j → O c ψ} →
         (∀ z → z ≅ˢ Ωˢ j → x ⊑ᵀ f z) → x ⊑ᵀ oi ac f
limᵢ-rᴱ {q = ()} H idO
limᵢ-rᴱ {k′ = k′} {q = q} {g = g} H (tlo o) =
  oi-rᵀ {ac = λ e → cvFlo k′ e q} {f = λ x → tl (flo k′) (cvFlo k′) (g (intoˢ (<→◃ q) x))} (λ z d → tl-cong (H z d)) o
limᵢ-rᴱ {j = j} {x = x} {q = q} {g = g} H (addo {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} o k ea) = limᵢ-rᴱ (λ z d →
  subst (λ u → addˢ a σ x ⊑ᴱ addˢ a′ σ′ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ′ q)) z))
        (add-congᴱ k ea (H z d))) o
limᵢ-rᴱ {j = j} {x = x} {q = q} {g = g} H (tro {e = e} {e′ = e′} o) = limᵢ-rᴱ (λ z d →
  subst (λ u → trˢ e x ⊑ᴱ trˢ e′ (g (intoˢ (<→◃ q) (backˢ (resˢ q e′) u)))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e′))) z))
        (tr-congᴱ (H (backˢ (resˢ q e′) z) (≅ˢ-trans (backˢ-≅ q e′ d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (resˢ q e′)))))))) o
limᵢ-rᴱ {j = j} {x = x} {q = q} {g = g} H (tr⁻o {e = e} {e′ = e′} o) = limᵢ-rᴱ (λ z d →
  subst (λ u → tr⁻ˢ e x ⊑ᴱ tr⁻ˢ e′ (g (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e′) u)))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e′))) z))
        (tr⁻-congᴱ (H (backˢ (res⁻ˢ q e′) z) (≅ˢ-trans (back⁻ˢ-≅ q e′ d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (res⁻ˢ q e′)))))))) o
oi-rᵀ {j = j} {x = x} {ac = ac} {f = f} H (top {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o) with <ᴵ-dec (ac ev′) p′
... | injᵃ (via e s) = limᵢ-rᴱ {q = s} {g = λ y → ψ̄ (f (tr⁻ˢ e (outˢ (<→◃ s) y))) ev′ p′} (λ z d →
        subst (λ u → ψ̄ x ev p ⊑ᴱ ψ̄ (f (tr⁻ˢ e u)) ev′ p′) (sym (out-intoˢ (<→◃ s) z))
              (ψ̄-cong (H (tr⁻ˢ e z) (tr⁻ˢ-≅ e (≅ˢ-trans d (Ωˢ-≅ (≅ᴵ-sym e))))))) o
... | injᵇ _ = lim-rᴱ {x = ψ̄ x ev p} {h = λ m → ψ̄ (f (iter (λ w → ψ̄ (f w) ev′ (ac ev′)) (Ωˢ j) m)) ev′ p′} 0 (ψ̄-cong (H (Ωˢ j) (Ωˢ-refl j))) o
... | injᶜ _ = lim-rᴱ {x = ψ̄ x ev p} {h = λ m → ψ̄ (f (iter (λ w → ψ̄ (f w) ev′ (ac ev′)) (Ωˢ j) m)) ev′ p′} 0 (ψ̄-cong (H (Ωˢ j) (Ωˢ-refl j))) o
oi-rᵀ {ac = ac} {f = f} H (pa {W = W} r o) = oi-rᵀ {ac = λ e → ac (proj₂ e)} {f = λ x → W ⊕ f x} (λ z d → ⊕-cong r (H z d)) o
oi-rᵀ {ac = ac} {f = f} H (pψ {q = q} o) = oi-rᵀ {ac = λ e → ac (proj₂ e)} {f = λ x → ψᵒ q (f x)} (λ z d → ψ-cong {q = q} (H z d)) o
oi-rᵀ {ac = ac} {f = f} H (pι {q = q} o) = oi-rᵀ {ac = ac} {f = λ x → ι q (f x)} (λ z d → ι-cong {q = q} (H z d)) o
oi-rᵀ {ac = ac} {f = f} H (ptr {e = e₀} {e′ = ε} o) = oi-rᵀ {ac = ac} {f = λ x → trO ε (f x)} (λ z d → trᵀ-cong {e = e₀} {e′ = ε} (H z d)) o
oi-rᵀ {ac = ac} {f = f} H (ptr⁻ {e = e₀} {e′ = ε} o) = oi-rᵀ {ac = ac} {f = λ x → tr⁻O ε (f x)} (λ z d → tr⁻ᵀ-cong {e = e₀} {e′ = ε} (H z d)) o

up-lᴱ : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} {y : Ordˢ ℓ′} → outˢ (◃₁→◃ r) x ⊑ᴱ y → Ord₊ˢ.up r x ⊑ᴱ y
up-lᴱ {k = k} {r = zero} {x = x} h (tlo o) = wk-lᵀ {x = tl (flo k) (cvFlo k) x} (tl-cong h) o
up-lᴱ {k = k} {r = self n} {x = x} h (tlo o) = wk-lᵀ {x = tl (flo k) (cvFlo k) x} (tl-cong h) o
up-lᴱ {r = zero}   h (addo o k e) = h (addo o k e)
up-lᴱ {r = zero}   {x = x} {y = y} h (tro {e = s≅ e} {e′ = e′} o)  =
  up-lᴱ {r = zero} {x = trˢ e x} {y = trˢ e′ y} (λ o′ → h (tro o′)) o
up-lᴱ {r = zero}   {x = x} {y = y} h (tr⁻o {e = s≅ e} {e′ = e′} o) =
  up-lᴱ {r = zero} {x = tr⁻ˢ e x} {y = tr⁻ˢ e′ y} (λ o′ → h (tr⁻o o′)) o
up-lᴱ {r = self n} h (addo o k e) = h (addo o k e)
up-lᴱ {r = self n} {x = x} {y = y} h (tro {e = l≅ f} {e′ = e′} o)  =
  up-lᴱ {r = self n} {x = trˢ (f n) x} {y = trˢ e′ y} (λ o′ → h (tro o′)) o
up-lᴱ {r = self n} {x = x} {y = y} h (tr⁻o {e = l≅ f} {e′ = e′} o) =
  up-lᴱ {r = self n} {x = tr⁻ˢ (f n) x} {y = tr⁻ˢ e′ y} (λ o′ → h (tr⁻o o′)) o

up-rᴱ : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {y : Uˢ k (◃₁→◃ r)} {x : Ordˢ ℓ′} → x ⊑ᴱ outˢ (◃₁→◃ r) y → x ⊑ᴱ Ord₊ˢ.up r y
up-rᴱ {k = k} {r = zero} {y = y} h (tlo o) = wk-rᵀ {y = tl (flo k) (cvFlo k) y} (tl-cong h) o
up-rᴱ {k = k} {r = self n} {y = y} h (tlo o) = wk-rᵀ {y = tl (flo k) (cvFlo k) y} (tl-cong h) o
up-rᴱ {r = zero}   h (addo o k e) = h (addo o k e)
up-rᴱ {r = zero}   {y = y} {x = x} h (tro {e = e} {e′ = s≅ e′} o)  =
  up-rᴱ {r = zero} {y = trˢ e′ y} {x = trˢ e x} (λ o′ → h (tro o′)) o
up-rᴱ {r = zero}   {y = y} {x = x} h (tr⁻o {e = e} {e′ = s≅ e′} o) =
  up-rᴱ {r = zero} {y = tr⁻ˢ e′ y} {x = tr⁻ˢ e x} (λ o′ → h (tr⁻o o′)) o
up-rᴱ {r = self n} h (addo o k e) = h (addo o k e)
up-rᴱ {r = self n} {y = y} {x = x} h (tro {e = e} {e′ = l≅ f} o)  =
  up-rᴱ {r = self n} {y = trˢ (f n) y} {x = trˢ e x} (λ o′ → h (tro o′)) o
up-rᴱ {r = self n} {y = y} {x = x} h (tr⁻o {e = e} {e′ = l≅ f} o) =
  up-rᴱ {r = self n} {y = tr⁻ˢ (f n) y} {x = tr⁻ˢ e x} (λ o′ → h (tr⁻o o′)) o
```

`clo-go`: 走上下文时累积弱化 $L$.

```agda
clo-go : ∀ {c χ φ ψ} {x : O c χ} {C : Cx c χ} {C′ : Cx c ψ} → C ≈ᶜ C′ → (L : ∀ {ℓ} → Ev ℓ ψ → Ev ℓ (φ ⊔ fk zero)) →
         {t : O c (φ ⊔ fk zero)} {g : (η : Ordᴵ) → O c (φ ⊔ fk η)} → x ⊑ᵀ t →
         (G′ : Goodᴺ (toZ (runᶜ (wkC L C′) (oclo t g)))) → Σ (Goodᴺ (toZ (runᶜ C x))) λ G → forceᴺ _ G ⊑ forceᴺ _ G′
clo-go {φ = φ} {x = x} (top {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o) L {t} {g} h G′ =
  ŝ-rᴱ {x = ψ̄ x ev p} {t₀ = ψ̄ t (L ev′) p′} (ψ̄-cong {y = t} {ev = ev} {ev′ = L ev′} {p = p} {p′ = p′} h) o G′
clo-go {φ = φ} {x = x} {C = pa W C₁} {C′ = pa .W C₁′} (pa r o) L {t} {g} h G′ =
  proj₁ K , ⊑-trans (proj₂ K) (proj₂ J)
  where
  M : ∀ {ℓ} → Ev ℓ _ → Ev ℓ _
  M e = proj₁ e , L (proj₂ e)
  Y = oclo (owk asr (W ⊕ t)) (λ η → owk asr (W ⊕ g η))
  eq : runᶜ (wkC M C₁′) (W ⊕ oclo t g) ≡ runᶜ (wkC (λ e → asl (M e)) C₁′) Y
  eq = trans (sym (run-wkC asl (wkC M C₁′) Y)) (cong (λ D → runᶜ D Y) (wkC-comp asl M C₁′))
  J = pull≡ (sym eq) G′
  K = clo-go {φ = _ ⊔ φ} {x = W ⊕ x} o (λ e → asl (M e)) {owk asr (W ⊕ t)} {λ η → owk asr (W ⊕ g η)} (wk-rᵀ (⊕-cong r h)) (proj₁ J)
clo-go {φ = φ} {x = x} {C = pψ q C₁} {C′ = pψ .q C₁′} (pψ o) L {t} {g} h G′ =
  proj₁ K , ⊑-trans (proj₂ K) (proj₂ J)
  where
  M : ∀ {ℓ} → Ev ℓ _ → Ev ℓ _
  M e = proj₁ e , L (proj₂ e)
  Y = oclo (owk asr (ψᵒ q t)) (λ η → owk asr (ψᵒ q (g η)))
  eq : runᶜ (wkC M C₁′) (ψᵒ q (oclo t g)) ≡ runᶜ (wkC (λ e → asl (M e)) C₁′) Y
  eq = trans (sym (run-wkC asl (wkC M C₁′) Y)) (cong (λ D → runᶜ D Y) (wkC-comp asl M C₁′))
  J = pull≡ (sym eq) G′
  K = clo-go {φ = Fl ⊔ φ} {x = ψᵒ q x} o (λ e → asl (M e)) {owk asr (ψᵒ q t)} {λ η → owk asr (ψᵒ q (g η))} (wk-rᵀ (ψ-cong {q = q} h)) (proj₁ J)
clo-go {φ = φ} {x = x} {C′ = pι q C₁′} (pι o) L {t} {g} h G′ =
  clo-go {φ = φ} {x = ι q x} o L {ι q t} {λ η → ι q (g η)} (ι-cong {q = q} h) G′
clo-go {φ = φ} {x = x} {C = ptr e₀ _} {C′ = ptr e C₁′} (ptr o) L {t} {g} h G′ =
  clo-go {φ = φ} {x = trO e₀ x} o L {trO e t} {λ η → trO e (g η)} (trᵀ-cong {e = e₀} {e′ = e} h) G′
clo-go {φ = φ} {x = x} {C = ptr⁻ e₀ _} {C′ = ptr⁻ e C₁′} (ptr⁻ o) L {t} {g} h G′ =
  clo-go {φ = φ} {x = tr⁻O e₀ x} o L {tr⁻O e t} {λ η → tr⁻O e (g η)} (tr⁻ᵀ-cong {e = e₀} {e′ = e} h) G′

clo-rᵀ : ∀ {c χ φ} {x : O c χ} {t : O c (φ ⊔ fk zero)} {g : (η : Ordᴵ) → O c (φ ⊔ fk η)} → x ⊑ᵀ t → x ⊑ᵀ oclo t g
clo-rᵀ {φ = φ} {t = t} {g = g} h {C′ = C′} o G′ = proj₁ K , ⊑-trans (proj₂ K) (proj₂ J)
  where
  J = pull≡ (cong (λ D → runᶜ D (oclo t g)) (wkC-id C′)) G′
  K = clo-go {φ = φ} o (λ e → e) {t} {g} h (proj₁ J)

FlΩ̇ : ∀ m {ξ} → O m ξ → Set
FlΩ̇ m z = ∀ {χ} {x : O m χ} → Rᵒ m m x x → x ⊑ᵀ Ω̇ m → x ⊑ᵀ z
```

## §3′ 地板沿层号搬运

`FlΩ̇-tr⁻`: 穿透分支的输入是 `tr⁻O e z`. 关键是 `FlΩ̇` 带了 $x$ 的自相关: $x$ 先搬到 $b$ 层, 用 $z$ 的地板, 再搬回来, $x$ 与 $\mathtt{tr}^-\mathtt{tr}\,x$ 互模拟. `R-back`, `Fl-back`: `backO` 是若干次搬运.

```agda
⊑ᵀ-Rˡ : ∀ {c φ ψ} {x y : O c φ} {w : O c ψ} → Rᵒ c c x y → y ⊑ᵀ w → x ⊑ᵀ w
⊑ᵀ-Rˡ e i o G′ = proj₁ K , ⊑-trans (proj₂ K) (proj₂ J)
  where
  J = i o G′
  K = R→⊑ᵀ e (≈ᶜ-reflˡ o) (proj₁ J)

FlΩ̇-tr⁻ : ∀ {a b ξ} (e : a ≅ᴵ b) {z : O b ξ} → FlΩ̇ b z → FlΩ̇ a (tr⁻O e z)
FlΩ̇-tr⁻ {a} {b} e {z} f {χ} {x} rx h =
  ⊑ᵀ-Rˡ {y = tr⁻O e (trO e x)} (R-tr⁻ʳ e (R-trʳ e rx))
    (tr⁻ᵀ-cong {e = e} {e′ = e} (f (R-trˡ e (R-trʳ e rx)) (⊑ᵀ-Rʳ (trᵀ-cong {e = e} {e′ = e} h) (R-trˡ e (RΩ̇ e)))))

FlΩ̇-tr : ∀ {a b ξ} (e : a ≅ᴵ b) {z : O a ξ} → FlΩ̇ a z → FlΩ̇ b (trO e z)
FlΩ̇-tr {a} {b} e {z} f {χ} {x} rx h =
  ⊑ᵀ-Rˡ {y = trO e (tr⁻O e x)} (R-trʳ e (R-tr⁻ʳ e rx))
    (trᵀ-cong {e = e} {e′ = e} (f (R-tr⁻ˡ e (R-tr⁻ʳ e rx)) (⊑ᵀ-Rʳ (tr⁻ᵀ-cong {e = e} {e′ = e} h) (R-tr⁻ˡ e (RΩ̇ (≅ᴵ-sym e))))))

R-back : ∀ {j a b ξ ξ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {z : O (repO (resO q e)) ξ} {z′ : O (repO (resO q e)) ξ′} → Rᵒ _ _ z z′ → Rᵒ j j (backO (resO q e) z) (backO (resO q e) z′)
R-back q e r = R-resˡ q e (R-resʳ q e r)

R-back⁻ : ∀ {j a b ξ ξ′} (q : j <ᴵ a) (e : b ≅ᴵ a) {z : O (repO (res⁻O q e)) ξ} {z′ : O (repO (res⁻O q e)) ξ′} → Rᵒ _ _ z z′ → Rᵒ j j (backO (res⁻O q e) z) (backO (res⁻O q e) z′)
R-back⁻ q e r = R-res⁻ˡ q e (R-res⁻ʳ q e r)

Fl-back : ∀ {j a b ξ} (q : j <ᴵ a) (e : a ≅ᴵ b) {z : O (repO (resO q e)) ξ} → FlΩ̇ _ z → FlΩ̇ j (backO (resO q e) z)
Fl-back zero      (s≅ e) f = FlΩ̇-tr⁻ e f
Fl-back (suc q)   (s≅ e) f = Fl-back q e f
Fl-back (lim n q) (l≅ h) f = Fl-back q (h n) f

Fl-back⁻ : ∀ {j a b ξ} (q : j <ᴵ a) (e : b ≅ᴵ a) {z : O (repO (res⁻O q e)) ξ} → FlΩ̇ _ z → FlΩ̇ j (backO (res⁻O q e) z)
Fl-back⁻ zero      (s≅ e) f = FlΩ̇-tr e f
Fl-back⁻ (suc q)   (s≅ e) f = Fl-back⁻ q e f
Fl-back⁻ (lim n q) (l≅ h) f = Fl-back⁻ q (h n) f

Ω-rᵀ : ∀ {c χ φ m} {x : O c χ} {fe : ∀ {L} → Ev L φ → Ev L Fl} {r : m <ᴵ c} {h : ∀ ξ → Us m (<→◃ r) ξ → O c (ξ ⊔ φ)} →
       (∀ ξ (z : O m ξ) → Rᵒ m m z z → FlΩ̇ m z → x ⊑ᵀ h ξ (intoU (<→◃ r) z)) → x ⊑ᵀ oΩ fe r h
Ω-rᵀ {φ = φ} {m = m} {x = x} {fe = fe} {r = r} {h = h} H (top {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} o) =
  lim-rᴱ {x = ψ̄ x ev p} {h = λ n → ψ̄ (h φ (intoU (<→◃ r) (chainᵒ fe (λ z → owk (λ v → fe v , (v , v)) (ψᵒ r (h φ (intoU (<→◃ r) z)))) n))) (ev′ , ev′) p′} 0
    (ψ̄-cong (H φ (owk fe (Ω̇ m)) (rwk (RΩ̇ (≅ᴵ-refl m))) (λ _ h₁ → wk-rᵀ h₁))) o
Ω-rᵀ {x = x} {fe = fe} {r = r} {h = h} H (pa {W = W} rW o) =
  Ω-rᵀ {x = W ⊕ x} {fe = λ e → fe (proj₂ e)} {r = r} {h = λ ξ z → owk swp (W ⊕ h ξ z)} (λ ξ z rz f → wk-rᵀ (⊕-cong rW (H ξ z rz f))) o
Ω-rᵀ {c = c} {φ = φ} {m = m} {x = x} {fe = fe} {r = r} {h = h} H (pψ {t = t} {q = q} o) with <ᴵ-dec r q
... | injᵃ (via e s) = Ω-rᵀ {x = ψᵒ q x} {fe = proj₁} {r = s} {h = λ ξ z → owk swp (ψᵒ q (h ξ (intoU (<→◃ r) (tr⁻O e (outU (<→◃ s) z)))))}
    (λ ξ z rz f → wk-rᵀ (ψ-cong {q = q} (subst (λ w → x ⊑ᵀ h ξ (intoU (<→◃ r) (tr⁻O e w))) (sym (out-intoU (<→◃ s) z)) (H ξ (tr⁻O e z) (R-tr⁻ˡ e (R-tr⁻ʳ e rz)) (FlΩ̇-tr⁻ e f))))) o
... | injᵇ _ = lim-rᵀ {x = ψᵒ q x} {F = λ n → owk dupr2 (ψᵒ q (h (Fl ⊔ φ) (intoU (<→◃ r) (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r (h (Fl ⊔ φ) (intoU (<→◃ r) z)))) n))))} 0
    (wk-rᵀ (ψ-cong {q = q} (H (Fl ⊔ φ) (owk proj₁ (Ω̇ m)) (rwk (RΩ̇ (≅ᴵ-refl m))) (λ _ h₁ → wk-rᵀ h₁)))) o
... | injᶜ _ = lim-rᵀ {x = ψᵒ q x} {F = λ n → owk dupr2 (ψᵒ q (h (Fl ⊔ φ) (intoU (<→◃ r) (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r (h (Fl ⊔ φ) (intoU (<→◃ r) z)))) n))))} 0
    (wk-rᵀ (ψ-cong {q = q} (H (Fl ⊔ φ) (owk proj₁ (Ω̇ m)) (rwk (RΩ̇ (≅ᴵ-refl m))) (λ _ h₁ → wk-rᵀ h₁)))) o
Ω-rᵀ {x = x} {fe = fe} {r = r} {h = h} H (pι {q = q} o) =
  Ω-rᵀ {x = ι q x} {fe = fe} {r = <◃ r q} {h = λ ξ z → ι q (h ξ (intoU (<→◃ r) (outU (<→◃ (<◃ r q)) z)))}
    (λ ξ z rz f → ι-cong {q = q} (subst (λ w → x ⊑ᵀ h ξ (intoU (<→◃ r) w)) (sym (out-intoU (<→◃ (<◃ r q)) z)) (H ξ z rz f))) o
Ω-rᵀ {x = x} {fe = fe} {r = r} {h = h} H (ptr {e = e₀} {e′ = e} o) =
  Ω-rᵀ {x = trO e₀ x} {fe = fe} {r = ltO (resO r e)} {h = λ ξ z → trO e (h ξ (intoU (<→◃ r) (backO (resO r e) (outU (<→◃ (ltO (resO r e))) z))))}
    (λ ξ z rz f → trᵀ-cong {e = e₀} {e′ = e} (subst (λ w → x ⊑ᵀ h ξ (intoU (<→◃ r) (backO (resO r e) w))) (sym (out-intoU (<→◃ (ltO (resO r e))) z))
       (H ξ _ (R-back r e rz) (Fl-back r e f)))) o
Ω-rᵀ {x = x} {fe = fe} {r = r} {h = h} H (ptr⁻ {e = e₀} {e′ = e} o) =
  Ω-rᵀ {x = tr⁻O e₀ x} {fe = fe} {r = ltO (res⁻O r e)} {h = λ ξ z → tr⁻O e (h ξ (intoU (<→◃ r) (backO (res⁻O r e) (outU (<→◃ (ltO (res⁻O r e))) z))))}
    (λ ξ z rz f → tr⁻ᵀ-cong {e = e₀} {e′ = e} (subst (λ w → x ⊑ᵀ h ξ (intoU (<→◃ r) (backO (res⁻O r e) w))) (sym (out-intoU (<→◃ (ltO (res⁻O r e))) z))
       (H ξ _ (R-back⁻ r e rz) (Fl-back⁻ r e f)))) o
```

## §4 地板

全部对 `Rᵒ` 的推导归纳, 不反演 `Rᵒ x x`. `selfL`/`selfR`: `Rᵒ` 的 `rΩ` 分支要的输入自相关.

```agda
B1ᵀ : ∀ {c c′ χ a φ ψ} {x : O c χ} {W : O c a} {t : O c φ} {t′ : O c′ ψ} → Rᵒ c c′ t t′ → x ⊑ᵀ W → x ⊑ᵀ W ⊕ t
B1ᵀ rz h = wk-rᵀ h
B1ᵀ (rs s r) h = suc-rᵀ (B1ᵀ r h)
B1ᵀ (rl f) h = lim-rᵀ 0 (B1ᵀ (f 0) h)
B1ᵀ (ri e f) h = oi-rᵀ (λ z d → B1ᵀ (f z (trˢ e z) (≅ˢ-sym (trˢ-≅ e (≅ˢ-reflˡ d)))) h)
B1ᵀ (rŝ e r f) h = ŝ-rᵀ (B1ᵀ r h)
B1ᵀ (rĉ e dz dg r f) h = ĉ-rᵀ (B1ᵀ r h)
B1ᵀ (rclo s r f) h = wk-rᵀ (clo-rᵀ (wk-rᵀ (B1ᵀ r h)))
B1ᵀ (rwkˡ r) h = wk-rᵀ (B1ᵀ r h)
B1ᵀ (rwkʳ r) h = B1ᵀ r h
B1ᵀ {W = W} (rΩ {φ = φ} {r = r} {h = h₀} ek s f) h = Ω-rᵀ {h = λ ξ z → owk swp (W ⊕ h₀ ξ z)} (λ ξ z rz fz → wk-rᵀ (B1ᵀ (f ξ ξ (∼ᶠ-refl ξ) z (trO ek z) (intoR (<→◃ r) (R-trʳ ek rz))) h))

F0ᵀ : ∀ {c c′ φ ψ i ℓ} {x : O c φ} {x′ : O c′ ψ} {ev : Ev ℓ φ} {p : i <ᴵ ℓ} → Rᵒ c c′ x x′ → Ωˢ i ⊑ᴱ ψ̄ x ev p
F0ᵀ {i = i} rz = ≅→⊑ᴱ (Ωˢ-refl i)
F0ᵀ {x = os a} {ev = ev} {p = p} (rs s r) = lim-rᴱ {h = iter (ψ̄ a ev p +ˢ_) Ord₊ˢ.zero} 1 (F0ᵀ r)
F0ᵀ {x = ol F} {ev = ev} {p = p} (rl f) = lim-rᴱ {h = λ n → ψ̄ (F n) ev p} 0 (F0ᵀ (f 0))
F0ᵀ {i = i} {x = oi {j = j} ac f₀} {ev = ev} {p = p} (ri e f) with <ᴵ-dec (ac ev) p
... | injᵃ (via e₁ s) = limᵢ-rᴱ {q = s} {g = λ y → ψ̄ (f₀ (tr⁻ˢ e₁ (outˢ (<→◃ s) y))) ev p} (λ z d →
        subst (λ u → Ωˢ i ⊑ᴱ ψ̄ (f₀ (tr⁻ˢ e₁ u)) ev p) (sym (out-intoˢ (<→◃ s) z))
              (F0ᵀ (f (tr⁻ˢ e₁ z) (trˢ e (tr⁻ˢ e₁ z)) (≅ˢ-sym (trˢ-≅ e (self-tr⁻ˢ e₁ (≅ˢ-reflˡ d)))))))
... | injᵇ _ = lim-rᴱ {h = λ m → ψ̄ (f₀ (iter (λ w → ψ̄ (f₀ w) ev (ac ev)) (Ωˢ j) m)) ev p} 0 (F0ᵀ (f (Ωˢ j) (trˢ e (Ωˢ j)) (≅ˢ-sym (trˢ-≅ e (Ωˢ-refl j)))))
... | injᶜ _ = lim-rᴱ {h = λ m → ψ̄ (f₀ (iter (λ w → ψ̄ (f₀ w) ev (ac ev)) (Ωˢ j) m)) ev p} 0 (F0ᵀ (f (Ωˢ j) (trˢ e (Ωˢ j)) (≅ˢ-sym (trˢ-≅ e (Ωˢ-refl j)))))
F0ᵀ {x = oŝ c₀ t g} {ev = ev} {p = p} (rŝ e r f) = ŝ-rᴱ {t₀ = ψ̄ t ev p} (F0ᵀ r)
F0ᵀ {x = oĉ c₀ z zg o₀ o} {ev = ev} {p = p} (rĉ e dz dg r f) = ĉ-rᴱ {o₀ = ψ̄ o₀ ev p} (F0ᵀ r)
F0ᵀ {x = oclo t g} {ev = ev} {p = p} (rclo s r f) = ŝ-rᴱ {t₀ = ψ̄ t ev p} (F0ᵀ r)
F0ᵀ (rwkˡ r) = F0ᵀ r
F0ᵀ (rwkʳ r) = F0ᵀ r
F0ᵀ {x = oΩ {φ = φ} {k = m} fe r h} {ev = ev} {p = p} (rΩ ek s f) =
  lim-rᴱ {h = λ n → ψ̄ (h φ (intoU (<→◃ r) (chainᵒ fe (λ z → owk (λ v → fe v , (v , v)) (ψᵒ r (h φ (intoU (<→◃ r) z)))) n))) (ev , ev) p} 0
    (F0ᵀ (f φ φ (∼ᶠ-refl φ) (owk fe (Ω̇ m)) (trO ek (owk fe (Ω̇ m))) (intoR (<→◃ r) (R-trʳ ek (rwk (RΩ̇ (≅ᴵ-refl m)))))))

P0ᵀ : ∀ {c c′ t χ φ ψ} {y : O t χ} {q : t <ᴵ c} {x : O c φ} {x′ : O c′ ψ} → Rᵒ c c′ x x′ → y ⊑ᵀ Ω̇ t → y ⊑ᵀ ψᵒ q x
P0ᵀ {q = q} rz h = wk-rᵀ h
P0ᵀ {q = q} {x = os a} (rs s r) h = lim-rᵀ {F = repᵒ (ψᵒ q a)} 1 (P0ᵀ {q = q} r h)
P0ᵀ {q = q} (rl f) h = lim-rᵀ 0 (P0ᵀ {q = q} (f 0) h)
P0ᵀ {q = q} (ri e f) h = oi-rᵀ (λ z d → P0ᵀ {q = q} (f z (trˢ e z) (≅ˢ-sym (trˢ-≅ e (≅ˢ-reflˡ d)))) h)
P0ᵀ {q = q} (rŝ e r f) h = ŝ-rᵀ (P0ᵀ {q = q} r h)
P0ᵀ {q = q} (rĉ e dz dg r f) h = ĉ-rᵀ (P0ᵀ {q = q} r h)
P0ᵀ {q = q} (rclo s r f) h = wk-rᵀ (clo-rᵀ (wk-rᵀ (P0ᵀ {q = q} r h)))
P0ᵀ {q = q} (rwkˡ r) h = wk-rᵀ (P0ᵀ {q = q} r h)
P0ᵀ {q = q} (rwkʳ r) h = P0ᵀ {q = q} r h
P0ᵀ {t = t} {y = y} {q = q} {x = oΩ {φ = φ} {k = m} fe r h₀} (rΩ ek s f) h with <ᴵ-dec r q
... | injᵃ (via e s₁) = Ω-rᵀ {h = λ ξ z → owk swp (ψᵒ q (h₀ ξ (intoU (<→◃ r) (tr⁻O e (outU (<→◃ s₁) z)))))}
    (λ ξ z rz fz → wk-rᵀ (subst (λ w → y ⊑ᵀ ψᵒ q (h₀ ξ (intoU (<→◃ r) (tr⁻O e w)))) (sym (out-intoU (<→◃ s₁) z))
       (P0ᵀ {q = q} (f ξ ξ (∼ᶠ-refl ξ) (tr⁻O e z) (trO ek (tr⁻O e z)) (intoR (<→◃ r) (R-trʳ ek (R-tr⁻ˡ e (R-tr⁻ʳ e rz))))) h)))
... | injᵇ _ = lim-rᵀ {F = λ n → owk dupr2 (ψᵒ q (h₀ (Fl ⊔ φ) (intoU (<→◃ r) (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r (h₀ (Fl ⊔ φ) (intoU (<→◃ r) z)))) n))))} 0
    (wk-rᵀ (P0ᵀ {q = q} (f (Fl ⊔ φ) (Fl ⊔ φ) (∼ᶠ-refl _) (owk proj₁ (Ω̇ m)) (trO ek (owk proj₁ (Ω̇ m))) (intoR (<→◃ r) (R-trʳ ek (rwk (RΩ̇ (≅ᴵ-refl m)))))) h))
... | injᶜ _ = lim-rᵀ {F = λ n → owk dupr2 (ψᵒ q (h₀ (Fl ⊔ φ) (intoU (<→◃ r) (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r (h₀ (Fl ⊔ φ) (intoU (<→◃ r) z)))) n))))} 0
    (wk-rᵀ (P0ᵀ {q = q} (f (Fl ⊔ φ) (Fl ⊔ φ) (∼ᶠ-refl _) (owk proj₁ (Ω̇ m)) (trO ek (owk proj₁ (Ω̇ m))) (intoR (<→◃ r) (R-trʳ ek (rwk (RΩ̇ (≅ᴵ-refl m)))))) h))

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

zero-lᵀ : ∀ {c c′ φ ψ χ} {y : O c ψ} {y′ : O c′ χ} → Rᵒ c c′ y y′ → o0 {φ = φ} ⊑ᵀ y
zero-lᵀ r (top o) = F0ᵀ r o
zero-lᵀ r (pa rW o) = B1ᵀ r (wk-lᵀ (R→⊑ᵀ rW)) o
zero-lᵀ {y = y} r (pψ {t = t} {q = q} o) = P0ᵀ {y = owk proj₁ (Ω̇ t)} {q = q} {x = y} r (wk-lᵀ (R→⊑ᵀ (RΩ̇ (≅ᴵ-refl t)))) o
zero-lᵀ {y = y} r (pι {q = q} o) = zero-lᵀ {y = ι q y} (R-ιˡ q r) o
zero-lᵀ {y = y} r (ptr {e′ = e} o) = zero-lᵀ {y = trO e y} (R-trˡ e r) o
zero-lᵀ {y = y} r (ptr⁻ {e′ = e} o) = zero-lᵀ {y = tr⁻O e y} (R-tr⁻ˡ e r) o

zero-lᴱ : ∀ {k k′} {y : Ordˢ k′} → y ≅ˢ y → 𝟎ˢ {k} ⊑ᴱ y
zero-lᴱ ey idO G′ = gz , λ ()
zero-lᴱ {k′ = k′} {y = y} ey (tlo o) = zero-lᵀ {y = tl (flo k′) (cvFlo k′) y} (R-tl {c′ = zero} {cv = cvFlo k′} {cv′ = cvFlo k′} ey) o
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
