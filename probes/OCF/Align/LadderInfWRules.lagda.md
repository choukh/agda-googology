> **机械克隆, 验收用.** 由 `LadderInfRules` 经 `Survey/scripts/laddernf/mk_infw.py` 复制, 只改导入, 落在标签阶梯的世界. 见 [LadderInfAccept](LadderInfAccept.lagda.md).

# 高度抽象: 比较规则

> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 对高度结构 `HtS` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFRules](LadderNFRules.lagda.md) 生成, 下面的说明是原文件的. 与 `OCF.Free.Rules` 同形, 上下文多 `pΨ`, `pD`, 树多 `qcl`, `qΩ↓`, `omk`. 值层的行逐字. 树层的行是脚本生成的. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderInfWRules (𝕊 : HtS) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.LadderNFWPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ; Ωˢ; addˢ; _+ˢ_; 𝟎ˢ)
open import OCF.Align.LadderNFWEq using (kd; ≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; _≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; upˡ; upʳ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ; trˢ-≅; tr⁻ˢ-≅; backˢ-≅; back⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; addˢ-≅; s-invˢ; l-invˢ; i-respˢ; u-reflˢ; ŝ-refl₀; ĉ-refl₀; self-trˢ; self-tr⁻ˢ)
open import OCF.Align.LadderNFWFloor using (_∼ᶠ_; ∼ᶠ-refl; fz∼; ⊔∼; Flr; fz; fk; Ev; Run; flo; cvFlo; toFlo; ∅ᴿ; _⊔_; cloA; limᵢA; Bd; bound; evF; iF; FB; Fc)
open import OCF.Align.LadderNFWForce using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Align.LadderNFWFT using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderInfWTree 𝕊
open import OCF.Align.LadderInfWRel 𝕊
open import OCF.Align.LadderInfWCx 𝕊
open Ord-Ord using (iter)
open Restrˢ
open RestrQ
```

## §0 相似的基本引理

```agda
≈ᵒ-reflˡ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O ≈ᵒ O
≈ᶜ-reflˡ : ∀ {m c φ χ ψ ρ} {C : Cx m c φ χ} {C′ : Cx m c ψ ρ} → C ≈ᶜ C′ → C ≈ᶜ C
≈ᵒ-reflˡ idO          = idO
≈ᵒ-reflˡ (tlo o)      = tlo (≈ᶜ-reflˡ o)
≈ᵒ-reflˡ (addo o k e) = addo (≈ᵒ-reflˡ o) (≅ᴵ-refl _) (≅ˢ-reflˡ e)
≈ᵒ-reflˡ (tro o)      = tro (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (tr⁻o o)     = tr⁻o (≈ᵒ-reflˡ o)
≈ᶜ-reflˡ (top o)   = top (≈ᵒ-reflˡ o)
≈ᶜ-reflˡ (pa r o)  = pa r (≈ᶜ-reflˡ o)
≈ᶜ-reflˡ (pψ o)    = pψ (≈ᶜ-reflˡ o)
≈ᶜ-reflˡ (pΨ o)    = pΨ (≈ᶜ-reflˡ o)
≈ᶜ-reflˡ (pι o)    = pι (≈ᶜ-reflˡ o)
≈ᶜ-reflˡ (pD o)    = pD (≈ᶜ-reflˡ o)
≈ᶜ-reflˡ (ptr o)   = ptr (≈ᶜ-reflˡ o)
≈ᶜ-reflˡ (ptr⁻ o)  = ptr⁻ (≈ᶜ-reflˡ o)

≈ᵒ-reflʳ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O′ ≈ᵒ O′
≈ᶜ-reflʳ : ∀ {m c φ χ ψ ρ} {C : Cx m c φ χ} {C′ : Cx m c ψ ρ} → C ≈ᶜ C′ → C′ ≈ᶜ C′
≈ᵒ-reflʳ idO          = idO
≈ᵒ-reflʳ (tlo o)      = tlo (≈ᶜ-reflʳ o)
≈ᵒ-reflʳ (addo o k e) = addo (≈ᵒ-reflʳ o) (≅ᴵ-refl _) (≅ˢ-reflʳ e)
≈ᵒ-reflʳ (tro o)      = tro (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (tr⁻o o)     = tr⁻o (≈ᵒ-reflʳ o)
≈ᶜ-reflʳ (top o)   = top (≈ᵒ-reflʳ o)
≈ᶜ-reflʳ (pa r o)  = pa r (≈ᶜ-reflʳ o)
≈ᶜ-reflʳ (pψ o)    = pψ (≈ᶜ-reflʳ o)
≈ᶜ-reflʳ (pΨ o)    = pΨ (≈ᶜ-reflʳ o)
≈ᶜ-reflʳ (pι o)    = pι (≈ᶜ-reflʳ o)
≈ᶜ-reflʳ (pD o)    = pD (≈ᶜ-reflʳ o)
≈ᶜ-reflʳ (ptr o)   = ptr (≈ᶜ-reflʳ o)
≈ᶜ-reflʳ (ptr⁻ o)  = ptr⁻ (≈ᶜ-reflʳ o)

≈ᶜ-wkʳ : ∀ {m c χ₀ φ χ ψ ρ φ₀} {C : Cx m c φ₀ χ₀} {C′ : Cx m c ψ ρ} (le : ∀ {L} → Ev L ψ → Ev L φ) (lc : Sub m ρ χ) → C ≈ᶜ C′ → C ≈ᶜ wkC le lc C′
≈ᶜ-wkʳ le lc (top o)  = top o
≈ᶜ-wkʳ le lc (pa r o) = pa r (≈ᶜ-wkʳ _ _ o)
≈ᶜ-wkʳ le lc (pψ o)   = pψ (≈ᶜ-wkʳ _ _ o)
≈ᶜ-wkʳ le lc (pΨ o)   = pΨ (≈ᶜ-wkʳ _ _ o)
≈ᶜ-wkʳ le lc (pι o)   = pι (≈ᶜ-wkʳ le lc o)
≈ᶜ-wkʳ le lc (pD o)   = pD (≈ᶜ-wkʳ _ _ o)
≈ᶜ-wkʳ le lc (ptr o)  = ptr (≈ᶜ-wkʳ le lc o)
≈ᶜ-wkʳ le lc (ptr⁻ o) = ptr⁻ (≈ᶜ-wkʳ le lc o)

≈ᶜ-wkˡ : ∀ {m c χ₀ φ χ ψ ρ φ₀} {C : Cx m c ψ ρ} {C′ : Cx m c φ₀ χ₀} (le : ∀ {L} → Ev L ψ → Ev L φ) (lc : Sub m ρ χ) → C ≈ᶜ C′ → wkC le lc C ≈ᶜ C′
≈ᶜ-wkˡ le lc (top o)  = top o
≈ᶜ-wkˡ le lc (pa r o) = pa r (≈ᶜ-wkˡ _ _ o)
≈ᶜ-wkˡ le lc (pψ o)   = pψ (≈ᶜ-wkˡ _ _ o)
≈ᶜ-wkˡ le lc (pΨ o)   = pΨ (≈ᶜ-wkˡ _ _ o)
≈ᶜ-wkˡ le lc (pι o)   = pι (≈ᶜ-wkˡ le lc o)
≈ᶜ-wkˡ le lc (pD o)   = pD (≈ᶜ-wkˡ _ _ o)
≈ᶜ-wkˡ le lc (ptr o)  = ptr (≈ᶜ-wkˡ le lc o)
≈ᶜ-wkˡ le lc (ptr⁻ o) = ptr⁻ (≈ᶜ-wkˡ le lc o)
```

## §1 两个前序

```agda
infix 4 _⊑ᴱ_ _⊑ᵀ_
_⊑ᴱ_ : ∀ {k k′} → Ordˢ k → Ordˢ k′ → Set
_⊑ᴱ_ {k} {k′} x y = ∀ {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → (G′ : Goodᴺ (toZ (run O′ y))) →
  Σ (Goodᴺ (toZ (run O x))) λ G → forceᴺ _ G ⊑ forceᴺ _ G′

_⊑ᵀ_ : ∀ {m c φ χ ψ ρ} → Q m c φ χ → Q m c ψ ρ → Set
_⊑ᵀ_ {m} {c} {φ} {χ} {ψ} {ρ} x y = ∀ {C : Cx m c φ χ} {C′ : Cx m c ψ ρ} → C ≈ᶜ C′ → (G′ : Goodᴺ (toZ (runᶜ C′ y))) →
  Σ (Goodᴺ (toZ (runᶜ C x))) λ G → forceᴺ _ G ⊑ forceᴺ _ G′

pull≡ : ∀ {u v : Ordˢ zero} → u ≡ v → (G′ : Goodᴺ (toZ v)) → Σ (Goodᴺ (toZ u)) λ G → forceᴺ _ G ⊑ forceᴺ _ G′
pull≡ refl G′ = G′ , (λ h → h)

≅→⊑ᴱ : ∀ {k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ≅ˢ y → x ⊑ᴱ y
≅→⊑ᴱ e o G′ = Goodᴺ-tr (≅ᶻ-sym d) G′ , ≅→⊑ (forceᴺ-≅ d (Goodᴺ-tr (≅ᶻ-sym d) G′) G′)
  where d = toZ-≅ (run-≅ o e)

R→⊑ᵀ : ∀ {m c φ χ ψ ρ} {x : Q m c φ χ} {y : Q m c ψ ρ} → Rq m c c x y → x ⊑ᵀ y
R→⊑ᵀ e o G′ = Goodᴺ-tr (≅ᶻ-sym d) G′ , ≅→⊑ (forceᴺ-≅ d (Goodᴺ-tr (≅ᶻ-sym d) G′) G′)
  where d = toZ-≅ (runᶜ-≅ o e)

⊑ᴱ-≅ʳ : ∀ {k k′} {x : Ordˢ k} {y y′ : Ordˢ k′} → x ⊑ᴱ y → y ≅ˢ y′ → x ⊑ᴱ y′
⊑ᴱ-≅ʳ h e o G′ = proj₁ (h o Gm) , ⊑-trans (proj₂ (h o Gm)) (≅→⊑ (forceᴺ-≅ d Gm G′))
  where
  d = toZ-≅ (run-≅ (≈ᵒ-reflʳ o) e)
  Gm = Goodᴺ-tr (≅ᶻ-sym d) G′

⊑ᵀ-Rʳ : ∀ {m c φ χ ψ ρ} {x : Q m c φ χ} {y y′ : Q m c ψ ρ} → x ⊑ᵀ y → Rq m c c y y′ → x ⊑ᵀ y′
⊑ᵀ-Rʳ h e o G′ = proj₁ (h o Gm) , ⊑-trans (proj₂ (h o Gm)) (≅→⊑ (forceᴺ-≅ d Gm G′))
  where
  d = toZ-≅ (runᶜ-≅ (≈ᶜ-reflʳ o) e)
  Gm = Goodᴺ-tr (≅ᶻ-sym d) G′

⊑ᴱ-trans : ∀ {k k′} {x : Ordˢ k} {y w : Ordˢ k′} → x ⊑ᴱ y → y ⊑ᴱ w → x ⊑ᴱ w
⊑ᴱ-trans h i o G′ = proj₁ (h o Gm) , ⊑-trans (proj₂ (h o Gm)) (proj₂ (i (≈ᵒ-reflʳ o) G′))
  where Gm = proj₁ (i (≈ᵒ-reflʳ o) G′)

⊑ᵀ-trans : ∀ {m c φ χ ψ ρ} {x : Q m c φ χ} {y w : Q m c ψ ρ} → x ⊑ᵀ y → y ⊑ᵀ w → x ⊑ᵀ w
⊑ᵀ-trans h i o G′ = proj₁ (h o Gm) , ⊑-trans (proj₂ (h o Gm)) (proj₂ (i (≈ᶜ-reflʳ o) G′))
  where Gm = proj₁ (i (≈ᶜ-reflʳ o) G′)
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

ψ̄-cong : ∀ {m c φ χ ψ ρ i ℓ ℓ′ w w′} {x : Q m c φ χ} {y : Q m c ψ ρ} {ok : Ok w} {ok′ : Ok w′} {e : Eh h₀ m w χ} {e′ : Eh h₀ m w′ ρ} {ev : Ev ℓ φ} {ev′ : Ev ℓ′ ψ} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} →
         x ⊑ᵀ y → ψ̄ᵠ ok e x ev p ⊑ᴱ ψ̄ᵠ ok′ e′ y ev′ p′
ψ̄-cong h o = h (top o)

tl-cong : ∀ {k k′ χ ρ} {x : Ordˢ k} {y : Ordˢ k′} → x ⊑ᴱ y → tl {c = zero} {χ = χ} (flo k) (cvFlo k) x ⊑ᵀ tl {c = zero} {χ = ρ} (flo k′) (cvFlo k′) y
tl-cong h o = h (tlo o)

⊞-cong : ∀ {m c a b φ χ ψ ρ} {W : Q m c a b} {x : Q m c φ χ} {y : Q m c ψ ρ} → Rq m c c W W → x ⊑ᵀ y → W ⊞ x ⊑ᵀ W ⊞ y
⊞-cong r h o = h (pa r o)

ψ-cong : ∀ {m c t φ χ ψ ρ} {q : t <ᴵ c} {x : Q m c φ χ} {y : Q m c ψ ρ} → x ⊑ᵀ y → ψᵠ q x ⊑ᵀ ψᵠ q y
ψ-cong {q = q} h o = h (pψ {q = q} o)

Ψ-cong : ∀ {H m c t φ χ ψ ρ w w′} {qH : H <ᴸ m} {ok : Ok w} {ok′ : Ok w′} {e : Eh H m w χ} {e′ : Eh H m w′ ρ} {p : t <ᴵ w H} {p′ : t <ᴵ w′ H} {x : Q m c φ χ} {y : Q m c ψ ρ} → x ⊑ᵀ y → Ψ qH ok e p x ⊑ᵀ Ψ qH ok′ e′ p′ y
Ψ-cong h o = h (pΨ o)

ι-cong : ∀ {m c d φ χ ψ ρ} {q : c ◃ d} {x : Q m c φ χ} {y : Q m c ψ ρ} → x ⊑ᵀ y → ι q x ⊑ᵀ ι q y
ι-cong {q = q} h o = h (pι {q = q} o)

ιD-cong : ∀ {n m k φ χ ψ ρ} {qd : n <ᴸ m} {x : Q n k φ χ} {y : Q n k ψ ρ} → x ⊑ᵀ y → ι↓ {α = zero} qd x ⊑ᵀ ι↓ {α = zero} qd y
ιD-cong {qd = qd} h o = h (pD {q = qd} o)

trᵀ-cong : ∀ {m a b φ χ ψ ρ} {e e′ : a ≅ᴵ b} {x : Q m a φ χ} {y : Q m a ψ ρ} → x ⊑ᵀ y → trQ e x ⊑ᵀ trQ e′ y
trᵀ-cong h o = h (ptr o)

tr⁻ᵀ-cong : ∀ {m a b φ χ ψ ρ} {e e′ : a ≅ᴵ b} {x : Q m b φ χ} {y : Q m b ψ ρ} → x ⊑ᵀ y → tr⁻Q e x ⊑ᵀ tr⁻Q e′ y
tr⁻ᵀ-cong h o = h (ptr⁻ o)

wk-lᵀ : ∀ {m c φ χ φ′ χ′ ψ ρ} {le : ∀ {L} → Ev L φ′ → Ev L φ} {lc : Sub m χ′ χ} {x : Q m c φ χ} {y : Q m c ψ ρ} → x ⊑ᵀ y → qwk le lc x ⊑ᵀ y
wk-lᵀ {le = le} {lc = lc} {x = x} h {C} o G′ = proj₁ L , ⊑-trans (proj₂ L) (proj₂ (h (≈ᶜ-wkˡ le lc o) G′))
  where L = pull≡ (sym (run-wkC le lc C x)) (proj₁ (h (≈ᶜ-wkˡ le lc o) G′))

wk-rᵀ : ∀ {m c φ₀ χ₀ φ χ ψ ρ} {le : ∀ {L} → Ev L ψ → Ev L φ} {lc : Sub m ρ χ} {x : Q m c φ₀ χ₀} {y : Q m c φ χ} → x ⊑ᵀ y → x ⊑ᵀ qwk le lc y
wk-rᵀ {le = le} {lc = lc} {x = x} {y = y} h {C′ = C′} o G′ = proj₁ K , ⊑-trans (proj₂ K) (proj₂ L)
  where
  L = pull≡ (run-wkC le lc C′ y) G′
  K = h {C′ = wkC le lc C′} (≈ᶜ-wkʳ le lc o) (proj₁ L)
```

## §3 右引入规则

```agda
lim-rᴱ : ∀ {k k′} {x : Ordˢ k} {h : ℕ → Ordˢ k′} n → x ⊑ᴱ h n → x ⊑ᴱ Ord₊ˢ.lim h
lim-rᵀ : ∀ {m c φ χ ψ ρ} {x : Q m c φ χ} {F : ℕ → Q m c ψ ρ} n → x ⊑ᵀ F n → x ⊑ᵀ ql F
lim-rᴱ n p idO (gl G′ st) = proj₁ (p idO (G′ n)) , ⊑-lim n (proj₂ (p idO (G′ n)))
lim-rᴱ {k′ = k′} {h = h} n p (tlo o) = lim-rᵀ {F = λ m → tl (flo k′) (cvFlo k′) (h m)} n (tl-cong p) o
lim-rᴱ {h = h} n p (addo {a′ = a′} {σ′ = σ′} o k a) = lim-rᴱ {h = λ m → addˢ a′ σ′ (h m)} n (add-congᴱ k a p) o
lim-rᴱ {h = h} n p (tro {e′ = e′} o)  = lim-rᴱ {h = λ m → trˢ e′ (h m)} n (tr-congᴱ p) o
lim-rᴱ {h = h} n p (tr⁻o {e′ = e′} o) = lim-rᴱ {h = λ m → tr⁻ˢ e′ (h m)} n (tr⁻-congᴱ p) o

lim-rᵀ {x = x} {F = F} n p₁ (top {ev = ev} {ev′ = ev′} {p = p₀} {p′ = pt} {ok = ok} {ok′ = ok′} {e = e} {e′ = e′} o) = lim-rᴱ {x = ψ̄ᵠ ok e x ev p₀} {h = λ i → ψ̄ᵠ ok′ e′ (F i) ev′ pt} n (ψ̄-cong p₁) o
lim-rᵀ {F = F} n p₁ (pa {W = W} r o) = lim-rᵀ {F = λ i → W ⊞ F i} n (⊞-cong r (p₁)) o
lim-rᵀ {F = F} n p₁ (pψ {q = q} o) = lim-rᵀ {F = λ i → ψᵠ q (F i)} n (ψ-cong {q = q} (p₁)) o
lim-rᵀ {F = F} n p₁ (pΨ {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} o) = lim-rᵀ {F = λ i → Ψ qH ok e pt (F i)} n (Ψ-cong {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} (p₁)) o
lim-rᵀ {F = F} n p₁ (pι {q = q} o) = lim-rᵀ {F = λ i → ι q (F i)} n (ι-cong {q = q} (p₁)) o
lim-rᵀ {F = F} n p₁ (pD {q = qd} o) = lim-rᵀ {F = λ i → ι↓ {α = zero} qd (F i)} n (ιD-cong (p₁)) o
lim-rᵀ {F = F} n p₁ (ptr {e = e₀} {e′ = ε} o) = lim-rᵀ {F = λ i → trQ ε (F i)} n (trᵀ-cong {e = e₀} {e′ = ε} (p₁)) o
lim-rᵀ {F = F} n p₁ (ptr⁻ {e = e₀} {e′ = ε} o) = lim-rᵀ {F = λ i → tr⁻Q ε (F i)} n (tr⁻ᵀ-cong {e = e₀} {e′ = ε} (p₁)) o

suc-rᴱ : ∀ {k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ⊑ᴱ y → x ⊑ᴱ Ord₊ˢ.suc y
suc-rᵀ : ∀ {m c φ χ ψ ρ} {x : Q m c φ χ} {y : Q m c ψ ρ} → x ⊑ᵀ y → x ⊑ᵀ qs y
suc-rᴱ p idO (gs G′) = proj₁ (p idO G′) , λ h → ≺s (proj₂ (p idO G′) h)
suc-rᴱ {k′ = k′} {y = y} p (tlo o) = suc-rᵀ {y = tl (flo k′) (cvFlo k′) y} (tl-cong p) o
suc-rᴱ {y = y} p (addo {a′ = a′} {σ′ = σ′} o k a) = suc-rᴱ {y = addˢ a′ σ′ y} (add-congᴱ k a p) o
suc-rᴱ {y = y} p (tro {e′ = e′} o)  = suc-rᴱ {y = trˢ e′ y} (tr-congᴱ p) o
suc-rᴱ {y = y} p (tr⁻o {e′ = e′} o) = suc-rᴱ {y = tr⁻ˢ e′ y} (tr⁻-congᴱ p) o

suc-rᵀ {x = x} {y = y} p₁ (top {ev = ev} {ev′ = ev′} {p = p₀} {p′ = pt} {ok = ok} {ok′ = ok′} {e = e} {e′ = e′} o) = lim-rᴱ {x = ψ̄ᵠ ok e x ev p₀} {h = iter (ψ̄ᵠ ok′ e′ y ev′ pt +ˢ_) Ord₊ˢ.zero} 1 (ψ̄-cong p₁) o
suc-rᵀ {y = y} p₁ (pa {W = W} r o) = suc-rᵀ {y = W ⊞ y} (⊞-cong r (p₁)) o
suc-rᵀ {y = y} p₁ (pψ {q = q} o) = lim-rᵀ {F = repᵠ (ψᵠ q y)} 1 (ψ-cong {q = q} (p₁)) o
suc-rᵀ {y = y} p₁ (pΨ {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} o) = lim-rᵀ {F = repᵠ (Ψ qH ok e pt y)} 1 (Ψ-cong {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} (p₁)) o
suc-rᵀ {y = y} p₁ (pι {q = q} o) = suc-rᵀ {y = ι q (y)} (ι-cong {q = q} (p₁)) o
suc-rᵀ {y = y} p₁ (pD {q = qd} o) = suc-rᵀ {y = ι↓ {α = zero} qd (y)} (ιD-cong (p₁)) o
suc-rᵀ {y = y} p₁ (ptr {e = e₀} {e′ = ε} o) = suc-rᵀ {y = trQ ε (y)} (trᵀ-cong {e = e₀} {e′ = ε} (p₁)) o
suc-rᵀ {y = y} p₁ (ptr⁻ {e = e₀} {e′ = ε} o) = suc-rᵀ {y = tr⁻Q ε (y)} (tr⁻ᵀ-cong {e = e₀} {e′ = ε} (p₁)) o

ĉ-rᵀ : ∀ {m c φ χ ψ ρ c₀ z} {zg : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {x : Q m c φ χ} {o₀ : Q m c ψ ρ} {o : (η : Ordᴵ) → c₀ ⊑ᴵ η → Q m c ψ ρ} → x ⊑ᵀ o₀ → x ⊑ᵀ qĉ c₀ z zg o₀ o
ŝ-rᵀ : ∀ {m c φ χ ψ ρ c₀} {x : Q m c φ χ} {t : Q m c ψ ρ} {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → Q m c ψ ρ} → x ⊑ᵀ t → x ⊑ᵀ qŝ c₀ t g
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
ŝ-rᵀ {c₀ = c₀} {x = x} {t = t} {g = g} p₁ (top {ev = ev} {ev′ = ev′} {p = p₀} {p′ = pt} {ok = ok} {ok′ = ok′} {e = e} {e′ = e′} o) = ŝ-rᴱ {c = c₀} {x = ψ̄ᵠ ok e x ev p₀} {t₀ = ψ̄ᵠ ok′ e′ t ev′ pt} {g = λ η d → ψ̄ᵠ ok′ e′ (g η d) ev′ pt} (ψ̄-cong p₁) o
ŝ-rᵀ {c₀ = c₀} {t = t} {g = g} p₁ (pa {W = W} r o) = ŝ-rᵀ {c₀ = c₀} {t = W ⊞ t} {g = λ η d → W ⊞ g η d} (⊞-cong r (p₁)) o
ŝ-rᵀ {c₀ = c₀} {t = t} {g = g} p₁ (pψ {q = q} o) = ŝ-rᵀ {c₀ = c₀} {t = ψᵠ q (t)} {g = λ η d → ψᵠ q (g η d)} (ψ-cong {q = q} (p₁)) o
ŝ-rᵀ {c₀ = c₀} {t = t} {g = g} p₁ (pΨ {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} o) = ŝ-rᵀ {c₀ = c₀} {t = Ψ qH ok e pt (t)} {g = λ η d → Ψ qH ok e pt (g η d)} (Ψ-cong {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} (p₁)) o
ŝ-rᵀ {c₀ = c₀} {t = t} {g = g} p₁ (pι {q = q} o) = ŝ-rᵀ {c₀ = c₀} {t = ι q (t)} {g = λ η d → ι q (g η d)} (ι-cong {q = q} (p₁)) o
ŝ-rᵀ {c₀ = c₀} {t = t} {g = g} p₁ (pD {q = qd} o) = ŝ-rᵀ {c₀ = c₀} {t = ι↓ {α = zero} qd (t)} {g = λ η d → ι↓ {α = zero} qd (g η d)} (ιD-cong (p₁)) o
ŝ-rᵀ {c₀ = c₀} {t = t} {g = g} p₁ (ptr {e = e₀} {e′ = ε} o) = ŝ-rᵀ {c₀ = c₀} {t = trQ ε (t)} {g = λ η d → trQ ε (g η d)} (trᵀ-cong {e = e₀} {e′ = ε} (p₁)) o
ŝ-rᵀ {c₀ = c₀} {t = t} {g = g} p₁ (ptr⁻ {e = e₀} {e′ = ε} o) = ŝ-rᵀ {c₀ = c₀} {t = tr⁻Q ε (t)} {g = λ η d → tr⁻Q ε (g η d)} (tr⁻ᵀ-cong {e = e₀} {e′ = ε} (p₁)) o
ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {x = x} {o₀ = o₀} {o = o₁} p₁ (top {ev = ev} {ev′ = ev′} {p = p₀} {p′ = pt} {ok = ok} {ok′ = ok′} {e = e} {e′ = e′} o) = ĉ-rᴱ {c = c₀} {t₀ = z} {g = zg} {x = ψ̄ᵠ ok e x ev p₀} {o₀ = ψ̄ᵠ ok′ e′ o₀ ev′ pt} {o = λ η d → ψ̄ᵠ ok′ e′ (o₁ η d) ev′ pt} (ψ̄-cong p₁) o
ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = o₀} {o = o₁} p₁ (pa {W = W} r o) = ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = W ⊞ o₀} {o = λ η d → W ⊞ o₁ η d} (⊞-cong r (p₁)) o
ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = o₀} {o = o₁} p₁ (pψ {q = q} o) = ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = ψᵠ q (o₀)} {o = λ η d → ψᵠ q (o₁ η d)} (ψ-cong {q = q} (p₁)) o
ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = o₀} {o = o₁} p₁ (pΨ {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} o) = ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = Ψ qH ok e pt (o₀)} {o = λ η d → Ψ qH ok e pt (o₁ η d)} (Ψ-cong {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} (p₁)) o
ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = o₀} {o = o₁} p₁ (pι {q = q} o) = ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = ι q (o₀)} {o = λ η d → ι q (o₁ η d)} (ι-cong {q = q} (p₁)) o
ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = o₀} {o = o₁} p₁ (pD {q = qd} o) = ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = ι↓ {α = zero} qd (o₀)} {o = λ η d → ι↓ {α = zero} qd (o₁ η d)} (ιD-cong (p₁)) o
ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = o₀} {o = o₁} p₁ (ptr {e = e₀} {e′ = ε} o) = ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = trQ ε (o₀)} {o = λ η d → trQ ε (o₁ η d)} (trᵀ-cong {e = e₀} {e′ = ε} (p₁)) o
ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = o₀} {o = o₁} p₁ (ptr⁻ {e = e₀} {e′ = ε} o) = ĉ-rᵀ {c₀ = c₀} {z = z} {zg = zg} {o₀ = tr⁻Q ε (o₀)} {o = λ η d → tr⁻Q ε (o₁ η d)} (tr⁻ᵀ-cong {e = e₀} {e′ = ε} (p₁)) o

limᵢ-rᴱ : ∀ {k k′ j} {x : Ordˢ k} {q : j <ᴵ k′} {g : Uˢ j (<→◃ q) → Ordˢ k′} →
         (∀ z → z ≅ˢ Ωˢ j → x ⊑ᴱ g (intoˢ (<→◃ q) z)) → x ⊑ᴱ Ord₊ˢ.limᵢ q g
qi-rᵀ : ∀ {m c φ χ ψ ρ j} {x : Q m c φ χ} {ac : ∀ {L} → Ev L ψ → j <ᴵ L} {f : Ordˢ j → Q m c ψ ρ} →
         (∀ z → z ≅ˢ Ωˢ j → x ⊑ᵀ f z) → x ⊑ᵀ qi ac f
limᵢ-rᴱ {q = ()} H idO
limᵢ-rᴱ {k′ = k′} {q = q} {g = g} H (tlo o) =
  qi-rᵀ {ac = λ e → cvFlo k′ e q} {f = λ x → tl (flo k′) (cvFlo k′) (g (intoˢ (<→◃ q) x))} (λ z d → tl-cong (H z d)) o
limᵢ-rᴱ {j = j} {x = x} {q = q} {g = g} H (addo {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} o k ea) = limᵢ-rᴱ (λ z d →
  subst (λ u → addˢ a σ x ⊑ᴱ addˢ a′ σ′ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ′ q)) z))
        (add-congᴱ k ea (H z d))) o
limᵢ-rᴱ {j = j} {x = x} {q = q} {g = g} H (tro {e = e} {e′ = e′} o) = limᵢ-rᴱ (λ z d →
  subst (λ u → trˢ e x ⊑ᴱ trˢ e′ (g (intoˢ (<→◃ q) (backˢ (resˢ q e′) u)))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e′))) z))
        (tr-congᴱ (H (backˢ (resˢ q e′) z) (≅ˢ-trans (backˢ-≅ q e′ d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (resˢ q e′)))))))) o
limᵢ-rᴱ {j = j} {x = x} {q = q} {g = g} H (tr⁻o {e = e} {e′ = e′} o) = limᵢ-rᴱ (λ z d →
  subst (λ u → tr⁻ˢ e x ⊑ᴱ tr⁻ˢ e′ (g (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e′) u)))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e′))) z))
        (tr⁻-congᴱ (H (backˢ (res⁻ˢ q e′) z) (≅ˢ-trans (back⁻ˢ-≅ q e′ d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (res⁻ˢ q e′)))))))) o
qi-rᵀ {j = j} {x = x} {ac = ac} {f = f} H (top {ev = ev} {ev′ = ev′} {p = p₀} {p′ = pt} {ok = ok} {ok′ = ok′} {e = e} {e′ = e′} o) with <ᴵ-dec (ac ev′) pt
... | injᵃ (via d s) = limᵢ-rᴱ {q = s} {g = λ y → ψ̄ᵠ ok′ e′ (f (tr⁻ˢ d (outˢ (<→◃ s) y))) ev′ pt} (λ z d₁ →
        subst (λ u → ψ̄ᵠ ok e x ev p₀ ⊑ᴱ ψ̄ᵠ ok′ e′ (f (tr⁻ˢ d u)) ev′ pt) (sym (out-intoˢ (<→◃ s) z))
              (ψ̄-cong (H (tr⁻ˢ d z) (tr⁻ˢ-≅ d (≅ˢ-trans d₁ (Ωˢ-≅ (≅ᴵ-sym d))))))) o
... | injᵇ _ = lim-rᴱ {x = ψ̄ᵠ ok e x ev p₀} {h = λ i → ψ̄ᵠ ok′ e′ (f (iter (λ w → ψ̄ᵠ ok′ e′ (f w) ev′ (ac ev′)) (Ωˢ j) i)) ev′ pt} 0 (ψ̄-cong (H (Ωˢ j) (Ωˢ-refl j))) o
... | injᶜ _ = lim-rᴱ {x = ψ̄ᵠ ok e x ev p₀} {h = λ i → ψ̄ᵠ ok′ e′ (f (iter (λ w → ψ̄ᵠ ok′ e′ (f w) ev′ (ac ev′)) (Ωˢ j) i)) ev′ pt} 0 (ψ̄-cong (H (Ωˢ j) (Ωˢ-refl j))) o
qi-rᵀ {ac = ac} {f = f} H (pa {W = W} r o) = qi-rᵀ {ac = λ u → ac (proj₂ u)} {f = λ y → W ⊞ f y} (λ z d₁ → ⊞-cong r (H z d₁)) o
qi-rᵀ {ac = ac} {f = f} H (pψ {q = q} o) = qi-rᵀ {ac = λ u → ac (proj₂ u)} {f = λ y → ψᵠ q (f y)} (λ z d₁ → ψ-cong {q = q} (H z d₁)) o
qi-rᵀ {ac = ac} {f = f} H (pΨ {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} o) = qi-rᵀ {ac = λ u → ac (proj₂ u)} {f = λ y → Ψ qH ok e pt (f y)} (λ z d₁ → Ψ-cong {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} (H z d₁)) o
qi-rᵀ {ac = ac} {f = f} H (pι {q = q} o) = qi-rᵀ {ac = ac} {f = λ y → ι q (f y)} (λ z d₁ → ι-cong {q = q} (H z d₁)) o
qi-rᵀ {ac = ac} {f = f} H (pD {q = qd} o) = qi-rᵀ {ac = ac} {f = λ y → ι↓ {α = zero} qd (f y)} (λ z d₁ → ιD-cong (H z d₁)) o
qi-rᵀ {ac = ac} {f = f} H (ptr {e = e₀} {e′ = ε} o) = qi-rᵀ {ac = ac} {f = λ y → trQ ε (f y)} (λ z d₁ → trᵀ-cong {e = e₀} {e′ = ε} (H z d₁)) o
qi-rᵀ {ac = ac} {f = f} H (ptr⁻ {e = e₀} {e′ = ε} o) = qi-rᵀ {ac = ac} {f = λ y → tr⁻Q ε (f y)} (λ z d₁ → tr⁻ᵀ-cong {e = e₀} {e′ = ε} (H z d₁)) o

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

