# 序数高度: 严格增长

> 由 `Survey/scripts/ladderord/mk_ord.py` 从 [LadderInfStrict2](LadderInfStrict2.lagda.md) 生成, 对结构 `HtB` 参数化. **判决: HOLDS (对结构参数, 编译过).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 除了名字逐字相同. 下面的说明是原文件的.
>
> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderOrd](LadderOrd.lagda.md). 对高度结构 `HtB` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFStrict2](LadderNFStrict2.lagda.md) 生成, 下面的说明是原文件的. `Sᵀ`, `Climbᵀ` 与 `OCF.Free.Strict` 同形. `𝟏⊑Ω̇`: 层 $k$ 的 $1$ (`𝟏q`) 低于 $\dot\Omega_k$, 对一切 $m$, $k$; 上移经 `omk-go`. `One`: 经 `pι` 时只读 $\mathrm{Nd}$ 上下文 (`ι q` 之下不再是 `ι↓`, 这是 `Ctxᶜ` 的一部分). 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.LadderOrdStrict2 (𝕊 : HtB) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ; Ωˢ; addˢ; _+ˢ_; 𝟎ˢ)
open import OCF.Free.Eq using (≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; _≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; upˡ; upʳ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ; trˢ-≅; tr⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; addˢ-≅; s-invˢ; l-invˢ; i-respˢ; u-reflˢ; ŝ-refl₀; ĉ-refl₀; self-trˢ; self-tr⁻ˢ)
open import OCF.Free.Floor using (_∼ᶠ_; ∼ᶠ-refl; fz∼; ⊔∼; Flr; fz; fk; Ev; Run; flo; cvFlo; toFlo; ∅ᴿ; _⊔_; bound)
open import OCF.Free.Force using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open import OCF.Align.LadderOrdCx 𝕊
open import OCF.Align.LadderOrdRules 𝕊
open import OCF.Align.LadderOrdRules2 𝕊
open import OCF.Align.LadderOrdRules3 𝕊
open import OCF.Align.LadderOrdStrict 𝕊
open import Data.Bool using (Bool; true; false)
open import OCF.Free.Eq using (backˢ-≅; back⁻ˢ-≅; ≅ˢ-trans)
open Ord-Ord using (iter)
open Restrˢ
open RestrQ
```

## §1 $1$ 的位置

```agda
⊑ᵀ-Rˡʷ : ∀ {m c φ₀ χ₀ φ₁ χ₁ ψ ρ} {x : Q m c φ₀ χ₀} {y : Q m c φ₁ χ₁} {w : Q m c ψ ρ} (le : ∀ {L} → Ev L ψ → Ev L φ₁) (lc : Sub m ρ χ₁) → Rq m c c x y → y ⊑ᵀ w → x ⊑ᵀ w
⊑ᵀ-Rˡʷ le lc e i {C} {C′} o G′ = Goodᴺ-tr (≅ᶻ-sym d) (proj₁ J) , ⊑-trans (≅→⊑ (forceᴺ-≅ d (Goodᴺ-tr (≅ᶻ-sym d) (proj₁ J)) (proj₁ J))) (proj₂ J)
  where
  J = i (≈ᶜ-wkˡ le lc (≈ᶜ-reflʳ o)) G′
  d = toZ-≅ (runᶜ-≅ (≈ᶜ-wkʳ le lc o) e)

R-tr₂ : ∀ {m a b a′ b′ φ χ ψ ρ} (e : a ≅ᴵ a′) (e′ : b ≅ᴵ b′) {x : Q m a φ χ} {y : Q m b ψ ρ} → Rq m a b x y → Rq m a′ b′ (trQ e x) (trQ e′ y)
R-tr₂ e e′ r = R-trˡ e (R-trʳ e′ r)

R-tr⁻₂ : ∀ {m a b a′ b′ φ χ ψ ρ} (e : a′ ≅ᴵ a) (e′ : b′ ≅ᴵ b) {x : Q m a φ χ} {y : Q m b ψ ρ} → Rq m a b x y → Rq m a′ b′ (tr⁻Q e x) (tr⁻Q e′ y)
R-tr⁻₂ e e′ r = R-tr⁻ˡ e (R-tr⁻ʳ e′ r)

fz-upd : ∀ m i → fz ∼ᶠ cap (κ fz) m fz i
fz-upd m i with tri i m
... | tlt _ = fz∼
... | teq _ = fz∼
... | tgt _ = fz∼

R𝟏D : ∀ {n m} (qd : n <ᴸ m) k → Rq m zero zero (qs {φ = fz} {χ = κ fz} q0) (ι↓ {n = n} {α = zero} qd (𝟏q k))
R𝟏D {n} qd zero = rs fz∼ (λ i q → fz-upd n i) rz
R𝟏D qd (suc k) = rwkʳ (R𝟏D qd k)
R𝟏D qd (lim f s) = rwkʳ (R𝟏D qd (f 0))

𝟏-D : ∀ {n m k φ χ} {qd : n <ᴸ m} {t : Q n k φ χ} → 𝟏q k ⊑ᵀ t → 𝟏q {m} zero ⊑ᵀ ι↓ {α = zero} qd t
𝟏-D {n} {m} {k} {qd = qd} h = ⊑ᵀ-Rˡʷ (λ _ → tt) (upd-sub n (λ i q _ → tt) (λ e → e)) (R𝟏D qd k) (ιD-cong h)

R𝟏-tr : ∀ {m a b} (e : a ≅ᴵ b) → Rq m b b (𝟏q b) (trQ e (𝟏q a))
R𝟏-tr z≅ = rs fz∼ (λ i q → fz∼) rz
R𝟏-tr (s≅ e) = rob {r = zero} {r′ = zero} (≅ᴵ-refl _) (R𝟏-tr e) (rs fz∼ (λ i q → fz∼) rz)
R𝟏-tr (l≅ h) = rob {r = self 0} {r′ = self 0} (≅ᴵ-refl _) (R𝟏-tr (h 0)) (rs fz∼ (λ i q → fz∼) rz)

R𝟏-tr⁻ : ∀ {m a b} (e : a ≅ᴵ b) → Rq m a a (𝟏q a) (tr⁻Q e (𝟏q b))
R𝟏-tr⁻ z≅ = rs fz∼ (λ i q → fz∼) rz
R𝟏-tr⁻ (s≅ e) = rob {r = zero} {r′ = zero} (≅ᴵ-refl _) (R𝟏-tr⁻ e) (rs fz∼ (λ i q → fz∼) rz)
R𝟏-tr⁻ (l≅ h) = rob {r = self 0} {r′ = self 0} (≅ᴵ-refl _) (R𝟏-tr⁻ (h 0)) (rs fz∼ (λ i q → fz∼) rz)

𝟏-tr : ∀ {m a b φ χ} (e : a ≅ᴵ b) {t : Q m a φ χ} → 𝟏q a ⊑ᵀ t → 𝟏q b ⊑ᵀ trQ e t
𝟏-tr e h = ⊑ᵀ-Rˡ (R𝟏-tr e) (trᵀ-cong {e = e} {e′ = e} h)

𝟏-tr⁻ : ∀ {m a b φ χ} (e : a ≅ᴵ b) {t : Q m b φ χ} → 𝟏q b ⊑ᵀ t → 𝟏q a ⊑ᵀ tr⁻Q e t
𝟏-tr⁻ e h = ⊑ᵀ-Rˡ (R𝟏-tr⁻ e) (tr⁻ᵀ-cong {e = e} {e′ = e} h)

-- ι↓ qd (Ω̇ n (suc a)) 的节点函数
Hι : ∀ {n m} (qd : n <ᴸ m) a ξ ζ → Q n a ξ ζ → Q m zero (ξ ⊔ Fl) (lo n ζ ∪ cap (κ Fl) n (flo (suc a)))
Hι {n} qd a ξ ζ z = qwk (λ e → e) (⇑ (c-∪ {lo n ζ} {κ Fl} _)) (ι↓ qd (qwk proj₁ (λ i q e → subst (Ev _) (lo-lt ζ q) (proj₁ e)) (omk zero z (ι zero z))))

X𝟏 : Ht → Set
X𝟏 m = ∀ k → 𝟏q {m} k ⊑ᵀ Ω̇ m k

𝟏-rowC : ∀ {m n} (q : n <ᴸ m) → X𝟏 n → 𝟏q {m} zero ⊑ᵀ rowC q (Ω̇ n)
𝟏-rowC q I = cl-rᵀ (wk-rᵀ (𝟏-D (I (suc zero))))

𝟏-row : ∀ m → (∀ {n} → n <ᴸ m → X𝟏 n) → (v : View _<ᴸ_ h₀ m) → 𝟏q {m} zero ⊑ᵀ rowV m (ΩI m) v
𝟏-row _ I base = clo-rᵀ (qi-rᵀ (λ z d → wk-rᵀ (tl-cong {x = 𝟏} {y = z} (⊑ᴱ-≅ʳ (Ω1ᴱ zero) (≅ˢ-sym d)))))
𝟏-row m I (clos q) = subst (λ X → 𝟏q {m} zero ⊑ᵀ rowC q X) (sym (ΩI≡ q)) (𝟏-rowC q (I q))
𝟏-row m I (chain F qs₁) = lim-rᵀ 0 (wk-rᵀ (R→⊑ᵀ (R𝟏 zero)))

F𝟏 : ∀ m → (∀ {n} → n <ᴸ m → X𝟏 n) → X𝟏 m
F𝟏 m I zero = 𝟏-row m I (view m)
F𝟏 m I (suc k) = Ω-rᵀ (λ ξ ζ z rr f → wk-rᵀ (omk-go zero zero (R𝟏 k) (𝟏-up k zero) rr (R-ι zero zero rr) (λ o G′ → f (R𝟏 k) (F𝟏 m I k) (sh-≈ zero o) G′)))
F𝟏 m I (lim f s) = lim-rᵀ 0 (omk-go (self 0) (self 0) (R𝟏 (f 0)) (𝟏-up (f 0) (self 0)) (RΩ̇ m (≅ᴵ-refl _)) (R-ι (self 0) (self 0) (RΩ̇ m (≅ᴵ-refl _))) (λ o G′ → F𝟏 m I (f 0) (sh-≈ (self 0) o) G′))

𝟏⊑Ω̇ : ∀ m k → 𝟏q {m} k ⊑ᵀ Ω̇ m k
𝟏⊑Ω̇ m = F𝟏 m (Rec X𝟏 F𝟏 m)

nd-𝟏 : ∀ {m} k (C : Cx m k fz (κ fz)) → Nd C → runᶜ C (𝟏q k) ≡ runᶜ C (qs q0)
nd-𝟏 zero C n = refl
nd-𝟏 (suc k) C n = nd-omk zero C n (𝟏q k) (qs q0)
nd-𝟏 (lim f s) C n = nd-omk (self 0) C n (𝟏q (f 0)) (qs q0)

-- 只在 Nd 上下文读 1
One : ∀ {m c φ χ} → Q m c φ χ → Set
One {m} {c} {φ} {χ} y = ∀ {C₀ : Cx m c fz (κ fz)} {C′ : Cx m c φ χ} → C₀ ≈ᶜ C′ → Nd C′ → (G′ : Goodᴺ (toZ (runᶜ C′ y))) → Σ (Goodᴺ (toZ (runᶜ C₀ (qs q0)))) λ G → forceᴺ _ G ⊑ forceᴺ _ G′

⊑→One : ∀ {m c φ χ} {y : Q m c φ χ} → 𝟏q c ⊑ᵀ y → One y
⊑→One {c = c} h {C₀} o n G′ = subst (λ v → Σ (Goodᴺ (toZ v)) λ G → forceᴺ _ G ⊑ forceᴺ _ G′) (nd-𝟏 c C₀ (Nd-≈ o n)) (h o G′)

One-ι : ∀ {m c d φ χ} (q : c ◃ d) {y : Q m c φ χ} → One y → One (ι q y)
One-ι q h o n G′ = h (pι {q = q} o) tt G′

One-tr : ∀ {m a b φ χ} (e : a ≅ᴵ b) {y : Q m a φ χ} → One y → One (trQ e y)
One-tr e h o n G′ = h (ptr {e = e} {e′ = e} o) n G′

One-tr⁻ : ∀ {m a b φ χ} (e : a ≅ᴵ b) {y : Q m b φ χ} → One y → One (tr⁻Q e y)
One-tr⁻ e h o n G′ = h (ptr⁻ {e = e} {e′ = e} o) n G′

S1ᵀ : ∀ {m c φ χ i ℓ w} {t : Q m c φ χ} {ok : Ok w} {e : Eh h₀ m w χ} {ev : Ev ℓ φ} {p : i <ᴵ ℓ} → One t → Ord₊ˢ.suc (Ωˢ i) ⊑ᴱ ψ̄ᵠ ok e t ev p
S1ᵀ {c = c} {i = i} {ok = ok} h {O} {O′} o G′ = proj₁ K , ⊑-trans (proj₂ K) (proj₂ J)
  where
  J = h {C₀ = top {ℓ = suc i} O tt zero ok (λ j k r → tt)} (top o) tt G′
  K = suc-iter {w = Ωˢ i} (Ωˢ-refl i) (Ω1ᴱ i) (≈ᵒ-reflˡ o) (proj₁ J)

```

## §2 严格关系

```agda

infix 4 _≺ᴱ_ _≺ᵀ_
_≺ᴱ_ : ∀ {k k′} → Ordˢ k → Ordˢ k′ → Set
_≺ᴱ_ {k} {k′} x y = ∀ {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → Ctx O′ → (G′ : Goodᴺ (toZ (run O′ y))) →
  Σ (Goodᴺ (toZ (run O x))) λ G → forceᴺ _ G ≺ forceᴺ _ G′

_≺ᵀ_ : ∀ {m c φ χ ψ ρ} → Q m c φ χ → Q m c ψ ρ → Set
_≺ᵀ_ {m} {c} {φ} {χ} {ψ} {ρ} x y = ∀ {C : Cx m c φ χ} {C′ : Cx m c ψ ρ} → C ≈ᶜ C′ → Ctxᶜ C′ → (G′ : Goodᴺ (toZ (runᶜ C′ y))) →
  Σ (Goodᴺ (toZ (runᶜ C x))) λ G → forceᴺ _ G ≺ forceᴺ _ G′

Sim∼-κ : ∀ {m} (χ : Fv) → Sim∼ m χ χ
Sim∼-κ = Sim∼-refl

⊞𝟏 : ∀ {m a b} t (X : Q m t a b) → X ⊞ 𝟏q t ≡ qs (qwk proj₁ (λ i q → proj₁) X)
⊞𝟏 zero X = refl
⊞𝟏 (suc t) X = refl
⊞𝟏 (lim f s) X = refl

Sᵛ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} {a : Ordˢ k} {a′ : Ordˢ k′} → O ≈ᵒ O′ → a ≅ˢ a′ → a′ ≅ˢ a′ →
     (G′ : Goodᴺ (toZ (run O′ (Ord₊ˢ.suc a′)))) → Σ (Goodᴺ (toZ (run O a))) λ G → forceᴺ _ G ≺ forceᴺ _ G′
Sᵀ : ∀ {m c φ χ ψ ρ φ₂ χ₂} {C : Cx m c φ χ} {C′ : Cx m c ψ ρ} {Cʷ : Cx m c φ₂ χ₂} {a : Q m c φ χ} {a′ : Q m c φ₂ χ₂} → C ≈ᶜ C′ → C′ ≈ᶜ Cʷ → Rq m c c a a′ → Rq m c c a′ a′ →
     (G′ : Goodᴺ (toZ (runᶜ Cʷ (qs a′)))) → Σ (Goodᴺ (toZ (runᶜ C a))) λ G → forceᴺ _ G ≺ forceᴺ _ G′
Sᵛ idO d d′ (gs H) = Goodᴺ-tr (≅ᶻ-sym (toZ-≅ d)) H , ≺z (forceᴺ-≅ (toZ-≅ d) (Goodᴺ-tr (≅ᶻ-sym (toZ-≅ d)) H) H)
Sᵛ (tlo o) d d′ G′ = Sᵀ o (≈ᶜ-reflʳ o) (R-tl d) (R-tl d′) G′
Sᵛ (addo o k ee) d d′ G′ = Sᵛ o (addˢ-≅ k ee d) (addˢ-≅ (≅ᴵ-refl _) (≅ˢ-reflʳ ee) d′) G′
Sᵛ (tro {e = e} {e′ = e′} o) d d′ G′ = Sᵛ o (trˢ-≅ e (≅-trˢ e′ d)) (self-trˢ e′ d′) G′
Sᵛ (tr⁻o {e = e} {e′ = e′} o) d d′ G′ = Sᵛ o (tr⁻ˢ-≅ e (≅-tr⁻ˢ e′ d)) (self-tr⁻ˢ e′ d′) G′
Sᵀ {Cʷ = top Oʷ evʷ pʷ okʷ eʷ} {a = a} {a′ = a′} (top {i = i} {ev = ev} {p = p} {ok = ok} {e = e} o) (top o′) ra ra′ G′ =
  proj₁ K , proj₂ J (proj₂ K)
  where
  w′ = ψ̄ᵠ okʷ eʷ a′ evʷ pʷ
  er = R→≈ᵠ ra′ okʷ eʷ okʷ eʷ evʷ pʷ evʷ pʷ (≅ᴵ-refl i)
  J = suc-iter {w = w′} er (⊑ᴱ-trans (Ω1ᴱ i) (F0ᵀ ra′)) (≈ᵒ-reflʳ o′) G′
  K = Sᵛ (≈ᵒ-trans′ o o′) (R→≈ᵠ ra ok e okʷ eʷ ev p evʷ pʷ (≅ᴵ-refl i)) er (proj₁ J)
Sᵀ (pa {a = α} {b = β} rW o) (pa _ o′) ra ra′ G′ =
  Sᵀ o o′ (R-⊞ (∼ᶠ-refl α) (Sim∼-refl β) rW ra) (R-⊞ (∼ᶠ-refl α) (Sim∼-refl β) rW ra′) G′
Sᵀ {m} {Cʷ = pψ {t = t} q C₁ʷ} {a = a} {a′ = a′} (pψ o) (pψ o′) ra ra′ G′ =
  proj₁ K , proj₂ J (proj₂ K)
  where
  X = ψᵠ q a′
  rX = R-ψᵠ q q (≅ᴵ-refl t) ra′
  J = subst (λ w → Σ (Goodᴺ (toZ (runᶜ (wkC (λ e → e , tt) (λ i q₁ e → e , tt) C₁ʷ) w))) λ G → forceᴺ _ G ⊑ forceᴺ _ G′) (⊞𝟏 t X)
        (lim-rᵀ {x = X ⊞ 𝟏q t} {F = repᵠ X} 2 (wk-rᵀ (⊞-cong rX (P0ᵀ {q = q} ra′ (𝟏⊑Ω̇ m t))))
          (≈ᶜ-wkˡ (λ e → e , tt) (λ i q₁ e → e , tt) (≈ᶜ-reflʳ o′)) G′)
  K = Sᵀ {a = ψᵠ q a} {a′ = qwk proj₁ (λ i q₁ → proj₁) X} o (≈ᶜ-wkʳ (λ e → e , tt) (λ i q₁ e → e , tt) o′) (rwkʳ (R-ψᵠ q q (≅ᴵ-refl t) ra)) (rwk rX) (proj₁ J)
Sᵀ {m} {C = pΨ qH ok₀ e₀ p₀ C₁} {Cʷ = pΨ {H = H} {t = t} qH′ ok e p C₁ʷ} {a = a} {a′ = a′} (pΨ o) (pΨ o′) ra ra′ G′ =
  proj₁ K , proj₂ J (proj₂ K)
  where
  X = Ψ qH ok e p a′
  rX = R-Ψ qH ok e p ok e p (≅ᴵ-refl t) ra′
  J = subst (λ w → Σ (Goodᴺ (toZ (runᶜ (wkC (λ e₁ → e₁ , tt) (λ i q₁ e₁ → e₁ , tt) C₁ʷ) w))) λ G → forceᴺ _ G ⊑ forceᴺ _ G′) (⊞𝟏 t X)
        (lim-rᵀ {x = X ⊞ 𝟏q t} {F = repᵠ X} 2 (wk-rᵀ (⊞-cong rX (H0ᵀ ra′ (𝟏⊑Ω̇ H t))))
          (≈ᶜ-wkˡ (λ e₁ → e₁ , tt) (λ i q₁ e₁ → e₁ , tt) (≈ᶜ-reflʳ o′)) G′)
  K = Sᵀ {a = Ψ qH ok₀ e₀ p₀ a} {a′ = qwk proj₁ (λ i q₁ → proj₁) X} o (≈ᶜ-wkʳ (λ e₁ → e₁ , tt) (λ i q₁ e₁ → e₁ , tt) o′) (rwkʳ (R-Ψ qH ok₀ e₀ p₀ ok e p (≅ᴵ-refl t) ra)) (rwk rX) (proj₁ J)
Sᵀ (pι {q = q} o) (pι o′) ra ra′ G′ = Sᵀ o o′ (R-ι q q ra) (R-ι q q ra′) G′
Sᵀ (pD {q = qd} o) (pD o′) ra ra′ G′ = Sᵀ o o′ (R-ι↓ qd (≅ᴵ-refl _) ra) (R-ι↓ qd (≅ᴵ-refl _) ra′) G′
Sᵀ (ptr {e = e} o) (ptr {e′ = ε} o′) ra ra′ G′ = Sᵀ o o′ (R-trˡ e (R-trʳ ε ra)) (R-trˡ ε (R-trʳ ε ra′)) G′
Sᵀ (ptr⁻ {e = e} o) (ptr⁻ {e′ = ε} o′) ra ra′ G′ = Sᵀ o o′ (R-tr⁻ˡ e (R-tr⁻ʳ ε ra)) (R-tr⁻ˡ ε (R-tr⁻ʳ ε ra′)) G′

Rs : ∀ {k k′} {a : Ordˢ k} {y : Ordˢ k′} → a ≅ˢ a → Ord₊ˢ.suc a ⊑ᴱ y → a ≺ᴱ y
Rs ea sa o c G′ = proj₁ K , proj₂ J (proj₂ K)
  where
  J = sa o G′
  K = Sᵛ (≈ᵒ-reflˡ o) ea ea (proj₁ J)
```

## §3 `Climb`

```agda

back-sucᴱ : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} → u ≅ˢ u → Ord₊ˢ.suc (Ωˢ (repˢ (resˢ q e))) ⊑ᴱ u → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ backˢ (resˢ q e) u
back-sucᴱ {j} zero (s≅ e) eu h = ⊑ᴱ-≅ˡ {x′ = tr⁻ˢ e (Ord₊ˢ.suc (Ωˢ _))} (s≅ (≅ᴵ-refl _) (≅ˢ-sym (tr⁻ˢ-≅ e (Ωˢ-≅ (≅ᴵ-sym e))))) (tr⁻-congᴱ {e = e} {e′ = e} h)
back-sucᴱ (suc q)   (s≅ e) eu h = back-sucᴱ q e eu h
back-sucᴱ (lim n q) (l≅ f) eu h = back-sucᴱ q (f n) eu h

back⁻-sucᴱ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} → u ≅ˢ u → Ord₊ˢ.suc (Ωˢ (repˢ (res⁻ˢ q e))) ⊑ᴱ u → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ backˢ (res⁻ˢ q e) u
back⁻-sucᴱ {j} zero (s≅ e) eu h = ⊑ᴱ-≅ˡ {x′ = trˢ e (Ord₊ˢ.suc (Ωˢ _))} (s≅ (≅ᴵ-refl _) (≅ˢ-sym (trˢ-≅ e (Ωˢ-≅ e)))) (tr-congᴱ {e = e} {e′ = e} h)
back⁻-sucᴱ (suc q)   (s≅ e) eu h = back⁻-sucᴱ q e eu h
back⁻-sucᴱ (lim n q) (l≅ f) eu h = back⁻-sucᴱ q (f n) eu h


Pos : ∀ {m c φ χ} → Bool → Q m c φ χ → Set
Pos true  y = 𝟏q _ ⊑ᵀ y
Pos false y = One y

NdB : ∀ {m c φ χ} → Bool → Cx m c φ χ → Set
NdB true  C = ⊤
NdB false C = Nd C

Pos→One : ∀ {m c φ χ} b {y : Q m c φ χ} → Pos b y → One y
Pos→One true h = ⊑→One h
Pos→One false h = h

nb : ∀ {m c φ χ} b {C : Cx m c φ χ} → Nd C → NdB b C
nb true n = tt
nb false n = n

Ls : ∀ {m c φ₀ χ₀ φ χ} → Bool → Q m c φ₀ χ₀ → Q m c φ χ → Set
Ls {m} {c} {φ₀} {χ₀} {φ} {χ} b x y = ∀ {C : Cx m c φ₀ χ₀} {C′ : Cx m c φ χ} → C ≈ᶜ C′ → Ctxᶜ C′ → NdB b C′ → (G′ : Goodᴺ (toZ (runᶜ C′ y))) → Σ (Goodᴺ (toZ (runᶜ C x))) λ G → forceᴺ _ G ≺ forceᴺ _ G′

chainCᵀ : ∀ {m c φ₀ χ₀ φ χ j i ℓ ℓ′ w w′} (b : Bool) {ac : ∀ {L} → Ev L φ → j <ᴵ L} {f : Ordˢ j → Q m c φ χ} {x : Q m c φ₀ χ₀} {ok : Ok w} {e : Eh h₀ m w χ₀} {ok′ : Ok w′} {e′ : Eh h₀ m w′ χ} {ev : Ev ℓ φ₀} {ev′ : Ev ℓ′ φ} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} →
        (∀ {z z′} → z ≅ˢ z′ → Rq m c c (f z) (f z′)) →
        (∀ z → z ≅ˢ Ωˢ j → One (f z)) →
        (∀ z → z ≅ˢ z → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ z → Ls b x (f z)) →
        ∀ {O O′ : Obs i} → O ≈ᵒ O′ → Ctx O′ →
        (G′ : Goodᴺ (toZ (run O′ (Ord₊ˢ.lim (λ n → ψ̄ᵠ ok′ e′ (f (iter (λ w₁ → ψ̄ᵠ ok′ e′ (f w₁) ev′ (ac ev′)) (Ωˢ j) n)) ev′ p′))))) →
        Σ (Goodᴺ (toZ (run O (ψ̄ᵠ ok e x ev p)))) λ G → forceᴺ _ G ≺ forceᴺ _ G′
chainCᵀ {j = j} b {ac = ac} {f = f} {x = x} {ok = ok} {e = e} {ok′ = ok′} {e′ = e′} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} rf h1 h2 {O} {O′} o c G′ =
  proj₁ S , proj₂ L (proj₂ S)
  where
  z₁ = ψ̄ᵠ ok′ e′ (f (Ωˢ j)) ev′ (ac ev′)
  ez₁ : z₁ ≅ˢ z₁
  ez₁ = R→≈ᵠ (rf (Ωˢ-refl j)) ok′ e′ ok′ e′ ev′ (ac ev′) ev′ (ac ev′) (≅ᴵ-refl j)
  sz₁ : Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ z₁
  sz₁ = S1ᵀ (h1 _ (Ωˢ-refl j))
  y₁ = ψ̄ᵠ ok′ e′ (f z₁) ev′ p′
  ey₁ : y₁ ≅ˢ y₁
  ey₁ = R→≈ᵠ (rf ez₁) ok′ e′ ok′ e′ ev′ p′ ev′ p′ (≅ᴵ-refl _)
  L = lim-rᴱ {h = λ n → ψ̄ᵠ ok′ e′ (f (iter (λ w₁ → ψ̄ᵠ ok′ e′ (f w₁) ev′ (ac ev′)) (Ωˢ j) n)) ev′ p′} 1 (≅→⊑ᴱ {x = y₁} ey₁) (≈ᵒ-reflʳ o) G′
  S = h2 z₁ ez₁ sz₁ (top {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} {ok = ok} {ok′ = ok′} {e = e} {e′ = e′} o) c (nb b tt) (proj₁ L)

Climbᵛ : ∀ {k k₀ j} {q : j <ᴵ k} {g : Uˢ j (<→◃ q) → Ordˢ k} {x : Ordˢ k₀} →
        (∀ {z z′} → z ≅ˢ z′ → g (intoˢ (<→◃ q) z) ≅ˢ g (intoˢ (<→◃ q) z′)) →
        (∀ z → z ≅ˢ Ωˢ j → 𝟏 ⊑ᴱ g (intoˢ (<→◃ q) z)) →
        (∀ z → z ≅ˢ z → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ z → x ≺ᴱ g (intoˢ (<→◃ q) z)) → x ≺ᴱ Ord₊ˢ.limᵢ q g
Climbᵀ : ∀ {m c φ₀ χ₀ φ χ j} (b : Bool) {ac : ∀ {L} → Ev L φ → j <ᴵ L} {f : Ordˢ j → Q m c φ χ} {x : Q m c φ₀ χ₀} →
        (∀ {z z′} → z ≅ˢ z′ → Rq m c c (f z) (f z′)) →
        (∀ z → z ≅ˢ Ωˢ j → Pos b (f z)) →
        (∀ z → z ≅ˢ z → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ z → Ls b x (f z)) →
        ∀ {C : Cx m c φ₀ χ₀} {C′ : Cx m c φ χ} → C ≈ᶜ C′ → Ctxᶜ C′ → NdB b C′ → (G′ : Goodᴺ (toZ (runᶜ C′ (qi ac f)))) →
        Σ (Goodᴺ (toZ (runᶜ C x))) λ G → forceᴺ _ G ≺ forceᴺ _ G′

Climbᵛ {q = ()} rf h1 h2 idO c G′
Climbᵛ {k = k} {k₀ = k₀} {q = q} {g = g} {x = x} rf h1 h2 (tlo o) c G′ =
  Climbᵀ true {ac = λ e → cvFlo k e q} {f = λ y → tl (flo k) (cvFlo k) (g (intoˢ (<→◃ q) y))} {x = tl (flo k₀) (cvFlo k₀) x}
    (λ d → R-tl (rf d)) (λ z d → tl-cong (h1 z d)) (λ z ez sz o′ c′ _ G → h2 z ez sz (tlo o′) c′ G) o c tt G′
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
Climbᵀ {j = j} b {ac = ac} {f = f} {x = x} rf h1 h2 (top {i = i} {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} {ok = ok} {ok′ = ok′} {e = e} {e′ = e′} o) c nd G′ with <ᴵ-dec (ac ev′) p′
... | injᵃ (via d s) =
  Climbᵛ {q = s} {g = λ u → ψ̄ᵠ ok′ e′ (f (tr⁻ˢ d (outˢ (<→◃ s) u))) ev′ p′} {x = ψ̄ᵠ ok e x ev p}
    (λ {z} {z′} d₁ → subst₂ (λ u v → ψ̄ᵠ ok′ e′ (f (tr⁻ˢ d u)) ev′ p′ ≅ˢ ψ̄ᵠ ok′ e′ (f (tr⁻ˢ d v)) ev′ p′)
                           (sym (out-intoˢ (<→◃ s) z)) (sym (out-intoˢ (<→◃ s) z′))
                           (R→≈ᵠ (rf (tr⁻ˢ-≅ d (≅-tr⁻ˢ d d₁))) ok′ e′ ok′ e′ ev′ p′ ev′ p′ (≅ᴵ-refl _)))
    (λ z d₁ → subst (λ u → 𝟏 ⊑ᴱ ψ̄ᵠ ok′ e′ (f (tr⁻ˢ d u)) ev′ p′) (sym (out-intoˢ (<→◃ s) z))
                   (⊑ᴱ-trans (Ω1ᴱ i) (F0ᵀ (rf (self-tr⁻ˢ d (≅ˢ-reflˡ d₁))))))
    (λ z ez sz → subst (λ u → ψ̄ᵠ ok e x ev p ≺ᴱ ψ̄ᵠ ok′ e′ (f (tr⁻ˢ d u)) ev′ p′) (sym (out-intoˢ (<→◃ s) z))
                       (λ o′ c′ G → h2 (tr⁻ˢ d z) (self-tr⁻ˢ d ez)
                                     (⊑ᴱ-≅ˡ {x′ = tr⁻ˢ d (Ord₊ˢ.suc (Ωˢ _))} (s≅ (≅ᴵ-refl _) (≅ˢ-sym (tr⁻ˢ-≅ d (Ωˢ-≅ (≅ᴵ-sym d))))) (tr⁻-congᴱ {e = d} {e′ = d} sz))
                                     (top {ev = ev} {ev′ = ev′} {p = p} {p′ = p′} {ok = ok} {ok′ = ok′} {e = e} {e′ = e′} o′) c′ (nb b tt) G))
    o c G′
... | injᵇ _ = chainCᵀ {j = j} b {ac = ac} {f = f} {x = x} rf (λ z d → Pos→One b (h1 z d)) h2 o c G′
... | injᶜ _ = chainCᵀ {j = j} b {ac = ac} {f = f} {x = x} rf (λ z d → Pos→One b (h1 z d)) h2 o c G′
Climbᵀ b {ac = ac} {f = f} {x = x} rf h1 h2 (pa {a = α} {b = β} {W = W} rW o) (w , c) nd G′ =
  Climbᵀ true {ac = λ e → ac (proj₂ e)} {f = λ y → W ⊞ f y} {x = W ⊞ x}
    (λ d → R-⊞ (∼ᶠ-refl α) (Sim∼-refl β) rW (rf d))
    (λ z d → B1ᵀ (rf (≅ˢ-reflˡ d)) (WFl.oneW w))
    (λ z ez sz o′ c′ _ G → h2 z ez sz (pa rW o′) (w , c′) (nb b tt) G)
    o c tt G′
Climbᵀ {m} b {ac = ac} {f = f} {x = x} rf h1 h2 (pψ {t = t} {q = q} o) c nd G′ =
  Climbᵀ true {ac = λ e → ac (proj₂ e)} {f = λ y → ψᵠ q (f y)} {x = ψᵠ q x}
    (λ d → R-ψᵠ q q (≅ᴵ-refl _) (rf d))
    (λ z d → P0ᵀ {q = q} (rf (≅ˢ-reflˡ d)) (𝟏⊑Ω̇ m t))
    (λ z ez sz o′ c′ _ G → h2 z ez sz (pψ {q = q} o′) c′ (nb b tt) G)
    o c tt G′
Climbᵀ b {ac = ac} {f = f} {x = x} rf h1 h2 (pΨ {H = H} {t = t} {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} o) c nd G′ =
  Climbᵀ true {ac = λ u → ac (proj₂ u)} {f = λ y → Ψ qH ok e pt (f y)} {x = Ψ qH ok₀ e₀ p₀ x}
    (λ d → R-Ψ qH ok e pt ok e pt (≅ᴵ-refl _) (rf d))
    (λ z d → H0ᵀ (rf (≅ˢ-reflˡ d)) (𝟏⊑Ω̇ H t))
    (λ z ez sz o′ c′ _ G → h2 z ez sz (pΨ {qH = qH} {ok = ok₀} {ok′ = ok} {e = e₀} {e′ = e} {p = p₀} {p′ = pt} o′) c′ (nb b tt) G)
    o c tt G′
Climbᵀ b {ac = ac} {f = f} {x = x} rf h1 h2 (pι {q = q} o) (n₁ , c) nd G′ =
  Climbᵀ false {ac = ac} {f = λ y → ι q (f y)} {x = ι q x}
    (λ d → R-ι q q (rf d))
    (λ z d → One-ι q (Pos→One b (h1 z d)))
    (λ z ez sz o′ c′ n₂ G → h2 z ez sz (pι {q = q} o′) (n₂ , c′) (nb b tt) G)
    o c n₁ G′
Climbᵀ true {ac = ac} {f = f} {x = x} rf h1 h2 (pD {q = qd} o) c nd G′ =
  Climbᵀ true {ac = ac} {f = λ y → ι↓ {α = zero} qd (f y)} {x = ι↓ {α = zero} qd x}
    (λ d → R-ι↓ qd (≅ᴵ-refl _) (rf d))
    (λ z d → 𝟏-D {qd = qd} (h1 z d))
    (λ z ez sz o′ c′ _ G → h2 z ez sz (pD {q = qd} o′) c′ tt G)
    o c tt G′
Climbᵀ false rf h1 h2 (pD o) c () G′
Climbᵀ true {ac = ac} {f = f} {x = x} rf h1 h2 (ptr {e = e₀} {e′ = ε} o) c nd G′ =
  Climbᵀ true {ac = ac} {f = λ y → trQ ε (f y)} {x = trQ e₀ x}
    (λ d → R-tr₂ ε ε (rf d))
    (λ z d → 𝟏-tr ε (h1 z d))
    (λ z ez sz o′ c′ _ G → h2 z ez sz (ptr {e = e₀} {e′ = ε} o′) c′ tt G)
    o c tt G′
Climbᵀ false {ac = ac} {f = f} {x = x} rf h1 h2 (ptr {e = e₀} {e′ = ε} o) c nd G′ =
  Climbᵀ false {ac = ac} {f = λ y → trQ ε (f y)} {x = trQ e₀ x}
    (λ d → R-tr₂ ε ε (rf d))
    (λ z d → One-tr ε (h1 z d))
    (λ z ez sz o′ c′ n₂ G → h2 z ez sz (ptr {e = e₀} {e′ = ε} o′) c′ n₂ G)
    o c nd G′
Climbᵀ true {ac = ac} {f = f} {x = x} rf h1 h2 (ptr⁻ {e = e₀} {e′ = ε} o) c nd G′ =
  Climbᵀ true {ac = ac} {f = λ y → tr⁻Q ε (f y)} {x = tr⁻Q e₀ x}
    (λ d → R-tr⁻₂ ε ε (rf d))
    (λ z d → 𝟏-tr⁻ ε (h1 z d))
    (λ z ez sz o′ c′ _ G → h2 z ez sz (ptr⁻ {e = e₀} {e′ = ε} o′) c′ tt G)
    o c tt G′
Climbᵀ false {ac = ac} {f = f} {x = x} rf h1 h2 (ptr⁻ {e = e₀} {e′ = ε} o) c nd G′ =
  Climbᵀ false {ac = ac} {f = λ y → tr⁻Q ε (f y)} {x = tr⁻Q e₀ x}
    (λ d → R-tr⁻₂ ε ε (rf d))
    (λ z d → One-tr⁻ ε (h1 z d))
    (λ z ez sz o′ c′ n₂ G → h2 z ez sz (ptr⁻ {e = e₀} {e′ = ε} o′) c′ n₂ G)
    o c nd G′
```

## §4 $\Omega_j\prec\Omega_{j+1}$

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
