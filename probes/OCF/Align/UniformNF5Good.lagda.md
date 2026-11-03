# 层号参数化的无符号闭包定理 (六): 树层的遗传好树 `Gᵀ`

> 由 [UniformNF4Good](UniformNF4Good.lagda.md) 经脚本移植到 `Ordᴵ` 层号. 差别: `LG` 按 `◃` 分层 (四个子句, 与 `Us` 同形); `gΩ` 的字段 `lΩ` 删掉 (`Ω̇G` 是不依赖 `Psi` 的定理, 而 `lΩ` 在穿透分支要字面不同的 `Ω̇ m` 与 `Ω̇ m′` 之间搬运); `read1ᵀ` 等多 `ptr`, `ptr⁻` 两行.
>
> 接 [UniformNF5ClassF](UniformNF5ClassF.lagda.md). 结论先说:
>
> 1. **`Gᵀ c 𝓖 x`: 树 $x\in O_c$ 在上下文类 $\mathcal G$ 里遗传好.** 一个构造子一行, 与 `O₊` 同分层. 类是 `Cx c φ → Set`, 里面没有深度, 没有前缀, 没有帧: $W\oplus{-}$, $\psi{-}$, $\iota{-}$ 都只是上下文.
> 2. **`gclo`: 闭包的行不提底部.** 字段全部在树层: 分支的类族 $\mathcal G^g_\eta$ 由 `ch₀`/`chS` 沿链传递, 地板由 `dt`/`dg` 给 (`Dem`). 走到 `top` 时才取 `Bd`. 所以 $W\oplus$ 与 $\psi$ 只要把类拉回.
> 3. **`gΩ`: 与 `gi` 同形, 输入在低层 `O m`.** 输入的第 0 点 `Ω̇ m` 的好性由 `Ω̇G` 给, 不是字段.
> 4. **`𝓥` 就是 `Ctxᶜ`.** $\dot\Omega_m$ 对一切 $m$ 都在这个类里好 ([UniformNF5Omega](UniformNF5Omega.lagda.md)). 旧的 `VT` 里的 `Tw`, `LoD`, `PFl`, 帧条件都没有了: 它们要么是定理 (`read1`, `Twᵀ`), 要么落在闭包行的字段上 (`dt`, `dg`).
> 5. `G→R`: `Gᵀ` 蕴含 `Rᵒ x x`, 所以后面的定理都不要单独的自互模拟前提.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF5Good where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ)
open import OCF.Align.UniformNF3Eq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; toZ-≅; Ωˢ-≅; Ωˢ-refl; addˢ-≅; self-trˢ; self-tr⁻ˢ)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; inb; Dem; DemB; _∼ᶠ_; ∼ᶠ-refl; flo; cvFlo; toFlo)
open import OCF.Align.Stage2Label using (one⁰)
open import OCF.Align.NotFree using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3NBase using (Goodᴺ-tr)
open import OCF.Align.Uniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.Uniform4Two
open RestrO
open import OCF.Align.UniformNF5Base
open import OCF.Align.UniformNF5Rules
open import OCF.Align.UniformNF5Strict
open import OCF.Align.UniformNF5Class
open import OCF.Align.UniformNF5ClassF using (NZ-of)
```

## §1 类与语义条件

```agda
ClT : Ordᴵ → Flr → Set₁
ClT c φ = Cx c φ → Set

𝓥 : ∀ {c φ} → ClT c φ
𝓥 C = Ctxᶜ C

HonT : ∀ {c φ} → O c φ → Cx c φ → Set
HonT {φ = φ} a C = (G : Goodᴺ (toZ (runᶜ C a))) → ∀ {K} (q : InF K φ) → Dem (lvG G) q

record FlOverᵀ {c φ} (a : O c φ) (O₁ C″ : Cx c φ) : Set where
  constructor flo-overᵀ
  field
    cxoᵀ : Ctxᶜ C″
    flwᵀ : (t : O c φ) → Rᵒ c c t t → (G : Goodᴺ (toZ (runᶜ C″ t))) → Σ (Goodᴺ (toZ (runᶜ O₁ a))) λ H → forceᴺ _ H ⊑ forceᴺ _ G
open FlOverᵀ public

record AboveV (j : Ordᴵ) {c φ} (C′ : Cx c φ) (D : Obs j) : Set where
  constructor aboveV
  field
    cxV   : Ctxᶜ C′
    wrapV : (t : O c φ) → Rᵒ c c t t → Σ (Ordˢ j) λ u → (u ≅ˢ u) × (Ωˢ j ⊑ᴱ u) × (runᶜ C′ t ≅ˢ run D u)
open AboveV public

record AboveΩ {c φ m ξ} (C′ : Cx c φ) (D : Cx m ξ) : Set where
  constructor aboveΩ
  field
    cxΩ   : Ctxᶜ C′
    wrapΩ : (t : O c φ) → Rᵒ c c t t → Σ (O m ξ) λ u → Rᵒ m m u u × FlΩ̇ m u × (runᶜ C′ t ≅ˢ runᶜ D u)
open AboveΩ public

_⟪_⟫ : ∀ {c φ j} → (Cx c φ → Obs j) → ClT c φ → Cl j
(W ⟪ 𝓔 ⟫) D = Ctx D × (Σ _ λ C → 𝓔 C × (D ≈ᵒ W C))

_⟪_⟫ᵀ : ∀ {c φ m ξ} → (Cx c φ → Cx m ξ) → ClT c φ → ClT m ξ
(W ⟪ 𝓔 ⟫ᵀ) D = Ctxᶜ D × (Σ _ λ C → 𝓔 C × (D ≈ᶜ W C))
```

## §2 `Gᵀ`

```agda
module _ (c : Ordᴵ) (L : ∀ {m} → m ◃ c → ∀ {ξ} → ClT m ξ → O m ξ → Set₁) where
  data G₊ : ∀ {φ} → ClT c φ → O c φ → Set₁ where
    g0 : ∀ {φ 𝓖} → G₊ {φ} 𝓖 o0
    gs : ∀ {φ 𝓖} {a : O c φ} (𝓚 : ClT c φ) → (∀ {C} → 𝓖 C → 𝓚 C) → G₊ 𝓚 a →
         (∀ {O₁ C″} → 𝓚 O₁ → FlOverᵀ a O₁ C″ → 𝓚 C″) → (∀ {C C′} → Ctxᶜ C → C ≈ᶜ C′ → 𝓚 C′ → 𝓚 C) → (∀ {C} → 𝓚 C → HonT a C) → G₊ 𝓖 (os a)
    gl : ∀ {φ 𝓖} {F : ℕ → O c φ} → (∀ n → G₊ 𝓖 (F n)) → (∀ n → F n ⊑ᵗ F (suc n)) → G₊ 𝓖 (ol F)
    gi : ∀ {φ 𝓖 j} {ac : ∀ {L₁} → Ev L₁ φ → j <ᴵ L₁} {f : Ordˢ j → O c φ}
         (𝓖₀ : ClT c φ) → (∀ {C} → 𝓖 C → 𝓖₀ C) → (W : Cx c φ → Obs j) →
         (∀ {C} → 𝓖₀ C → ∀ u → u ≅ˢ u → run (W C) u ≅ˢ runᶜ C (f u)) →
         (∀ (𝓔 : ClT c φ) → (∀ {C} → 𝓔 C → 𝓖₀ C) → ∀ (z : Ordˢ j) → z ≅ˢ z → Good true (Inp j (W ⟪ 𝓔 ⟫)) z → G₊ 𝓔 (f z)) →
         (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) →
         (∀ {C C′} → 𝓖₀ C → AboveV j C′ (W C) → 𝓖₀ C′) →
         (∀ {C C′} → Ctxᶜ C → C ≈ᶜ C′ → 𝓖₀ C′ → 𝓖₀ C) →
         (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f z ⊑ᵗ f z′) →
         (∀ {z z′} → z ≅ˢ z′ → Rᵒ c c (f z) (f z′)) →
         G₊ 𝓖 (oi ac f)
    gŝ : ∀ {φ 𝓖 c₀} {t : O c φ} {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → O c φ} (𝓑 : Ordᴵ → ClT c φ) →
         (∀ {η η′ C} → η ≅ᴵ η′ → 𝓑 η C → 𝓑 η′ C) →
         G₊ 𝓖 t → (∀ η e → G₊ (λ C → 𝓖 C × 𝓑 η C) (g η e)) →
         Rᵒ c c t t → (∀ η e η′ e′ → η ≅ᴵ η′ → Rᵒ c c (g η e) (g η′ e′)) →
         (∀ η e → t ⊑ᵗ g η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → g η e ⊑ᵗ g η′ e′) →
         (∀ {C} → 𝓖 C → (G : Goodᴺ (toZ (runᶜ C t))) → c₀ ⊑ᴵ lvG G) →
         (∀ {C} η e → 𝓖 C → 𝓑 η C → (G : Goodᴺ (toZ (runᶜ C (g η e)))) → c₀ ⊑ᴵ lvG G) →
         (∀ {C} → 𝓖 C → (G : Goodᴺ (toZ (runᶜ C t))) → 𝓑 (lvG G) C) →
         (∀ {C} η e → 𝓖 C → 𝓑 η C → (G : Goodᴺ (toZ (runᶜ C (g η e)))) → 𝓑 (lvG G) C) →
         G₊ 𝓖 (oŝ c₀ t g)
    gĉ : ∀ {φ 𝓖 c₀ z} {zg : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {o₁ : O c φ} {o₂ : (η : Ordᴵ) → c₀ ⊑ᴵ η → O c φ}
         (ys : ℕ → Ordᶜ zero) (hy : ∀ m → HS (ys m)) (dy : ∀ m → c₀ ⊑ᴵ toLevel (ys m) (hy m))
         (G₀ : Goodᴺ z) (l₀ : forceᴺ z G₀ ≅ ys 0)
         (Gg : ∀ m → Goodᴺ (zg (toLevel (ys m) (hy m)) (dy m)))
         (lE : ∀ m → forceᴺ _ (Gg m) ≅ ys (suc m)) →
         z ≅ᶻ z → (∀ η e η′ e′ → η ≅ᴵ η′ → zg η e ≅ᶻ zg η′ e′) → Rᵒ c c o₁ o₁ → (∀ η e η′ e′ → η ≅ᴵ η′ → Rᵒ c c (o₂ η e) (o₂ η′ e′)) →
         G₊ 𝓖 o₁ → (∀ k → G₊ 𝓖 (o₂ (toLevel (ys k) (hy k)) (dy k))) →
         o₁ ⊑ᵗ o₂ (toLevel (ys 0) (hy 0)) (dy 0) → (∀ k → o₂ (toLevel (ys k) (hy k)) (dy k) ⊑ᵗ o₂ (toLevel (ys (suc k)) (hy (suc k))) (dy (suc k))) →
         G₊ 𝓖 (oĉ c₀ z zg o₁ o₂)
    gclo : ∀ {φ 𝓖} {t : O c (φ ⊔ fk zero)} {g : (η : Ordᴵ) → O c (φ ⊔ fk η)}
         (𝓖ᵗ : ClT c (φ ⊔ fk zero)) → (∀ {C} → 𝓖 C → 𝓖ᵗ C) → (𝓖ᵍ : ∀ η → ClT c (φ ⊔ fk η)) →
         (∀ {η η′} {C : Cx c (φ ⊔ fk η)} {C′ : Cx c (φ ⊔ fk η′)} → η ≅ᴵ η′ → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖ᵍ η C → 𝓖ᵍ η′ C′) →
         G₊ 𝓖ᵗ t → (∀ η → G₊ (𝓖ᵍ η) (g η)) →
         Rᵒ c c t t → (∀ η η′ → η ≅ᴵ η′ → Rᵒ c c (g η) (g η′)) →
         (∀ η → suc zero ⊑ᴵ η → t ⊑ᵗ g η) → (∀ η η′ → suc zero ⊑ᴵ η → η ⊑ᴵ η′ → g η ⊑ᵗ g η′) →
         (∀ {C} → 𝓖ᵗ C → (G : Goodᴺ (toZ (runᶜ C t))) → ∀ {K} (q : InF K φ) → Dem (lvG G) q) →
         (∀ η {C} → 𝓖ᵍ η C → (G : Goodᴺ (toZ (runᶜ C (g η)))) → ∀ {K} (q : InF K φ) → Dem (lvG G) q) →
         (∀ {C} → 𝓖ᵗ C → (G : Goodᴺ (toZ (runᶜ C t))) → ∀ {C′ : Cx c (φ ⊔ fk (lvG G))} → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖ᵍ (lvG G) C′) →
         (∀ η {C} → 𝓖ᵍ η C → (G : Goodᴺ (toZ (runᶜ C (g η)))) → ∀ {C′ : Cx c (φ ⊔ fk (lvG G))} → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖ᵍ (lvG G) C′) →
         G₊ 𝓖 (oclo t g)
    gw : ∀ {φ ψ 𝓖} {le : ∀ {L₁} → Ev L₁ ψ → Ev L₁ φ} {x : O c φ} (𝓖₁ : ClT c φ) → (∀ {C} → 𝓖 C → 𝓖₁ (wkC le C)) → G₊ 𝓖₁ x → G₊ 𝓖 (owk le x)
    gΩ : ∀ {φ 𝓖 m} {fe : ∀ {L₁} → Ev L₁ φ → Ev L₁ Fl} {r : m <ᴵ c} {h : ∀ ξ → Us m (<→◃ r) ξ → O c (ξ ⊔ φ)}
         (𝓖₀ : ∀ ξ → ClT c (ξ ⊔ φ)) →
         (∀ ξ {C} {C′ : Cx c (ξ ⊔ φ)} → 𝓖 C → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖₀ ξ C′) →
         (W : ∀ ξ → Cx c (ξ ⊔ φ) → Cx m ξ) →
         (∀ ξ {C} → 𝓖₀ ξ C → ∀ (u : O m ξ) → Rᵒ m m u u → runᶜ (W ξ C) u ≅ˢ runᶜ C (h ξ (intoU (<→◃ r) u))) →
         (∀ (𝓔 : ∀ ξ → ClT c (ξ ⊔ φ)) → (∀ ξ {C} → 𝓔 ξ C → 𝓖₀ ξ C) → ∀ ξ (z : O m ξ) → Rᵒ m m z z → L (<→◃ r) (W ξ ⟪ 𝓔 ξ ⟫ᵀ) z → G₊ (𝓔 ξ) (h ξ (intoU (<→◃ r) z))) →
         (∀ ξ {C} → 𝓖₀ ξ C → 𝓥 (W ξ C)) →
         (∀ ξ {C} {C′ : Cx c (ξ ⊔ φ)} → 𝓖₀ ξ C → AboveΩ C′ (W ξ C) → 𝓖₀ ξ C′) →
         (∀ ξ ξ′ {C : Cx c (ξ ⊔ φ)} {C′ : Cx c (ξ′ ⊔ φ)} → Ctxᶜ C → C ≈ᶜ C′ → 𝓖₀ ξ′ C′ → 𝓖₀ ξ C) →
         (∀ {ξ ξ′} {z : O m ξ} {z′ : O m ξ′} → z ⊑ᵗ z′ → h ξ (intoU (<→◃ r) z) ⊑ᵗ h ξ′ (intoU (<→◃ r) z′)) →
         (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : O m ξ) (z′ : O m ξ′) → Rᵒ m m z z′ → Rᵒ c c (h ξ (intoU (<→◃ r) z)) (h ξ′ (intoU (<→◃ r) z′))) →
         G₊ 𝓖 (oΩ fe r h)

Gᵀ : ∀ c {φ} → ClT c φ → O c φ → Set₁
LG : ∀ c {m} → m ◃ c → ∀ {ξ} → ClT m ξ → O m ξ → Set₁
Gᵀ c 𝓖 x = G₊ c (LG c) 𝓖 x
LG (suc c)   zero      𝓖 x = Gᵀ c 𝓖 x
LG (suc c)   (suc r)   𝓖 x = LG c r 𝓖 x
LG (lim f s) (self n)  𝓖 x = Gᵀ (f n) 𝓖 x
LG (lim f s) (lim n r) 𝓖 x = LG (f n) r 𝓖 x

outG : ∀ {c m} (r : m ◃ c) {ξ} {𝓖 : ClT m ξ} {z : O m ξ} → LG c r 𝓖 z → Gᵀ m 𝓖 z
outG zero      g = g
outG (suc r)   g = outG r g
outG (self n)  g = g
outG (lim n r) g = outG r g

intoG : ∀ {c m} (r : m ◃ c) {ξ} {𝓖 : ClT m ξ} {z : O m ξ} → Gᵀ m 𝓖 z → LG c r 𝓖 z
intoG zero      g = g
intoG (suc r)   g = intoG r g
intoG (self n)  g = g
intoG (lim n r) g = intoG r g

G→R : ∀ {c φ} {𝓖 : ClT c φ} {x : O c φ} → Gᵀ c 𝓖 x → Rᵒ c c x x
G→R g0 = rz
G→R {φ = φ} (gs 𝓚 inc g clk cgk ho) = rs (∼ᶠ-refl φ) (G→R g)
G→R (gl h st) = rl (λ n → G→R (h n))
G→R (gi {j = j} 𝓖₀ inc W Wf hb Wv St cg hm rf) = ri (≅ᴵ-refl j) (λ x y d → rf d)
G→R (gŝ {c₀ = c₀} 𝓑 Bc g₀ gg et eg m mm d₀ dE ch₀ chS) = rŝ (≅ᴵ-refl c₀) et eg
G→R (gĉ {c₀ = c₀} ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) = rĉ (≅ᴵ-refl c₀) ez ezg r₁ r₂
G→R {φ = φ₁} (gclo {φ = φ} 𝓖ᵗ inc 𝓖ᵍ Bc gt gg rt rg m mm dt dg ch₀ chS) = rclo (∼ᶠ-refl φ) rt rg
G→R (gw 𝓖₁ inc g) = rwk (G→R g)
G→R {c = c} (gΩ {φ = φ} {m = m} {r = r} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  rΩ (≅ᴵ-refl m) (∼ᶠ-refl φ) (λ ξ ξ′ d z z′ l → rf ξ ξ′ d z z′ (outR (<→◃ r) l))

Gmono : ∀ {c φ} {𝓖 𝓖′ : ClT c φ} {x : O c φ} → (∀ {C} → 𝓖′ C → 𝓖 C) → Gᵀ c 𝓖 x → Gᵀ c 𝓖′ x
Gmono h g0 = g0
Gmono h (gs 𝓚 v g clk cgk ho) = gs 𝓚 (λ c → v (h c)) g clk cgk ho
Gmono h (gl f st) = gl (λ n → Gmono h (f n)) st
Gmono h (gi 𝓖₀ inc W Wf hb Wv St cg hm rf) = gi 𝓖₀ (λ c → inc (h c)) W Wf hb Wv St cg hm rf
Gmono h (gŝ 𝓑 Bc g₀ gg et eg m mm d₀ dE ch₀ chS) =
  gŝ 𝓑 Bc (Gmono h g₀) (λ η e → Gmono (λ { (c , b) → h c , b }) (gg η e)) et eg m mm (λ c G → d₀ (h c) G) (λ η e c b G → dE η e (h c) b G) (λ c G → ch₀ (h c) G) (λ η e c b G → chS η e (h c) b G)
Gmono h (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) = gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ (Gmono h go) (λ k → Gmono h (gO k)) mo mO
Gmono h (gclo 𝓖ᵗ inc 𝓖ᵍ Bc gt gg rt rg m mm dt dg ch₀ chS) = gclo 𝓖ᵗ (λ c → inc (h c)) 𝓖ᵍ Bc gt gg rt rg m mm dt dg ch₀ chS
Gmono h (gw 𝓖₁ inc g) = gw 𝓖₁ (λ c → inc (h c)) g
Gmono h (gΩ 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) = gΩ 𝓖₀ (λ ξ c x o → inc₀ ξ (h c) x o) W Wf hb Wv St cg hm rf
```

## §3 `𝓥` 的封闭性

```agda
at≡ : ∀ {u v : Ordˢ zero} → u ≡ v → {Q : Ordᴵ → Set} → ((G₁ : Goodᴺ (toZ u)) → Q (lvG G₁)) → (G : Goodᴺ (toZ v)) → Q (lvG G)
at≡ refl K G = K G

fr≡ : ∀ {u v : Ordˢ zero} → u ≡ v → (G : Goodᴺ (toZ v)) → Σ (Goodᴺ (toZ u)) λ G₁ → (forceᴺ _ G₁ ⊑ forceᴺ _ G) × (forceᴺ _ G ⊑ forceᴺ _ G₁)
fr≡ = pull≅

≈-unwk : ∀ {c φ ψ χ} {le : ∀ {L₁} → Ev L₁ ψ → Ev L₁ φ} {D : Cx c χ} (C : Cx c ψ) → D ≈ᶜ wkC le C → D ≈ᶜ C
≈-unwk (top O ev p) (top o) = top o
≈-unwk (pa W C) (pa r o) = pa r (≈-unwk C o)
≈-unwk (pψ q C) (pψ o) = pψ (≈-unwk C o)
≈-unwk (pι q C) (pι o) = pι (≈-unwk C o)
≈-unwk (ptr e C) (ptr o) = ptr (≈-unwk C o)
≈-unwk (ptr⁻ e C) (ptr⁻ o) = ptr⁻ (≈-unwk C o)

Ctx-unwk : ∀ {c φ ψ} {le : ∀ {L₁} → Ev L₁ ψ → Ev L₁ φ} (C : Cx c ψ) → Ctxᶜ (wkC le C) → Ctxᶜ C
Ctx-unwk (top O ev p) c = c
Ctx-unwk (pa W C) (w , c) = w , Ctx-unwk C c
Ctx-unwk (pψ q C) c = Ctx-unwk C c
Ctx-unwk (pι q C) c = Ctx-unwk C c
Ctx-unwk (ptr e C) c = Ctx-unwk C c
Ctx-unwk (ptr⁻ e C) c = Ctx-unwk C c

wk≈ : ∀ {c φ ψ φ₁ ψ₁} {C : Cx c φ} {C′ : Cx c ψ} (le : ∀ {L₁} → Ev L₁ φ → Ev L₁ φ₁) (le′ : ∀ {L₁} → Ev L₁ ψ → Ev L₁ ψ₁) → C ≈ᶜ C′ → wkC le C ≈ᶜ wkC le′ C′
wk≈ le le′ o = ≈ᶜ-wkˡ le (≈ᶜ-wkʳ le′ o)

demUp : ∀ {K φ} (q : InF K φ) {X Y} → X ⊑ᴵ Y → Dem X q → Dem Y q
demUp ink u (inj₁ h) = inj₁ (≺ᴵ-up′ h u)
  where
  ≺ᴵ-up′ : ∀ {b A′ B′} → b ≺ᴵ A′ → A′ ⊑ᴵ B′ → b ≺ᴵ B′
  ≺ᴵ-up′ (via e q) h′ = ≺ᴵ-respˡ e (sim h′ q)
demUp ink u (inj₂ z) = inj₂ z
demUp inb u h = ⊑ᴵ-trans h u
demUp (inl q) u h = demUp q u h
demUp (inr q) u h = demUp q u h

h2N : (G : Goodᴺ (Z.suc (Z.suc Z.zero))) → one⁰ ≺ forceᴺ _ G
h2N (gs (gs gz)) = ≺z (s≅ z≅)
```

## §4 读数: 对一切上下文

旧的 `Vis.tw`/`twH` 是类的字段, 这里没有了: 层号 $\succ1$ 由严格增长 ($\Omega_0\prec\Omega_1$) 与 `read1` 读出 (`two₁`). `read1`: 尾巴 $\sqsupseteq1$ 推出层号 $\sqsupseteq1$, 对一切上下文.

```agda
oneH : (H : Goodᴺ (Z.suc Z.zero)) {X : Ordᶜ zero} → forceᴺ _ H ⊑⁰ X → suc zero ⊑⁰ X
oneH (gs gz) h = h

read1  : ∀ {k} (O : Obs k) → Ctx O → (t : Ordˢ k) → t ≅ˢ t → 𝟏 ⊑ᴱ t → (G : Goodᴺ (toZ (run O t))) → suc zero ⊑ᴵ lvG G
read1ᵀ : ∀ {c φ} (C : Cx c φ) → Ctxᶜ C → (t : O c φ) → Rᵒ c c t t → 𝟏ᵀ ⊑ᵀ t → (G : Goodᴺ (toZ (runᶜ C t))) → suc zero ⊑ᴵ lvG G
read1 idO c t et one G = toLevel-⊑ (hs hz) (forceᴺ-HS _ G) (oneH (proj₁ (one idO G)) (proj₂ (one idO G)))
read1 (tlo {k = k} C) c t et one G = read1ᵀ C c (tl (flo k) (cvFlo k) t) (R-tl et) (tl-cong one) G
read1 (addo O a σ) (afl e₁ one₁ _ , c) t et one G = read1 O c _ (addˢ-≅ (≅ᴵ-refl _) e₁ et) (add-floorᴱ {σ = σ} t one₁ et) G
read1 (tro O e) c t et one G = read1 O c _ (self-trˢ e et) (fl-tr e (s≅ z≅ z≅) one) G
read1 (tr⁻o O e) c t et one G = read1 O c _ (self-tr⁻ˢ e et) (fl-tr⁻ e (s≅ z≅ z≅) one) G
read1ᵀ (top {i = i} O ev p) c t rt one G = read1 O c (ψ̄ t ev p) (R→≈ rt ev p ev p (≅ᴵ-refl i)) (⊑ᴱ-trans (Ω1ᴱ i) (F0ᵀ rt)) G
read1ᵀ (pa W C) (w , c) t rt one G = read1ᵀ C c (W ⊕ t) (R-⊕ (∼ᶠ-refl _) (WFl.rW w) rt) (B1ᵀ rt (WFl.oneW w)) G
read1ᵀ (pψ {t = t₀} q C) c t rt one G = read1ᵀ C c (ψᵒ q t) (R-ψ q q (≅ᴵ-refl _) rt) (P0ᵀ {q = q} rt (𝟏⊑Ω̇ t₀)) G
read1ᵀ (pι q C) c t rt one G = read1ᵀ C c (ι q t) (R-ι q q rt) (ι-cong {q = q} one) G
read1ᵀ (ptr e C) c t rt one G = read1ᵀ C c (trO e t) (R-tr₂ e e rt) (trᵀ-cong {e = e} {e′ = e} one) G
read1ᵀ (ptr⁻ e C) c t rt one G = read1ᵀ C c (tr⁻O e t) (R-tr⁻₂ e e rt) (tr⁻ᵀ-cong {e = e} {e′ = e} one) G
```
