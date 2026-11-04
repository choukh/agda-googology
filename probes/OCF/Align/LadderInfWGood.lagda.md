> **机械克隆, 验收用.** 由 `LadderInfGood` 经 `Survey/scripts/laddernf/mk_infw.py` 复制, 只改导入, 落在标签阶梯的世界. 见 [LadderInfAccept](LadderInfAccept.lagda.md).

# 高度抽象: 塔上的遗传好树 `Gq`

> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 对高度结构 `HtS` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFGood](LadderNFGood.lagda.md) 生成, 下面的说明是原文件的. 接 [LadderNFClassF](LadderNFClassF.lagda.md). 与 `OCF.Free.Good` 同形, 差别:
>
> 1. **`Gq g m c 𝓖 x`: 档位 `g`.** `g₀`: 字面世界, 节点的输入类只要 `Ctxᶜ`, 对一切层号成立. `g₁`: `ι r` 的像 (eager): 节点的输入类读 `VisQT`. `g₂`: `ι↓` 可读: `qs a` 带 `Hon` ($c\sqsubseteq$ 层号), `omk` 带 $z$ 的好性. 这是 `Good true` 与 `Ordˢ` 的 `bu`, `b1` 的树版.
> 2. **`VisQ k C`: 字面前驱读数.** 对 $b<k$, $C$ 下移到层 $b$, 尾巴 $\sqsupseteq\dot\Omega_b$ 推出层号 $\succ b$. 与 `Vis` 同义, 跨层的部分全部交给下移 `shs`, 所以不需要跨层的 `⊑`. `VisQT` 多一个 $b=k$.
> 3. **`gcl`, `gΩ↓`** 与 `gclo`, `gi` 同形, 层是 `Q n k`.
> 4. **`NdG g C`: 封闭性按档位要求.** `g₀`, `g₁` 只对 `Nd` 上下文要求 (`Iota` 要造 `pι q C`, 这是 `omk` 第二格的求值范围), `g₂` 对一切上下文要求 (`ID` 要造 `pD C`).
>
> 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderInfWGood (𝕊 : HtS) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.LadderNFWPrefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ)
open import OCF.Align.LadderNFWEq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; toZ-≅; Ωˢ-≅; Ωˢ-refl; addˢ-≅; self-trˢ; self-tr⁻ˢ; tr⁻ˢ-≅; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; ≅ᴵ→⊑ᴵ)
open import OCF.Align.LadderNFWFloor using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; inb; Dem; DemB; _∼ᶠ_; ∼ᶠ-refl; flo; cvFlo; toFlo)
open import OCF.Align.LadderNFWAux using (one⁰)
open import OCF.Align.LadderNFWForce using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Align.LadderNFWFT using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderInfWTree 𝕊
open import OCF.Align.LadderInfWRel 𝕊
open import OCF.Align.LadderInfWCx 𝕊
open import OCF.Align.LadderInfWRules 𝕊
open import OCF.Align.LadderInfWRules2 𝕊
open import OCF.Align.LadderInfWRules3 𝕊
open import OCF.Align.LadderInfWStrict 𝕊
open import OCF.Align.LadderInfWStrict2 𝕊
open import OCF.Align.LadderInfWClass 𝕊
open import OCF.Align.LadderInfWClassF 𝕊 using (NZ-of)
open Ord-Ord using (iter)
open RestrQ
```

## §1 类, 下移, 读数

```agda
ClT : Ht → Ordᴵ → Flr → Fv → Set₁
ClT m c φ χ = Cx m c φ χ → Set

𝓥 : ∀ {m c φ χ} → ClT m c φ χ
𝓥 C = Ctxᶜ C

data Gr : Set where
  g₀ g₁ g₂ : Gr

inp : Gr → Gr
inp g₀ = g₀
inp g₁ = g₂
inp g₂ = g₂

eag : Gr → Gr
eag g₀ = g₀
eag g₁ = g₁
eag g₂ = g₁

-- C 经下移与搬运到 E (地板 Fl). 第二个参数: 至少下移过一个后继层
data Sft {m} : ∀ {k φ χ} → Cx m k φ χ → Bool → ∀ {b} → Cx m b Fl (κ Fl) → Set where
  sB : ∀ {k φ χ} {C : Cx m k φ χ} {E : Cx m k Fl (κ Fl)} → E ≈ᶜ C → Sft C false E
  sS : ∀ {k φ χ s b} {C : Cx m (suc k) φ χ} {E : Cx m b Fl (κ Fl)} → Sft (sh zero C) s E → Sft C true E
  sL : ∀ {f t φ χ b} n {C : Cx m (lim f t) φ χ} {E : Cx m b Fl (κ Fl)} → Sft (sh (self n) C) true E → Sft C true E
  sT : ∀ {a a′ φ χ s b} (e : a′ ≅ᴵ a) {C : Cx m a φ χ} {E : Cx m b Fl (κ Fl)} → Sft (ptr e C) s E → Sft C s E
  sT⁻ : ∀ {a a′ φ χ s b} (e : a ≅ᴵ a′) {C : Cx m a φ χ} {E : Cx m b Fl (κ Fl)} → Sft (ptr⁻ e C) s E → Sft C s E

-- 读数: C 的一切下移下, Ω̇_b 的值的层号 ≻ b. 这是 ψ₀(…Ω̇_b…) ≻ b, 对栈形的陈述.
record VisQ {m} (k : Ordᴵ) {φ χ} (C : Cx m k φ χ) : Set where
  constructor visQ
  field
    cxQ : Ctxᶜ C
    cpQ : ∀ {b} {E : Cx m b Fl (κ Fl)} → Sft C true E → (G : Goodᴺ (toZ (runᶜ E (Ω̇ m b)))) → suc b ⊑ᴵ lvG G
open VisQ public

record VisQT {m} (k : Ordᴵ) {φ χ} (C : Cx m k φ χ) : Set where
  constructor visT
  field
    vQ  : VisQ k C
    tpQ : ∀ {b} {E : Cx m b Fl (κ Fl)} → Sft C false E → (G : Goodᴺ (toZ (runᶜ E (Ω̇ m b)))) → suc b ⊑ᴵ lvG G
open VisQT public

KlT : Gr → ∀ {m} k {φ χ} → Cx m k φ χ → Set
KlT g₀ k C = Ctxᶜ C
KlT g₁ k C = VisQT k C
KlT g₂ k C = VisQT k C

KQ : Gr → ∀ {m} k {φ χ} → Cx m k φ χ → Set
KQ g₀ k C = Ctxᶜ C
KQ g₁ k C = VisQ k C
KQ g₂ k C = VisQ k C

KlT→Ctx : ∀ g {m k φ χ} {C : Cx m k φ χ} → KlT g k C → Ctxᶜ C
KlT→Ctx g₀ c = c
KlT→Ctx g₁ v = cxQ (vQ v)
KlT→Ctx g₂ v = cxQ (vQ v)

KlT→KQ : ∀ g {m k φ χ} {C : Cx m k φ χ} → KlT g k C → KQ g k C
KlT→KQ g₀ c = c
KlT→KQ g₁ v = vQ v
KlT→KQ g₂ v = vQ v

KQ→Ctx : ∀ g {m k φ χ} {C : Cx m k φ χ} → KQ g k C → Ctxᶜ C
KQ→Ctx g₀ c = c
KQ→Ctx g₁ v = cxQ v
KQ→Ctx g₂ v = cxQ v

-- 第二格 (omk 的 x) 只在 Nd 上下文求值, 故 g₀, g₁ 的封闭性只对 Nd 上下文要求; g₂ 对一切上下文要求, 因为它要过 ι↓
NdG : Gr → ∀ {m c φ χ} → Cx m c φ χ → Set
NdG g₀ C = Nd C
NdG g₁ C = Nd C
NdG g₂ C = ⊤

ndg : ∀ g {m c φ χ} {C : Cx m c φ χ} → Nd C → NdG g C
ndg g₀ n = n
ndg g₁ n = n
ndg g₂ n = tt

ndE : ∀ g {m c φ χ} {C : Cx m c φ χ} → NdG (eag g) C → Nd C
ndE g₀ n = n
ndE g₁ n = n
ndE g₂ n = n

ndT : ∀ g {m a b φ χ} (e : a ≅ᴵ b) {C : Cx m b φ χ} → NdG g C → NdG g (ptr e C)
ndT g₀ e n = n
ndT g₁ e n = n
ndT g₂ e n = tt

ndT⁻ : ∀ g {m a b φ χ} (e : a ≅ᴵ b) {C : Cx m a φ χ} → NdG g C → NdG g (ptr⁻ e C)
ndT⁻ g₀ e n = n
ndT⁻ g₁ e n = n
ndT⁻ g₂ e n = tt

Dm : ∀ m → Ordᴵ → Flr → Fv → Set
Dm m X φ χ = (∀ {K} (q : InF K φ) → Dem X q) × (∀ i → i <ᴸ m → ∀ {K} (q : InF K (χ i)) → Dem X q)

HonT : ∀ {m c φ χ} → Q m c φ χ → Cx m c φ χ → Set
HonT {m} {φ = φ} {χ = χ} a C = (G : Goodᴺ (toZ (runᶜ C a))) → Dm m (lvG G) φ χ

Hq : Gr → ∀ {m c φ χ} → Q m c φ χ → Cx m c φ χ → Set
Hq g₀ a C = ⊤
Hq g₁ a C = ⊤
Hq g₂ {c = c} a C = (G : Goodᴺ (toZ (runᶜ C a))) → c ⊑ᴵ lvG G

record FlOverᵀ {m c φ χ} (a : Q m c φ χ) (O₁ C″ : Cx m c φ χ) : Set where
  constructor flo-overᵀ
  field
    cxoᵀ : Ctxᶜ C″
    flwᵀ : (t : Q m c φ χ) → Rq m c c t t → (G : Goodᴺ (toZ (runᶜ C″ t))) → Σ (Goodᴺ (toZ (runᶜ O₁ a))) λ H → forceᴺ _ H ⊑ forceᴺ _ G
open FlOverᵀ public

record AboveV (j : Ordᴵ) {m c φ χ} (C′ : Cx m c φ χ) (D : Obs j) : Set where
  constructor aboveV
  field
    cxV   : Ctxᶜ C′
    wrapV : (t : Q m c φ χ) → Rq m c c t t → Σ (Ordˢ j) λ u → (u ≅ˢ u) × (Ωˢ j ⊑ᴱ u) × (runᶜ C′ t ≅ˢ run D u)
open AboveV public

record AboveΩ {m c φ χ n k ξ ζ} (C′ : Cx m c φ χ) (D : Cx n k ξ ζ) : Set where
  constructor aboveΩ
  field
    cxΩ   : Ctxᶜ C′
    wrapΩ : (t : Q m c φ χ) → Rq m c c t t → Σ (Q n k ξ ζ) λ u → Rq n k k u u × FlΩ̇ n k u × (runᶜ C′ t ≅ˢ runᶜ D u)
open AboveΩ public

_⟪_⟫ : ∀ {m c φ χ j} → (Cx m c φ χ → Obs j) → ClT m c φ χ → Cl j
(W ⟪ 𝓔 ⟫) D = Ctx D × (Σ _ λ C → 𝓔 C × (D ≈ᵒ W C))

_⟪_⟫ᵀ : ∀ {m c φ χ n k ξ ζ} → (Cx m c φ χ → Cx n k ξ ζ) → ClT m c φ χ → ClT n k ξ ζ
(W ⟪ 𝓔 ⟫ᵀ) D = Ctxᶜ D × (Σ _ λ C → 𝓔 C × (D ≈ᶜ W C))

Dq : ∀ {m k ℓ φ χ} → k ◃₁ ℓ → ClT m ℓ φ χ → ClT m k φ χ
Dq r 𝓖 D = Ctxᶜ D × (Σ _ λ C → 𝓖 C × (Σ (Dd C) λ d → D ≈ᶜ shD r C d))

data ⊤₁ : Set₁ where
  tt₁ : ⊤₁

Zc : Gr → Set₁ → Set₁
Zc g₀ X = ⊤₁
Zc g₁ X = ⊤₁
Zc g₂ X = X
```

## §2 `Gq`

```agda
module _ (m : Ht) (c : Ordᴵ) (L : Gr → ∀ {k} → k ◃ c → ∀ {ξ ζ} → ClT m k ξ ζ → Q m k ξ ζ → Set₁) (Lv : ∀ {n} → n <ᴸ m → ∀ {k ξ ζ} → ClT n k ξ ζ → Q n k ξ ζ → Set₁) where
  data G₊ (g : Gr) : ∀ {φ χ} → ClT m c φ χ → Q m c φ χ → Set₁ where
    g0 : ∀ {φ χ 𝓖} → G₊ g {φ} {χ} 𝓖 q0
    gs : ∀ {φ χ 𝓖} {a : Q m c φ χ} (𝓚 : ClT m c φ χ) → (∀ {C} → 𝓖 C → 𝓚 C) → G₊ g 𝓚 a →
         (∀ {O₁ C″} → 𝓚 O₁ → FlOverᵀ a O₁ C″ → NdG g C″ → 𝓚 C″) → (∀ {C C′} → Ctxᶜ C → C ≈ᶜ C′ → 𝓚 C′ → 𝓚 C) → (∀ {C} → 𝓚 C → HonT a C) → (∀ {C} → 𝓚 C → Hq g a C) → G₊ g 𝓖 (qs a)
    gl : ∀ {φ χ 𝓖} {F : ℕ → Q m c φ χ} → (∀ n → G₊ g 𝓖 (F n)) → (∀ n → F n ⊑ᵗ F (suc n)) → G₊ g 𝓖 (ql F)
    gi : ∀ {φ χ 𝓖 j} {ac : ∀ {L₁} → Ev L₁ φ → j <ᴵ L₁} {f : Ordˢ j → Q m c φ χ}
         (𝓖₀ : ClT m c φ χ) → (∀ {C} → 𝓖 C → 𝓖₀ C) → (W : Cx m c φ χ → Obs j) →
         (∀ {C} → 𝓖₀ C → ∀ u → u ≅ˢ u → run (W C) u ≅ˢ runᶜ C (f u)) →
         (∀ (𝓔 : ClT m c φ χ) → (∀ {C} → 𝓔 C → 𝓖₀ C) → ∀ (z : Ordˢ j) → z ≅ˢ z → Good true (Inp j (W ⟪ 𝓔 ⟫)) z → G₊ g 𝓔 (f z)) →
         (∀ {C} → 𝓖₀ C → Vis (suc j) (W C)) →
         (∀ {C C′} → 𝓖₀ C → AboveV j C′ (W C) → NdG g C′ → 𝓖₀ C′) →
         (∀ {C C′} → Ctxᶜ C → C ≈ᶜ C′ → 𝓖₀ C′ → 𝓖₀ C) →
         (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f z ⊑ᵗ f z′) →
         (∀ {z z′} → z ≅ˢ z′ → Rq m c c (f z) (f z′)) →
         G₊ g 𝓖 (qi ac f)
    gŝ : ∀ {φ χ 𝓖 c₀} {t : Q m c φ χ} {h : (η : Ordᴵ) → c₀ ⊑ᴵ η → Q m c φ χ} (𝓑 : Ordᴵ → ClT m c φ χ) →
         (∀ {η η′ C} → η ≅ᴵ η′ → 𝓑 η C → 𝓑 η′ C) →
         G₊ g 𝓖 t → (∀ η e → G₊ g (λ C → 𝓖 C × 𝓑 η C) (h η e)) →
         Rq m c c t t → (∀ η e η′ e′ → η ≅ᴵ η′ → Rq m c c (h η e) (h η′ e′)) →
         (∀ η e → t ⊑ᵗ h η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → h η e ⊑ᵗ h η′ e′) →
         (∀ {C} → 𝓖 C → (G : Goodᴺ (toZ (runᶜ C t))) → c₀ ⊑ᴵ lvG G) →
         (∀ {C} η e → 𝓖 C → 𝓑 η C → (G : Goodᴺ (toZ (runᶜ C (h η e)))) → c₀ ⊑ᴵ lvG G) →
         (∀ {C} → 𝓖 C → (G : Goodᴺ (toZ (runᶜ C t))) → 𝓑 (lvG G) C) →
         (∀ {C} η e → 𝓖 C → 𝓑 η C → (G : Goodᴺ (toZ (runᶜ C (h η e)))) → 𝓑 (lvG G) C) →
         G₊ g 𝓖 (qŝ c₀ t h)
    gĉ : ∀ {φ χ 𝓖 c₀ z} {zg : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {o₁ : Q m c φ χ} {o₂ : (η : Ordᴵ) → c₀ ⊑ᴵ η → Q m c φ χ}
         (ys : ℕ → Ordᶜ zero) (hy : ∀ i → HS (ys i)) (dy : ∀ i → c₀ ⊑ᴵ toLevel (ys i) (hy i))
         (G₀ : Goodᴺ z) (l₀ : forceᴺ z G₀ ≅ ys 0)
         (Gg : ∀ i → Goodᴺ (zg (toLevel (ys i) (hy i)) (dy i)))
         (lE : ∀ i → forceᴺ _ (Gg i) ≅ ys (suc i)) →
         z ≅ᶻ z → (∀ η e η′ e′ → η ≅ᴵ η′ → zg η e ≅ᶻ zg η′ e′) → Rq m c c o₁ o₁ → (∀ η e η′ e′ → η ≅ᴵ η′ → Rq m c c (o₂ η e) (o₂ η′ e′)) →
         G₊ g 𝓖 o₁ → (∀ k → G₊ g 𝓖 (o₂ (toLevel (ys k) (hy k)) (dy k))) →
         o₁ ⊑ᵗ o₂ (toLevel (ys 0) (hy 0)) (dy 0) → (∀ k → o₂ (toLevel (ys k) (hy k)) (dy k) ⊑ᵗ o₂ (toLevel (ys (suc k)) (hy (suc k))) (dy (suc k))) →
         G₊ g 𝓖 (qĉ c₀ z zg o₁ o₂)
    gclo : ∀ {φ χ 𝓖} {t : Q m c (φ ⊔ fk zero) χ} {h : (η : Ordᴵ) → Q m c (φ ⊔ fk η) χ}
         (𝓖ᵗ : ClT m c (φ ⊔ fk zero) χ) → (∀ {C} → 𝓖 C → 𝓖ᵗ C) → (∀ {C C′} → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖ᵗ C → 𝓖ᵗ C′) → (𝓖ᵍ : ∀ η → ClT m c (φ ⊔ fk η) χ) →
         (∀ {η η′} {C : Cx m c (φ ⊔ fk η) χ} {C′ : Cx m c (φ ⊔ fk η′) χ} → η ≅ᴵ η′ → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖ᵍ η C → 𝓖ᵍ η′ C′) →
         G₊ g 𝓖ᵗ t → (∀ η → G₊ g (𝓖ᵍ η) (h η)) →
         Rq m c c t t → (∀ η η′ → η ≅ᴵ η′ → Rq m c c (h η) (h η′)) →
         (∀ η → suc zero ⊑ᴵ η → t ⊑ᵗ h η) → (∀ η η′ → suc zero ⊑ᴵ η → η ⊑ᴵ η′ → h η ⊑ᵗ h η′) →
         (∀ {C} → 𝓖ᵗ C → (G : Goodᴺ (toZ (runᶜ C t))) → ∀ {K} (q : InF K φ) → Dem (lvG G) q) →
         (∀ η {C} → 𝓖ᵍ η C → (G : Goodᴺ (toZ (runᶜ C (h η)))) → ∀ {K} (q : InF K φ) → Dem (lvG G) q) →
         (∀ {C} → 𝓖ᵗ C → (G : Goodᴺ (toZ (runᶜ C t))) → ∀ {C′ : Cx m c (φ ⊔ fk (lvG G)) χ} → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖ᵍ (lvG G) C′) →
         (∀ η {C} → 𝓖ᵍ η C → (G : Goodᴺ (toZ (runᶜ C (h η)))) → ∀ {C′ : Cx m c (φ ⊔ fk (lvG G)) χ} → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖ᵍ (lvG G) C′) →
         G₊ g 𝓖 (qclo t h)
    gcl : ∀ {φ χ 𝓖 n} {q : n <ᴸ m} {ψ : Flr} {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (ψ ⊔ fk zero)} {t : Q m c φ χ} {h : (η : Ordᴵ) → Q m c φ (upd χ n (ψ ⊔ fk η))}
         (𝓖ᵗ : ClT m c φ χ) → (∀ {C} → 𝓖 C → 𝓖ᵗ C) → (𝓖ᵍ : ∀ η → ClT m c φ (upd χ n (ψ ⊔ fk η))) →
         (∀ {η η′} {C : Cx m c φ (upd χ n (ψ ⊔ fk η))} {C′ : Cx m c φ (upd χ n (ψ ⊔ fk η′))} → η ≅ᴵ η′ → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖ᵍ η C → 𝓖ᵍ η′ C′) →
         G₊ g 𝓖ᵗ t → (∀ η → G₊ g (𝓖ᵍ η) (h η)) →
         Rq m c c t t → (∀ η η′ → η ≅ᴵ η′ → Rq m c c (h η) (h η′)) →
         (∀ η → suc zero ⊑ᴵ η → t ⊑ᵗ h η) → (∀ η η′ → suc zero ⊑ᴵ η → η ⊑ᴵ η′ → h η ⊑ᵗ h η′) →
         (∀ {C} → 𝓖ᵗ C → (G : Goodᴺ (toZ (runᶜ C t))) → ∀ {K} (r : InF K ψ) → Dem (lvG G) r) →
         (∀ η {C} → 𝓖ᵍ η C → (G : Goodᴺ (toZ (runᶜ C (h η)))) → ∀ {K} (r : InF K ψ) → Dem (lvG G) r) →
         (∀ {C} → 𝓖ᵗ C → (G : Goodᴺ (toZ (runᶜ C t))) → ∀ {C′ : Cx m c φ (upd χ n (ψ ⊔ fk (lvG G)))} → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖ᵍ (lvG G) C′) →
         (∀ η {C} → 𝓖ᵍ η C → (G : Goodᴺ (toZ (runᶜ C (h η)))) → ∀ {C′ : Cx m c φ (upd χ n (ψ ⊔ fk (lvG G)))} → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖ᵍ (lvG G) C′) →
         G₊ g 𝓖 (qcl q ψ s t h)
    gw : ∀ {φ χ ψ ρ 𝓖} {le : ∀ {L₁} → Ev L₁ ψ → Ev L₁ φ} {lc : Sub m ρ χ} {x : Q m c φ χ} (𝓖₁ : ClT m c φ χ) → (∀ {C} → 𝓖 C → 𝓖₁ (wkC le lc C)) → G₊ g 𝓖₁ x → G₊ g 𝓖 (qwk le lc x)
    gΩ↓ : ∀ {φ χ 𝓖 n k} {q : n <ᴸ m} {fe : ∀ {L₁} → Ev L₁ φ → Ev L₁ Fl} {ac : ∀ {L₁} → Ev L₁ (χ n) → k <ᴵ L₁} {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m c (ξ ⊔ φ) (lo n ζ ∪ χ)}
         (𝓖₀ : ∀ ξ ζ → ClT m c (ξ ⊔ φ) (lo n ζ ∪ χ)) →
         (∀ ξ ζ {C} {C′ : Cx m c (ξ ⊔ φ) (lo n ζ ∪ χ)} → 𝓖 C → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖₀ ξ ζ C′) →
         (W : ∀ ξ ζ → Cx m c (ξ ⊔ φ) (lo n ζ ∪ χ) → Cx n k ξ ζ) →
         (∀ ξ ζ {C} → 𝓖₀ ξ ζ C → ∀ (u : Q n k ξ ζ) → Rq n k k u u → runᶜ (W ξ ζ C) u ≅ˢ runᶜ C (h ξ ζ (intoV q u))) →
         (∀ (𝓔 : ∀ ξ ζ → ClT m c (ξ ⊔ φ) (lo n ζ ∪ χ)) → (∀ ξ ζ {C} → 𝓔 ξ ζ C → 𝓖₀ ξ ζ C) → ∀ ξ ζ (z : Q n k ξ ζ) → Rq n k k z z → Lv q (W ξ ζ ⟪ 𝓔 ξ ζ ⟫ᵀ) z → G₊ g (𝓔 ξ ζ) (h ξ ζ (intoV q z))) →
         (∀ ξ ζ {C} → 𝓖₀ ξ ζ C → VisQT k (W ξ ζ C)) →
         (∀ ξ ζ {C} {C′ : Cx m c (ξ ⊔ φ) (lo n ζ ∪ χ)} → 𝓖₀ ξ ζ C → AboveΩ C′ (W ξ ζ C) → NdG g C′ → 𝓖₀ ξ ζ C′) →
         (∀ ξ ξ′ ζ ζ′ {C : Cx m c (ξ ⊔ φ) (lo n ζ ∪ χ)} {C′ : Cx m c (ξ′ ⊔ φ) (lo n ζ′ ∪ χ)} → Ctxᶜ C → C ≈ᶜ C′ → 𝓖₀ ξ′ ζ′ C′ → 𝓖₀ ξ ζ C) →
         (∀ {ξ ξ′ ζ ζ′} {z : Q n k ξ ζ} {z′ : Q n k ξ′ ζ′} → z ⊑ᵗ z′ → h ξ ζ (intoV q z) ⊑ᵗ h ξ′ ζ′ (intoV q z′)) →
         (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n k ξ′ ζ′) → Rq n k k z z′ → Rq m c c (h ξ ζ (intoV q z)) (h ξ′ ζ′ (intoV q z′))) →
         G₊ g 𝓖 (qΩ↓ q fe ac h)
    gΩ : ∀ {φ χ 𝓖 k} {fe : ∀ {L₁} → Ev L₁ φ → Ev L₁ Fl} {r : k <ᴵ c} {h : ∀ ξ ζ → Us m k (<→◃ r) ξ ζ → Q m c (ξ ⊔ φ) (lo m ζ ∪ χ)}
         (𝓖₀ : ∀ ξ ζ → ClT m c (ξ ⊔ φ) (lo m ζ ∪ χ)) →
         (∀ ξ ζ {C} {C′ : Cx m c (ξ ⊔ φ) (lo m ζ ∪ χ)} → 𝓖 C → Ctxᶜ C′ → C′ ≈ᶜ C → 𝓖₀ ξ ζ C′) →
         (W : ∀ ξ ζ → Cx m c (ξ ⊔ φ) (lo m ζ ∪ χ) → Cx m k ξ ζ) →
         (∀ ξ ζ {C} → 𝓖₀ ξ ζ C → ∀ (u : Q m k ξ ζ) → Rq m k k u u → runᶜ (W ξ ζ C) u ≅ˢ runᶜ C (h ξ ζ (intoU (<→◃ r) u))) →
         (∀ (𝓔 : ∀ ξ ζ → ClT m c (ξ ⊔ φ) (lo m ζ ∪ χ)) → (∀ ξ ζ {C} → 𝓔 ξ ζ C → 𝓖₀ ξ ζ C) → ∀ ξ ζ (z : Q m k ξ ζ) → Rq m k k z z → L (inp g) (<→◃ r) (W ξ ζ ⟪ 𝓔 ξ ζ ⟫ᵀ) z → G₊ g (𝓔 ξ ζ) (h ξ ζ (intoU (<→◃ r) z))) →
         (∀ ξ ζ {C} → 𝓖₀ ξ ζ C → KlT g k (W ξ ζ C)) →
         (∀ ξ ζ {C} {C′ : Cx m c (ξ ⊔ φ) (lo m ζ ∪ χ)} → 𝓖₀ ξ ζ C → AboveΩ C′ (W ξ ζ C) → NdG g C′ → 𝓖₀ ξ ζ C′) →
         (∀ ξ ξ′ ζ ζ′ {C : Cx m c (ξ ⊔ φ) (lo m ζ ∪ χ)} {C′ : Cx m c (ξ′ ⊔ φ) (lo m ζ′ ∪ χ)} → Ctxᶜ C → C ≈ᶜ C′ → 𝓖₀ ξ′ ζ′ C′ → 𝓖₀ ξ ζ C) →
         (∀ {ξ ξ′ ζ ζ′} {z : Q m k ξ ζ} {z′ : Q m k ξ′ ζ′} → z ⊑ᵗ z′ → h ξ ζ (intoU (<→◃ r) z) ⊑ᵗ h ξ′ ζ′ (intoU (<→◃ r) z′)) →
         (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ m ζ ζ′ → (z : Q m k ξ ζ) (z′ : Q m k ξ′ ζ′) → Rq m k k z z′ → Rq m c c (h ξ ζ (intoU (<→◃ r) z)) (h ξ′ ζ′ (intoU (<→◃ r) z′))) →
         G₊ g 𝓖 (qΩ fe r h)
    gm : ∀ {φ χ 𝓖 k} {r : k ◃₁ c} {z : Us m k (◃₁→◃ r) φ χ} {x : Q m c φ χ} →
         Zc g (∀ (𝓔 : ClT m c φ χ) → (∀ {C} → 𝓔 C → 𝓖 C) → L g₂ (◃₁→◃ r) (Dq r 𝓔) (outU (◃₁→◃ r) z)) → Rq m k k (outU (◃₁→◃ r) z) (outU (◃₁→◃ r) z) → G₊ (eag g) (λ C → 𝓖 C × Nd C) x → G₊ g 𝓖 (omk r z x)

XG : Ht → Set₂
XG n = ∀ {k ξ ζ} → ClT n k ξ ζ → Q n k ξ ζ → Set₁

GV : Gr → ∀ m (v : ∀ {n} → n <ᴸ m → XG n) c {φ χ} → ClT m c φ χ → Q m c φ χ → Set₁
LGV : ∀ m (v : ∀ {n} → n <ᴸ m → XG n) c → Gr → ∀ {k} → k ◃ c → ∀ {ξ ζ} → ClT m k ξ ζ → Q m k ξ ζ → Set₁
GV g m v c 𝓖 x = G₊ m c (LGV m v c) v g 𝓖 x
LGV m v (suc c)   g zero      𝓖 x = GV g m v c 𝓖 x
LGV m v (suc c)   g (suc r)   𝓖 x = LGV m v c g r 𝓖 x
LGV m v (lim f s) g (self n)  𝓖 x = GV g m v (f n) 𝓖 x
LGV m v (lim f s) g (lim n r) 𝓖 x = LGV m v (f n) g r 𝓖 x

FG : ∀ m → (∀ {n} → n <ᴸ m → XG n) → XG m
FG m v {k} 𝓖 x = GV g₂ m v k 𝓖 x

LV : ∀ m {n} → n <ᴸ m → XG n
LV = Rec XG FG

Gq : Gr → ∀ m c {φ χ} → ClT m c φ χ → Q m c φ χ → Set₁
Gq g m = GV g m (LV m)

LG : ∀ m c → Gr → ∀ {k} → k ◃ c → ∀ {ξ ζ} → ClT m k ξ ζ → Q m k ξ ζ → Set₁
LG m = LGV m (LV m)

outG : ∀ {g m c k} (r : k ◃ c) {ξ ζ} {𝓖 : ClT m k ξ ζ} {z : Q m k ξ ζ} → LG m c g r 𝓖 z → Gq g m k 𝓖 z
outG zero      x = x
outG (suc r)   x = outG r x
outG (self n)  x = x
outG (lim n r) x = outG r x

intoG : ∀ {g m c k} (r : k ◃ c) {ξ ζ} {𝓖 : ClT m k ξ ζ} {z : Q m k ξ ζ} → Gq g m k 𝓖 z → LG m c g r 𝓖 z
intoG zero      x = x
intoG (suc r)   x = intoG r x
intoG (self n)  x = x
intoG (lim n r) x = intoG r x

outGV : ∀ {m n} (q : n <ᴸ m) {k ξ ζ} {𝓖 : ClT n k ξ ζ} {z : Q n k ξ ζ} → LV m q 𝓖 z → Gq g₂ n k 𝓖 z
outGV {m} q {𝓖 = 𝓖} {z = z} x = subst (λ X → X 𝓖 z) (Rec-β XG FG m q) x

intoGV : ∀ {m n} (q : n <ᴸ m) {k ξ ζ} {𝓖 : ClT n k ξ ζ} {z : Q n k ξ ζ} → Gq g₂ n k 𝓖 z → LV m q 𝓖 z
intoGV {m} q {𝓖 = 𝓖} {z = z} x = subst (λ X → X 𝓖 z) (sym (Rec-β XG FG m q)) x

G→R : ∀ {g m c φ χ} {𝓖 : ClT m c φ χ} {x : Q m c φ χ} → Gq g m c 𝓖 x → Rq m c c x x
G→R g0 = rz
G→R {φ = φ} {χ = χ} (gs 𝓚 inc h clk cgk ho hq) = rs (∼ᶠ-refl φ) (Sim∼-refl χ) (G→R h)
G→R (gl h st) = rl (λ n → G→R (h n))
G→R (gi {j = j} 𝓖₀ inc W Wf hb Wv St cg hm rf) = ri (≅ᴵ-refl j) (λ x y d → rf d)
G→R (gŝ {c₀ = c₀} 𝓑 Bc g₀′ gg et eg m₁ mm d₀ dE ch₀ chS) = rŝ (≅ᴵ-refl c₀) et eg
G→R (gĉ {c₀ = c₀} ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) = rĉ (≅ᴵ-refl c₀) ez ezg r₁ r₂
G→R (gclo {φ = φ} 𝓖ᵗ inc cgᵗ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) = rclo (∼ᶠ-refl φ) rt rg
G→R (gcl {q = q} {ψ = ψ} 𝓖ᵗ inc 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) = rcl {q = q} same (∼ᶠ-refl ψ) rt rg
G→R (gw 𝓖₁ inc h) = rwk (G→R h)
G→R {φ = φ} {χ = χ} (gΩ↓ {n = n} {k = k} {q = q} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  rΩ↓ {q = q} same (≅ᴵ-refl k) (∼ᶠ-refl φ) (Sim∼-refl χ) (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → rf ξ ξ′ ζ ζ′ d dc z z′ (outVq q l))
G→R {φ = φ} {χ = χ} (gΩ {k = k} {r = r} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  rΩ (≅ᴵ-refl k) (∼ᶠ-refl φ) (Sim∼-refl χ) (λ ξ ξ′ ζ ζ′ d dc z z′ l → rf ξ ξ′ ζ ζ′ d dc z z′ (outRq (<→◃ r) l))
G→R (gm {k = k} {r = zero} zc rz₁ gx) = rob {r = zero} {r′ = zero} (≅ᴵ-refl k) rz₁ (G→R gx)
G→R (gm {k = k} {r = self n} zc rz₁ gx) = rob {r = self n} {r′ = self n} (≅ᴵ-refl k) rz₁ (G→R gx)

dq-map : ∀ {m k ℓ φ χ} (r : k ◃₁ ℓ) {𝓖 𝓖′ : ClT m ℓ φ χ} → (∀ {C} → 𝓖′ C → 𝓖 C) → ∀ {D} → Dq r 𝓖′ D → Dq r 𝓖 D
dq-map r h (x , C , c , o) = x , C , h c , o

Zc-map : ∀ g {X Y : Set₁} → (X → Y) → Zc g X → Zc g Y
Zc-map g₀ f x = x
Zc-map g₁ f x = x
Zc-map g₂ f x = f x

Gmono : ∀ {g m c φ χ} {𝓖 𝓖′ : ClT m c φ χ} {x : Q m c φ χ} → (∀ {C} → 𝓖′ C → 𝓖 C) → Gq g m c 𝓖 x → Gq g m c 𝓖′ x
Gmono h g0 = g0
Gmono h (gs 𝓚 v k clk cgk ho hq) = gs 𝓚 (λ c → v (h c)) k clk cgk ho hq
Gmono h (gl f st) = gl (λ n → Gmono h (f n)) st
Gmono h (gi 𝓖₀ inc W Wf hb Wv St cg hm rf) = gi 𝓖₀ (λ c → inc (h c)) W Wf hb Wv St cg hm rf
Gmono h (gŝ 𝓑 Bc g₀′ gg et eg m₁ mm d₀ dE ch₀ chS) =
  gŝ 𝓑 Bc (Gmono h g₀′) (λ η e → Gmono (λ { (c , b) → h c , b }) (gg η e)) et eg m₁ mm (λ c G → d₀ (h c) G) (λ η e c b G → dE η e (h c) b G) (λ c G → ch₀ (h c) G) (λ η e c b G → chS η e (h c) b G)
Gmono h (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) = gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ (Gmono h go) (λ k → Gmono h (gO k)) mo mO
Gmono h (gclo 𝓖ᵗ inc cgᵗ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) = gclo 𝓖ᵗ (λ c → inc (h c)) cgᵗ 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS
Gmono h (gcl 𝓖ᵗ inc 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS) = gcl 𝓖ᵗ (λ c → inc (h c)) 𝓖ᵍ Bc gt gg rt rg m₁ mm dt dg ch₀ chS
Gmono h (gw 𝓖₁ inc k) = gw 𝓖₁ (λ c → inc (h c)) k
Gmono h (gΩ↓ 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) = gΩ↓ 𝓖₀ (λ ξ ζ c x o → inc₀ ξ ζ (h c) x o) W Wf hb Wv St cg hm rf
Gmono h (gΩ 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) = gΩ 𝓖₀ (λ ξ ζ c x o → inc₀ ξ ζ (h c) x o) W Wf hb Wv St cg hm rf
Gmono {g = g₀} h (gm zc rz₁ gx) = gm tt₁ rz₁ (Gmono (λ { (c , n) → h c , n }) gx)
Gmono {g = g₁} h (gm zc rz₁ gx) = gm tt₁ rz₁ (Gmono (λ { (c , n) → h c , n }) gx)
Gmono {g = g₂} h (gm {r = r} zc rz₁ gx) = gm {r = r} (λ 𝓔 i → zc 𝓔 (λ c → h (i c))) rz₁ (Gmono (λ { (c , n) → h c , n }) gx)
```

## §3 上下文的小引理

```agda
at≡ : ∀ {u v : Ordˢ zero} → u ≡ v → {P : Ordᴵ → Set} → ((G₁ : Goodᴺ (toZ u)) → P (lvG G₁)) → (G : Goodᴺ (toZ v)) → P (lvG G)
at≡ refl K G = K G

fr≡ : ∀ {u v : Ordˢ zero} → u ≡ v → (G : Goodᴺ (toZ v)) → Σ (Goodᴺ (toZ u)) λ G₁ → (forceᴺ _ G₁ ⊑ forceᴺ _ G) × (forceᴺ _ G ⊑ forceᴺ _ G₁)
fr≡ = pull≅

Ctx-unwk : ∀ {m c φ χ ψ ρ} {le : ∀ {L₁} → Ev L₁ ψ → Ev L₁ φ} {lc : Sub m ρ χ} (C : Cx m c ψ ρ) → Ctxᶜ (wkC le lc C) → Ctxᶜ C
Nd-unwk : ∀ {m c φ χ ψ ρ} {le : ∀ {L₁} → Ev L₁ ψ → Ev L₁ φ} {lc : Sub m ρ χ} (C : Cx m c ψ ρ) → Nd (wkC le lc C) → Nd C
Nd-unwk (top O ev p ok e) n = tt
Nd-unwk (pa W C) n = tt
Nd-unwk (pψ q C) n = tt
Nd-unwk (pΨ qH ok e p C) n = tt
Nd-unwk (pι q C) n = tt
Nd-unwk (pD C) ()
Nd-unwk (ptr e C) n = Nd-unwk C n
Nd-unwk (ptr⁻ e C) n = Nd-unwk C n
Ctx-unwk (top O ev p ok e) c = c
Ctx-unwk (pa W C) (w , c) = w , Ctx-unwk C c
Ctx-unwk (pψ q C) c = Ctx-unwk C c
Ctx-unwk (pΨ qH ok e p C) c = Ctx-unwk C c
Ctx-unwk (pι q C) (n , c) = Nd-unwk C n , Ctx-unwk C c
Ctx-unwk (pD C) c = Ctx-unwk C c
Ctx-unwk (ptr e C) c = Ctx-unwk C c
Ctx-unwk (ptr⁻ e C) c = Ctx-unwk C c

demUp : ∀ {K φ} (q : InF K φ) {X Y} → X ⊑ᴵ Y → Dem X q → Dem Y q
demUp ink u (inj₁ h) = inj₁ (≺ᴵ-up′ h u)
  where
  ≺ᴵ-up′ : ∀ {b A′ B′} → b ≺ᴵ A′ → A′ ⊑ᴵ B′ → b ≺ᴵ B′
  ≺ᴵ-up′ (via e q) h′ = ≺ᴵ-respˡ e (sim h′ q)
demUp ink u (inj₂ z) = inj₂ z
demUp inb u h = ⊑ᴵ-trans h u
demUp (inl q) u h = demUp q u h
demUp (inr q) u h = demUp q u h

≈Ctx : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → Ctx O′ → Ctx O
≈Ctxᶜ : ∀ {m c φ χ ψ ρ} {C : Cx m c φ χ} {C′ : Cx m c ψ ρ} → C ≈ᶜ C′ → Ctxᶜ C′ → Ctxᶜ C
≈Ctx idO c = tt
≈Ctx (tlo o) c = ≈Ctxᶜ o c
≈Ctx (addo {ℓ′ = ℓ′} {a = a} {a′ = a′} o k e) (afl ea one nz , c) = afl (≅ˢ-reflˡ e) one′ (NZ-e k nz) , ≈Ctx o c
  where
  one′ : 𝟏 ⊑ᴱ a
  one′ = ⊑ᴱ-≅ʳ (fl-tr⁻ k (s≅ z≅ z≅) one) (tr⁻ˢ-≅ k (≅ˢ-sym e))
≈Ctx (tro o) c = ≈Ctx o c
≈Ctx (tr⁻o o) c = ≈Ctx o c
≈Ctxᶜ (top o) c = ≈Ctx o c
≈Ctxᶜ (pa r o) (w , c) = w , ≈Ctxᶜ o c
≈Ctxᶜ (pψ o) c = ≈Ctxᶜ o c
≈Ctxᶜ (pΨ o) c = ≈Ctxᶜ o c
≈Ctxᶜ (pι o) (n , c) = Nd-≈ o n , ≈Ctxᶜ o c
≈Ctxᶜ (pD o) c = ≈Ctxᶜ o c
≈Ctxᶜ (ptr o) c = ≈Ctxᶜ o c
≈Ctxᶜ (ptr⁻ o) c = ≈Ctxᶜ o c
```
