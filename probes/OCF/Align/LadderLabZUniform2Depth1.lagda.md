> **机械克隆, 验收用.** 由 `ScafLadderZUniform2Depth1` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆.** 由 `Uniform2Depth1` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 自上而下的统一形 (二), 深度 1

> [Uniform2Base](Uniform2Base.lagda.md) 的续篇 (因篇幅拆出, 节号沿用 §10–§11): 深度 1 的好帧 `GA1`, 层对齐的互模拟, 与地板平凡的尾巴的深度 1 折叠定理. 结论在 Uniform2Base §12. 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZUniform2Depth1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev; Fs; Fst)
open import OCF.Align.LadderLabZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; _+ˢ_; trˢ; tr⁻ˢ;
  H1-pen; H1-fsT)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; lt; eq; gt;
              []<; cofA) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω)
open import OCF.Align.Bachmann using (fs-gt; pen→<; gt→≤; clash)
open import OCF.Align.Closure using (Pen; fsT₊-pen′)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-pred; NF₁-fsn)
open import OCF.Align.Standard using (Ctbl; c[]; c∷)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts; occ<)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.LadderLabZUniformS
open import OCF.Align.LadderLabZStage2Label using (one⁰; Lab-oc)
open import OCF.Align.LadderLabZDecoupleBase using (ΩΩ; ŝ-reflg)
open import OCF.Align.LadderLabZDecouple using (Idx; lvI; Ilt; Ieq; kdI; kdI′; gtν; kdI[]; cofP; Lab0[])
open import OCF.Align.LadderLabZGoodLBase
open import OCF.Align.LadderLabZOmegaExpBase using (σ⊥; πw; onCons; cofΣ; predΣ; fsnΣ; fsTΣ; OccΣ; cofW; repW; ωW; γW; γW-eq;
  gtW; penW; H1W; ne-w; 1<γ; ++-ne; fsT-ne; snoc)
open import OCF.Align.LadderLabZOmegaSqBase using (ψΩ; cmpΩ; cofΩc; fsTΩ)
open import OCF.Align.LadderLabZUniform2Base
```

## §10 深度 1: 好帧与层对齐的互模拟

深度 1 的前缀 $E$ (指数前缀) 带标签 $\zeta$ 指: 静态地板 `FlrLab`, 只看目标非零的 `GW1` (底只要 `LW` 与地板标签), 完整的 `GV1` (底完整好则 $E\,P$ 完整好), 与帧互模拟 `≈₁` (底互模拟、地板非平凡部分 $\cong$ 则输出互模拟). 分出 `GW1` 是因为 `gi` 行对**一切**带标签输入量化, 而输入没有自互模拟时只能要目标非零的标签 (Pre0 与 PreW 的分工).

```agda
infix 4 _≈₁_
_≈₁_ : ∀ {φ ψ} → A 1 φ → A 1 ψ → Set
E ≈₁ E′ = ∀ {fl fl′} {P : Run fl} {P′ : Run fl′} → fl ∼ᶠ fl′ → P ≈ᴿ P′ → E P ≈ᴿ E′ P′

GW1 : ∀ {φ} → A 1 φ → T → Set
GW1 E ζ = ∀ {fl} {P : Run fl} {π} → FlrLab fl π → LW P π → LW (E P) (π ++ ψΩᵗ ζ)

GV1 : ∀ {φ} → A 1 φ → T → Set
GV1 E ζ = ∀ {fl} {P : Run fl} {π} → GA0 P π → GR (E P) (π ++ ψΩᵗ ζ)

record GA1 {φ} (E : A 1 φ) (ζ : T) : Set where
  constructor ga1
  field
    fl1 : FlrLab φ ζ
    gw1 : GW1 E ζ
    gv1 : GV1 E ζ
    gr1 : E ≈₁ E
open GA1 public

selfΩ̂0 : Ω̂A 0 ≈₁ Ω̂A 0
selfΩ̂0 {P = P} {P′ = P′} s H =
  cloR {t = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))} {g = λ η → fold 0 (fk η) (λ e q → e (suc q)) P (Ωˢ η)}
       {t′ = fold 0 (fk zero) (λ e → e) P′ (Ωˢ (suc zero))} {g′ = λ η → fold 0 (fk η) (λ e q → e (suc q)) P′ (Ωˢ η)}
       s (fold-≅0 H (Ωˢ-refl (suc zero))) (λ η η′ eη → fold-≅0 H (Ωˢ-≅ eη))

gwΩ̂0 : GW1 (Ω̂A 0) []
gwΩ̂0 {fl} {P} {π} F hP =
  cloW {t = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))} {g = λ η → fold 0 (fk η) (λ e q → e (suc q)) P (Ωˢ η)}
       (FW-pop F) refl (TlW.tlWV hP (LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _)))
       (λ θ Y hY lY nθ lt → TlW.tlWV hP (LabL-Ω Y hY lY nθ (≅ᴵ-refl _)))

goodΩ̂₀ : GA1 (Ω̂A 0) []
goodΩ̂₀ = ga1 FlrLab-z gwΩ̂0 goodΩ̂0 selfΩ̂0
```

**层对齐.** 深度 $\ge1$ 的折叠里地板影响值 (后继行的帧副本成为弹栈的底), 所以尾巴的互模拟推导在后继步要求两侧地板的非平凡部分 $\cong$. `AlignD φ φ′ d` 沿推导记录两侧的当前地板 (`up zero` 处换成紧地板 `flo`), 只在 `s≅` 处要求 `φ ∼ᶠ φ′`. `lowA`: 两侧都在第 $0$、$1$ 层且地板平凡时对**一切**推导成立.

```agda
AlignD : ∀ {k₁ k₂} (φ φ′ : Flr) {a : Ordˢ k₁} {b : Ordˢ k₂} → a ≅ˢ b → Set
AlignD φ φ′ z≅ = ⊤
AlignD φ φ′ (s≅ e) = (φ ∼ᶠ φ′) × AlignD φ φ′ e
AlignD φ φ′ (l≅ h) = ∀ n → AlignD φ φ′ (h n)
AlignD φ φ′ (lᵢ≅ e h) = ∀ x y r → AlignD φ φ′ (h x y r)
AlignD φ φ′ (upˡ {k = k′} {r = zero} e) = AlignD (flo k′) φ′ e
AlignD φ φ′ (upˡ {r = self n} e) = AlignD φ φ′ e
AlignD φ φ′ (upʳ {k = k′} {r = zero} e) = AlignD φ (flo k′) e
AlignD φ φ′ (upʳ {r = self n} e) = AlignD φ φ′ e
AlignD φ φ′ (ŝ≅ k ec et eg) = AlignD φ φ′ et × (∀ η e η′ e′ eη → AlignD φ φ′ (eg η e η′ e′ eη))
AlignD φ φ′ (ĉ≅ ec dt dg eo eO) = AlignD φ φ′ eo × (∀ η e η′ e′ eη → AlignD φ φ′ (eO η e η′ e′ eη))

TrivLeaf : Flr → Set
TrivLeaf φ = (φ ≡ fz) ⊎ Σ Ordᴵ λ K → (φ ≡ fk K) × (K ≅ᴵ zero)

TL∼ : ∀ {φ φ′} → TrivLeaf φ → TrivLeaf φ′ → φ ∼ᶠ φ′
TL∼ (inj₁ refl) (inj₁ refl) = fz∼
TL∼ (inj₁ refl) (inj₂ (K′ , refl , e′)) = zk∼ e′
TL∼ (inj₂ (K , refl , e)) (inj₁ refl) = kz∼ e
TL∼ (inj₂ (K , refl , e)) (inj₂ (K′ , refl , e′)) = fk∼ (≅ᴵ-trans e (≅ᴵ-sym e′))

Low : Ordᴵ → Set
Low k = (k ≡ zero) ⊎ (k ≡ suc zero)

lowA : ∀ {k₁ k₂ φ φ′} {a : Ordˢ k₁} {b : Ordˢ k₂} → Low k₁ → Low k₂ → TrivLeaf φ → TrivLeaf φ′ → (d : a ≅ˢ b) → AlignD φ φ′ d
lowA L₁ L₂ t t′ z≅ = tt
lowA L₁ L₂ t t′ (s≅ e) = TL∼ t t′ , lowA L₁ L₂ t t′ e
lowA L₁ L₂ t t′ (l≅ h) = λ n → lowA L₁ L₂ t t′ (h n)
lowA L₁ L₂ t t′ (lᵢ≅ e h) = λ x y r → lowA L₁ L₂ t t′ (h x y r)
lowA (inj₁ ()) L₂ t t′ (upˡ {r = zero} e)
lowA (inj₂ refl) L₂ t t′ (upˡ {r = zero} e) = lowA (inj₁ refl) L₂ (inj₁ refl) t′ e
lowA (inj₁ ()) L₂ t t′ (upˡ {r = self n} e)
lowA (inj₂ ()) L₂ t t′ (upˡ {r = self n} e)
lowA L₁ (inj₁ ()) t t′ (upʳ {r = zero} e)
lowA L₁ (inj₂ refl) t t′ (upʳ {r = zero} e) = lowA L₁ (inj₁ refl) t (inj₁ refl) e
lowA L₁ (inj₁ ()) t t′ (upʳ {r = self n} e)
lowA L₁ (inj₂ ()) t t′ (upʳ {r = self n} e)
lowA L₁ L₂ t t′ (ŝ≅ k ec et eg) = lowA L₁ L₂ t t′ et , (λ η e η′ e′ eη → lowA L₁ L₂ t t′ (eg η e η′ e′ eη))
lowA L₁ L₂ t t′ (ĉ≅ ec dt dg eo eO) = lowA L₁ L₂ t t′ eo , (λ η e η′ e′ eη → lowA L₁ L₂ t t′ (eO η e η′ e′ eη))
```

**深度 1 的折叠互模拟.** `fold-≅1`: 指数前缀互模拟、尾巴推导层对齐, 则深度 1 的折叠是互模拟的帧. 后继行由 `repR` (副本逐份, 底的地板 `fl ⊔ ψ` 由 `⊔∼` 对齐).

```agda
repR : ∀ {fl fl′ ψ ψ′} {Q : Run fl} {Q′ : Run fl′} {fr : A 1 ψ} {fr′ : A 1 ψ′} →
       fl ∼ᶠ fl′ → ψ ∼ᶠ ψ′ → Q ≈ᴿ Q′ → fr ≈₁ fr′ → ∀ m → repA 0 Q fr m ≈ᴿ repA 0 Q′ fr′ m
repR s sψ H F zero          = wkR proj₁ proj₁ H
repR s sψ H F (suc zero)    = F s H
repR s sψ H F (suc (suc m)) = wkR _ _ (F (⊔∼ s sψ) (repR s sψ H F (suc m)))

fold-≅1 : ∀ {flE flE′ φ φ′ k₁ k₂} {cv : ∀ {L} → Ev L φ → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k₂ L}
          {E : A 1 flE} {E′ : A 1 flE′} {a : Ordˢ k₁} {b : Ordˢ k₂} →
          flE ∼ᶠ flE′ → E ≈₁ E′ → (d : a ≅ˢ b) → AlignD φ φ′ d → fold 1 φ cv E a ≈₁ fold 1 φ′ cv′ E′ b
fold-≅1 sE HE z≅ al s H = wkR _ _ (HE s H)
fold-≅1 sE HE (s≅ e) (sφ , al) s H = limR (λ m → repR s (⊔∼ sE sφ) H (fold-≅1 sE HE e al) m)
fold-≅1 sE HE (l≅ h) al s H = limR (λ n → fold-≅1 sE HE (h n) (al n) s H)
fold-≅1 sE HE (lᵢ≅ {p = q} e h) al s H =
  limᵢR e (λ x y d → fold-≅1 sE HE (h x y (≅→Rˢ (<→◃ q) d)) (al x y (≅→Rˢ (<→◃ q) d)) s H)
fold-≅1 {k₁ = suc k′} {cv = cv} sE HE (upˡ {r = zero} e) al s H =
  wkR (λ { (u , (w , v)) → u , (w , toFlo k′ (cv v)) }) (λ ev → ev) (fold-≅1 sE HE e al s H)
fold-≅1 sE HE (upˡ {r = self n} e) al s H = fold-≅1 sE HE e al s H
fold-≅1 {k₂ = suc k′} {cv′ = cv′} sE HE (upʳ {r = zero} e) al s H =
  wkR (λ ev → ev) (λ { (u , (w , v)) → u , (w , toFlo k′ (cv′ v)) }) (fold-≅1 sE HE e al s H)
fold-≅1 sE HE (upʳ {r = self n} e) al s H = fold-≅1 sE HE e al s H
fold-≅1 {k₁ = zero} {k₂ = zero} sE HE (ŝ≅ k ec et eg) (al₀ , al) s H =
  ĉR ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (fold-≅1 sE HE et al₀ s H)
     (λ η e η′ e′ eη → fold-≅1 sE HE (eg η e η′ e′ eη) (al η e η′ e′ eη) s H)
fold-≅1 {k₁ = zero} {k₂ = suc _}   sE HE (ŝ≅ k ec et eg) al s H = ⊥-elim (tf k)
fold-≅1 {k₁ = zero} {k₂ = lim _ _} sE HE (ŝ≅ k ec et eg) al s H = ⊥-elim (tf k)
fold-≅1 {k₁ = suc _}   {k₂ = zero} sE HE (ŝ≅ k ec et eg) al s H = ⊥-elim (tf (sym k))
fold-≅1 {k₁ = lim _ _} {k₂ = zero} sE HE (ŝ≅ k ec et eg) al s H = ⊥-elim (tf (sym k))
fold-≅1 {k₁ = suc _} {k₂ = suc _} sE HE (ŝ≅ k ec et eg) (al₀ , al) s H =
  ŝR ec (fold-≅1 sE HE et al₀ s H) (λ η e η′ e′ eη → fold-≅1 sE HE (eg η e η′ e′ eη) (al η e η′ e′ eη) s H)
fold-≅1 {k₁ = suc _} {k₂ = lim _ _} sE HE (ŝ≅ k ec et eg) (al₀ , al) s H =
  ŝR ec (fold-≅1 sE HE et al₀ s H) (λ η e η′ e′ eη → fold-≅1 sE HE (eg η e η′ e′ eη) (al η e η′ e′ eη) s H)
fold-≅1 {k₁ = lim _ _} {k₂ = suc _} sE HE (ŝ≅ k ec et eg) (al₀ , al) s H =
  ŝR ec (fold-≅1 sE HE et al₀ s H) (λ η e η′ e′ eη → fold-≅1 sE HE (eg η e η′ e′ eη) (al η e η′ e′ eη) s H)
fold-≅1 {k₁ = lim _ _} {k₂ = lim _ _} sE HE (ŝ≅ k ec et eg) (al₀ , al) s H =
  ŝR ec (fold-≅1 sE HE et al₀ s H) (λ η e η′ e′ eη → fold-≅1 sE HE (eg η e η′ e′ eη) (al η e η′ e′ eη) s H)
fold-≅1 sE HE (ĉ≅ ec dt dg eo eO) (al₀ , al) s H =
  ĉR ec dt dg (fold-≅1 sE HE eo al₀ s H) (λ η e η′ e′ eη → fold-≅1 sE HE (eO η e η′ e′ eη) (al η e η′ e′ eη) s H)
```

## §11 深度 1 的折叠定理 (地板平凡的尾巴)

**记号.** 深度 1 的折叠作用于底 $P$ (标签 $\pi$) 时标签为 $\pi+\psi_\Omega(\zeta+y)$, 即 §7 的 "前缀 + cons" 形 (`ps = π`, `y = ψᵗ Ωᵗ (ζ ++ y)`, `ys = []`). 各行的记号交换都是 OmegaExpBase 的引理在外层下标 $\Omega$ 上的实例 (`cofW Ωᵗ`、`repW Ωᵗ`、`ωW Ωᵗ`、`penW Ωᵗ` 与 OmegaSqBase 的 `cmpΩ`: 可数的 $\nu$ 有 $\nu+1<\Omega$, $\psi_\Omega$ 穿透).

```agda
wkLW : ∀ {φ ψ} {R : Run φ} (le : ∀ {L} → Ev L ψ → Ev L φ) {u} → LW R u → LW (wk 0 le R) u
wkLW le h ev p = h (le ev) p

wkL0 : ∀ {φ ψ} {R : Run φ} (le : ∀ {L} → Ev L ψ → Ev L φ) {u} → L0 R u → L0 (wk 0 le R) u
wkL0 le h ev p = h (le ev) p

wkGR : ∀ {φ ψ} {R : Run φ} (le : ∀ {L} → Ev L ψ → Ev L φ) {u} → GR R u → GR (wk 0 le R) u
wkGR le (gr a b c) = gr (wkLW le a) (wkL0 le b) (wkR le le c)

TrivF : Flr → Set
TrivF φ = ∀ {K} → InF K φ → K ≅ᴵ zero

TrivF-fz : TrivF fz
TrivF-fz ()

TrivF-z : TrivF (fk zero)
TrivF-z ink = z≅

Triv→FL : ∀ {φ ps} → TrivF φ → FlrLab φ ps
Triv→FL T k = inj₁ (T k)

module _ (ζ : T) {y : PT} {ys : T} where
  c1Ω : cof (y ∷ ys) ≡ c1 → cof (ψᵗ Ωᵗ (ζ ++ (y ∷ ys)) ∷ []) ≡ cω
  c1Ω c = trans (cofW Ωᵗ ζ y ys) (cong (cofA Ωᵗ) c)
  cωΩ : cof (y ∷ ys) ≡ cω → cof (ψᵗ Ωᵗ (ζ ++ (y ∷ ys)) ∷ []) ≡ cω
  cωΩ c = trans (cofW Ωᵗ ζ y ys) (cong (cofA Ωᵗ) c)
  cΩΩ : ∀ {ν} → cof (y ∷ ys) ≡ cΩ ν → Idx ν → cof (ψᵗ Ωᵗ (ζ ++ (y ∷ ys)) ∷ []) ≡ cΩ ν
  cΩΩ {ν} c I = trans (cofW Ωᵗ ζ y ys) (trans (cong (cofA Ωᵗ) c) (cofP {w = Ωᵗ} {ν = ν} (inj₁ (cmpΩ I))))
  penΩ : ∀ {ν} → cof (y ∷ ys) ≡ cΩ ν → Idx ν → ∀ η → fsT (ψᵗ Ωᵗ (ζ ++ (y ∷ ys)) ∷ []) η ≡ ψᵗ Ωᵗ (ζ ++ fsT (y ∷ ys) η) ∷ []
  penΩ {ν} c I η = penW Ωᵗ ζ y ys ν c (inj₁ (cmpΩ I)) η

ψΩ-occ : ∀ {w} ζ b → Occ w ζ → Occ w (ψΩᵗ (ζ ++ b))
ψΩ-occ ζ b o = od (OccPre b o)

FL-rep : ∀ {flE φ ζ b} → FlrLab flE ζ → TrivF φ → ∀ m → FlrLab (flE ⊔ φ) (replicate (suc m) (ψᵗ Ωᵗ (ζ ++ b)))
FL-rep {ζ = ζ} {b} FE T m (inl k) = FlrLab-mono (λ o → od (OccPre b o)) FE k
FL-rep FE T m (inr k) = inj₁ (T k)
```

**目标非零 (`W1`).** 对尾巴推导递归 (第 0、1 层; 地板平凡). 后继行的第 $m$ 份副本的底是前 $m-1$ 份, 它们的地板标签由 `FL-rep` (前缀帧的地板见证在 $\zeta$ 里, 尾巴地板平凡).

```agda
module Depth1 {flE} {E : A 1 flE} {ζ : T} (GE : GA1 E ζ) where

  copyW : ∀ {ψ fl} {P : Run fl} {π x} {fr : A 1 ψ} → FlrLab fl π → (∀ m → FlrLab ψ (replicate (suc m) x)) → LW P π →
          (∀ {fl′} {Q : Run fl′} {ρ} → FlrLab fl′ ρ → LW Q ρ → LW (fr Q) (ρ ++ x ∷ [])) →
          ∀ m → LW (repA 0 P fr m) (π ++ replicate m x)
  copyW {ψ = ψ} F Fψ hP hF zero = zW {φ = ψ} hP
  copyW F Fψ hP hF (suc zero) = hF F hP
  copyW {π = π} {x = x} F Fψ hP hF (suc (suc m)) =
    wkLW _ (subst (λ u → LW _ u) (snoc π (suc m) x) (hF (FlrLab-⊔ F (Fψ m)) (copyW F Fψ hP hF (suc m))))

  W1A : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → TrivF φ → Lab0ᴸ t y → GW1 (fold 1 φ cv E t) (ζ ++ y)
  W1₁ : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ (suc zero) L} {t : Ordˢ (suc zero)} {y} → TrivF φ →
        LabL₊ (suc zero) Ll t y → GW1 (fold 1 φ cv E t) (ζ ++ y)

  W1A {y = []} T (lz c) F hP = wkLW _ (subst (λ u → LW _ (_ ++ ψΩᵗ u)) (sym (++-identityʳ ζ)) (gw1 GE F hP))
  W1A {y = y ∷ ys} T (lz c) F hP = ⊥-elim (cof-ne y ys c)
  W1A {y = []} T (ls () l) F hP
  W1A {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y ∷ ys} T (ls c l) {P = P} {π = π} F hP =
    limW {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → repA 0 P (fold 1 φ cv E a) m} (c1Ω ζ c)
         (λ m → subst (λ u → LW _ (π ++ u)) (sym (repW Ωᵗ ζ y ys c m))
                      (copyW F (FL-rep (fl1 GE) T) hP (W1A T l) m))
  W1A {y = []} T (ll () h) F hP
  W1A {φ = φ} {cv = cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} T (ll c h) {P = P} {π = π} F hP =
    limW {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → fold 1 φ cv E (G m) P} (cωΩ ζ c)
         (λ n → subst (λ u → LW _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys c n)) (W1A T (h n) F hP))
  W1A {y = []} T (lŝ₀ () K h₀ hk) F hP
  W1A {φ = φ} {cv = cv} {y = y ∷ ys} T (lŝ₀ {t₀ = t₀} {g = g} c K h₀ hk) {P = P} {π = π} F hP =
    ĉW {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E t₀ P} {O = λ η e → fold 1 φ cv E (g η e) P}
       (cωΩ ζ c) K (subst (λ u → LW _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys c 0)) (W1A T h₀ F hP))
       (λ k → subst (λ u → LW _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys c (suc k))) (W1A T (hk k) F hP))
  W1A {y = []} T (lĉ () K h₀ hk) F hP
  W1A {φ = φ} {cv = cv} {y = y ∷ ys} T (lĉ {o₀ = o₀} {o = o} c K h₀ hk) {P = P} {π = π} F hP =
    ĉW {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E o₀ P} {O = λ η e → fold 1 φ cv E (o η e) P}
       (cωΩ ζ c) K (subst (λ u → LW _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys c 0)) (W1A T h₀ F hP))
       (λ k → subst (λ u → LW _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys c (suc k))) (W1A T (hk k) F hP))

  W1₁ {y = []} T (gz c) F hP = wkLW _ (subst (λ u → LW _ (_ ++ ψΩᵗ u)) (sym (++-identityʳ ζ)) (gw1 GE F hP))
  W1₁ {y = y ∷ ys} T (gz c) F hP = ⊥-elim (cof-ne y ys c)
  W1₁ {y = []} T (gs () l) F hP
  W1₁ {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y ∷ ys} T (gs c l) {P = P} {π = π} F hP =
    limW {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → repA 0 P (fold 1 φ cv E a) m} (c1Ω ζ c)
         (λ m → subst (λ u → LW _ (π ++ u)) (sym (repW Ωᵗ ζ y ys c m))
                      (copyW F (FL-rep (fl1 GE) T) hP (W1₁ T l) m))
  W1₁ {y = []} T (gl () h) F hP
  W1₁ {φ = φ} {cv = cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} T (gl c h) {P = P} {π = π} F hP =
    limW {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → fold 1 φ cv E (G m) P} (cωΩ ζ c)
         (λ n → subst (λ u → LW _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys c n)) (W1₁ T (h n) F hP))
  W1₁ {cv = cv} T (gu {r = zero} h) F hP ev p =
    W1A {φ = fz} {cv = cvFlo zero} TrivF-fz (atomL h) F hP (proj₁ ev , (proj₁ (proj₂ ev) , tt)) p
  W1₁ {y = []} T (gi () I ej h) F hP
  W1₁ {φ = φ} {cv = cv} {y = y ∷ ys} T (gi {q = q} {f = f} c I ej h) {P = P} {π = π} F hP =
    limᵢW {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {ac = λ ev → cv (proj₂ (proj₂ ev)) q}
          {H = λ x → fold 1 φ cv E (f (intoˢ (<→◃ q) x)) P} (cΩΩ ζ c I) I ej
          (λ η x l → subst (λ u → LW _ (π ++ u)) (sym (penΩ ζ c I η)) (W1₁ T (h η x (→Ll (<→◃ q) l)) F hP))
  W1₁ {y = []} T (gĉ () K h₀ hk) F hP
  W1₁ {φ = φ} {cv = cv} {y = y ∷ ys} T (gĉ {o₀ = o₀} {o = o} c K h₀ hk) {P = P} {π = π} F hP =
    ĉW {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E o₀ P} {O = λ η e → fold 1 φ cv E (o η e) P}
       (cωΩ ζ c) K (subst (λ u → LW _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys c 0)) (W1₁ T h₀ F hP))
       (λ k → subst (λ u → LW _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys c (suc k))) (W1₁ T (hk k) F hP))
  W1₁ {y = []} T (gŝ kk () Iw bw ob h₀ hg) F hP
  W1₁ {φ = φ} {cv = cv} {y = y ∷ ys} T (gŝ {w = w} {t₀ = t₀} {g = g} kk c Iw bw ob h₀ hg) {P = P} {π = π} F hP =
    ŝW {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {T₀ = fold 1 φ cv E t₀ P} {G = λ η e → fold 1 φ cv E (g η e) P}
       (cΩΩ ζ c I0) Iw bw (λ θ → subst (λ u → Occ w (π ++ u)) (sym (penΩ ζ c I0 θ)) (OccΣ π (od (OccΣ ζ (ob θ)))))
       (subst (λ u → LW _ (π ++ u)) (sym (penΩ ζ c I0 (natT 1))) (W1₁ T h₀ F hP))
       (λ θ Y hY lY nθ lt e → subst (λ u → LW _ (π ++ u)) (sym (penΩ ζ c I0 θ)) (W1₁ T (hg θ Y hY lY nθ lt e) F hP))
```

**目标 0 与完整的好帧 (`O1`, `Full`).** 互递归: 后继行的副本要帧 (前驱尾巴的折叠) 的完整好性 `Full` (结构上更小), `Full` 由同一推导上的 `W1`、`O1` 与 `fold-≅1` (层对齐由 `lowA`) 组装. 副本的底的地板标签 `FL-rep`.

```agda
  TL→TF : ∀ {φ} → TrivLeaf φ → TrivF φ
  TL→TF (inj₁ refl) ()
  TL→TF (inj₂ (K , refl , e)) ink = e

  copyGA : ∀ {ψ fl} {P : Run fl} {π b} {fr : A 1 ψ} → GA0 P π → (∀ m → FlrLab ψ (replicate (suc m) (ψᵗ Ωᵗ b))) →
           GV1 fr b → ∀ m → GA0 (repA 0 P fr (suc m)) (π ++ replicate (suc m) (ψᵗ Ωᵗ b))
  copyGA (F , GP) Fψ Gfr zero = FlrLab-⊔ F (Fψ 0) , Gfr (F , GP)
  copyGA {π = π} {b = b} (F , GP) Fψ Gfr (suc m) =
    FlrLab-⊔ F (Fψ (suc m)) ,
    wkGR _ (subst (GR _) (snoc π (suc m) (ψᵗ Ωᵗ b)) (Gfr (copyGA (F , GP) Fψ Gfr m)))

  copyGR : ∀ {ψ fl} {P : Run fl} {π b} {fr : A 1 ψ} → GA0 P π → (∀ m → FlrLab ψ (replicate (suc m) (ψᵗ Ωᵗ b))) →
           GV1 fr b → ∀ m → GR (repA 0 P fr m) (π ++ replicate m (ψᵗ Ωᵗ b))
  copyGR {ψ = ψ} {π = π} (F , GP) Fψ Gfr zero =
    wkGR (proj₁ {B = λ _ → Ev _ ψ}) (subst (GR _) (sym (++-identityʳ π)) GP)
  copyGR GP Fψ Gfr (suc m) = proj₂ (copyGA GP Fψ Gfr m)

  L0≡π : ∀ {φ} (R : Run φ) π {u v} → u ≡ v → L0 R (π ++ u) → L0 R (π ++ v)
  L0≡π R π refl h = h

  L0≡ζ : ∀ {φ} (R : Run φ) {π u v} → u ≡ v → L0 R (π ++ ψΩᵗ u) → L0 R (π ++ ψΩᵗ v)
  L0≡ζ R refl h = h

  FullA : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → TrivLeaf φ → Lab0ᴸ t y → t ≅ˢ t →
          GA1 (fold 1 φ cv E t) (ζ ++ y)
  O1A : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → TrivLeaf φ → Lab0ᴸ t y → t ≅ˢ t →
        ∀ {fl} {P : Run fl} {π} → GA0 P π → L0 (fold 1 φ cv E t P) (π ++ ψΩᵗ (ζ ++ y))
  Full₁ : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ (suc zero) L} {t : Ordˢ (suc zero)} {y} → TrivLeaf φ →
          LabL₊ (suc zero) Ll t y → t ≅ˢ t → GA1 (fold 1 φ cv E t) (ζ ++ y)
  O1₁ : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ (suc zero) L} {t : Ordˢ (suc zero)} {y} → TrivLeaf φ →
        LabL₊ (suc zero) Ll t y → t ≅ˢ t → ∀ {fl} {P : Run fl} {π} → GA0 P π → L0 (fold 1 φ cv E t P) (π ++ ψΩᵗ (ζ ++ y))

  FullA {φ} {cv} TL l ex =
    ga1 (FlrLab-⊔ (fl1 GE) (Triv→FL (TL→TF TL))) (W1A (TL→TF TL) l)
        (λ {fl} GP → gr (W1A (TL→TF TL) l (proj₁ GP) (gW (proj₂ GP))) (O1A {cv = cv} TL l ex GP)
                        (fold-≅1 (∼ᶠ-refl flE) (gr1 GE) ex (lowA (inj₁ refl) (inj₁ refl) TL TL ex) (∼ᶠ-refl fl) (gR (proj₂ GP))))
        (fold-≅1 (∼ᶠ-refl flE) (gr1 GE) ex (lowA (inj₁ refl) (inj₁ refl) TL TL ex))

  Full₁ {φ} {cv} TL l ex =
    ga1 (FlrLab-⊔ (fl1 GE) (Triv→FL (TL→TF TL))) (W1₁ (TL→TF TL) l)
        (λ {fl} GP → gr (W1₁ (TL→TF TL) l (proj₁ GP) (gW (proj₂ GP))) (O1₁ {cv = cv} TL l ex GP)
                        (fold-≅1 (∼ᶠ-refl flE) (gr1 GE) ex (lowA (inj₂ refl) (inj₂ refl) TL TL ex) (∼ᶠ-refl fl) (gR (proj₂ GP))))
        (fold-≅1 (∼ᶠ-refl flE) (gr1 GE) ex (lowA (inj₂ refl) (inj₂ refl) TL TL ex))

  O1A {y = []} TL (lz c) ex {P = P} GP = wkL0 {R = E P} (λ ev → proj₁ ev , proj₁ (proj₂ ev)) (L0≡ζ (E P) (sym (++-identityʳ ζ)) (g0 (gv1 GE GP)))
  O1A {y = y ∷ ys} TL (lz c) ex GP = ⊥-elim (cof-ne y ys c)
  O1A {y = []} TL (ls () l) ex GP
  O1A {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y ∷ ys} TL (ls c l) (s≅ e) {P = P} {π = π} GP =
    lim0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → repA 0 P (fold 1 φ cv E a) m} (c1Ω ζ c)
         (λ m → L0≡π (repA 0 P (fold 1 φ cv E a) m) π (sym (repW Ωᵗ ζ y ys c m))
                      (g0 (copyGR GP (FL-rep (fl1 GE) (TL→TF TL)) (gv1 (FullA {cv = cv} TL l e)) m)))
  O1A {y = []} TL (ll () h) ex GP
  O1A {φ = φ} {cv = cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} TL (ll c h) ex {P = P} {π = π} GP =
    lim0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → fold 1 φ cv E (G m) P} (cωΩ ζ c)
         (λ n → L0≡π (fold 1 φ cv E (G n) P) π (sym (ωW Ωᵗ ζ y ys c n)) (O1A {cv = cv} TL (h n) (l-invˢ ex n) GP))
  O1A {y = []} TL (lŝ₀ () K h₀ hk) ex GP
  O1A {φ = φ} {cv = cv} {y = y ∷ ys} TL (lŝ₀ {t₀ = t₀} {g = g} c K h₀ hk) ex {P = P} {π = π} GP =
    ĉ0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E t₀ P} {O = λ η e → fold 1 φ cv E (g η e) P}
       (cωΩ ζ c) K (L0≡π (fold 1 φ cv E t₀ P) π (sym (ωW Ωᵗ ζ y ys c 0)) (O1A {cv = cv} TL h₀ (ŝ-refl₀ ex) GP))
       (λ k → L0≡π (fold 1 φ cv E (g (lvK K k) (dxK K k)) P) π (sym (ωW Ωᵗ ζ y ys c (suc k))) (O1A {cv = cv} TL (hk k) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) GP))
  O1A {y = []} TL (lĉ () K h₀ hk) ex GP
  O1A {φ = φ} {cv = cv} {y = y ∷ ys} TL (lĉ {o₀ = o₀} {o = o} c K h₀ hk) ex {P = P} {π = π} GP =
    ĉ0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E o₀ P} {O = λ η e → fold 1 φ cv E (o η e) P}
       (cωΩ ζ c) K (L0≡π (fold 1 φ cv E o₀ P) π (sym (ωW Ωᵗ ζ y ys c 0)) (O1A {cv = cv} TL h₀ (ĉ-refl₀ ex) GP))
       (λ k → L0≡π (fold 1 φ cv E (o (lvK K k) (dxK K k)) P) π (sym (ωW Ωᵗ ζ y ys c (suc k))) (O1A {cv = cv} TL (hk k) (ĉ-reflg ex _ _) GP))

  O1₁ {y = []} TL (gz c) ex {P = P} GP = wkL0 {R = E P} (λ ev → proj₁ ev , proj₁ (proj₂ ev)) (L0≡ζ (E P) (sym (++-identityʳ ζ)) (g0 (gv1 GE GP)))
  O1₁ {y = y ∷ ys} TL (gz c) ex GP = ⊥-elim (cof-ne y ys c)
  O1₁ {y = []} TL (gs () l) ex GP
  O1₁ {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y ∷ ys} TL (gs c l) (s≅ e) {P = P} {π = π} GP =
    lim0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → repA 0 P (fold 1 φ cv E a) m} (c1Ω ζ c)
         (λ m → L0≡π (repA 0 P (fold 1 φ cv E a) m) π (sym (repW Ωᵗ ζ y ys c m))
                      (g0 (copyGR GP (FL-rep (fl1 GE) (TL→TF TL)) (gv1 (Full₁ {cv = cv} TL l e)) m)))
  O1₁ {y = []} TL (gl () h) ex GP
  O1₁ {φ = φ} {cv = cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} TL (gl c h) ex {P = P} {π = π} GP =
    lim0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → fold 1 φ cv E (G m) P} (cωΩ ζ c)
         (λ n → L0≡π (fold 1 φ cv E (G n) P) π (sym (ωW Ωᵗ ζ y ys c n)) (O1₁ {cv = cv} TL (h n) (l-invˢ ex n) GP))
  O1₁ TL (gu {r = zero} h) ex GP ev p =
    O1A {φ = fz} {cv = cvFlo zero} (inj₁ refl) (atomL h) (u-reflˢ zero ex) GP (proj₁ ev , (proj₁ (proj₂ ev) , tt)) p
  O1₁ {y = []} TL (gi () I ej h) ex GP
  O1₁ {φ = φ} {cv = cv} {y = y ∷ ys} TL (gi {q = q} {f = f} c I ej h) ex {fl = fl} {P = P} {π = π} GP =
    limᵢ0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {ac = λ ev → cv (proj₂ (proj₂ ev)) q}
          {H = λ x → fold 1 φ cv E (f (intoˢ (<→◃ q) x)) P} (cΩΩ ζ c I) I ej
          (λ η x l → subst (λ u → LW _ (π ++ u)) (sym (penΩ ζ c I η))
                           (W1₁ (TL→TF TL) (h η x (→Ll (<→◃ q) l)) (proj₁ GP) (gW (proj₂ GP))))
          (λ η x l xx → L0≡π (fold 1 φ cv E (f (intoˢ (<→◃ q) x)) P) π (sym (penΩ ζ c I η)) (O1₁ {cv = cv} TL (h η x (→Ll (<→◃ q) l)) (i-respˢ ex xx) GP) ,
                        fold-≅1 (∼ᶠ-refl flE) (gr1 GE) (i-respˢ ex xx) (lowA (inj₂ refl) (inj₂ refl) TL TL (i-respˢ ex xx))
                                (∼ᶠ-refl fl) (gR (proj₂ GP)))
  O1₁ {y = []} TL (gĉ () K h₀ hk) ex GP
  O1₁ {φ = φ} {cv = cv} {y = y ∷ ys} TL (gĉ {o₀ = o₀} {o = o} c K h₀ hk) ex {P = P} {π = π} GP =
    ĉ0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E o₀ P} {O = λ η e → fold 1 φ cv E (o η e) P}
       (cωΩ ζ c) K (L0≡π (fold 1 φ cv E o₀ P) π (sym (ωW Ωᵗ ζ y ys c 0)) (O1₁ {cv = cv} TL h₀ (ĉ-refl₀ ex) GP))
       (λ k → L0≡π (fold 1 φ cv E (o (lvK K k) (dxK K k)) P) π (sym (ωW Ωᵗ ζ y ys c (suc k))) (O1₁ {cv = cv} TL (hk k) (ĉ-reflg ex _ _) GP))
  O1₁ {y = []} TL (gŝ kk () Iw bw ob h₀ hg) ex GP
  O1₁ {φ = φ} {cv = cv} {y = y ∷ ys} TL (gŝ {w = w} {t₀ = t₀} {g = g} kk c Iw bw ob h₀ hg) ex {P = P} {π = π} GP =
    ŝ0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {T₀ = fold 1 φ cv E t₀ P} {G = λ η e → fold 1 φ cv E (g η e) P}
       (cΩΩ ζ c I0) Iw bw (λ θ → subst (λ u → Occ w (π ++ u)) (sym (penΩ ζ c I0 θ)) (OccΣ π (od (OccΣ ζ (ob θ)))))
       (L0≡π (fold 1 φ cv E t₀ P) π (sym (penΩ ζ c I0 (natT 1))) (O1₁ {cv = cv} TL h₀ (ŝ-refl₀ ex) GP))
       (λ θ Y hY lY nθ lt e → L0≡π (fold 1 φ cv E (g (toLevel Y hY) e) P) π (sym (penΩ ζ c I0 θ))
                                    (O1₁ {cv = cv} TL (hg θ Y hY lY nθ lt e) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) GP))
```

**读法.** `Full₁`/`FullA` 是自下而上 `GoodE`、`WE₀`/`ZE₀`、`WE₁`/`ZE₁`、`repGood₀`/`repGood₁` 的合并: 一个对尾巴推导的互递归, 各行用的是深度 0 的行引理, 只多一层 `ψΩ` 的记号交换. 后继行的帧是对前驱推导的递归调用 (`Full … l e`, 结构上更小), 互模拟由 `fold-≅1` 与 `lowA` (对**任意**推导, 因为两侧都在第 0、1 层). 停机一次通过.

