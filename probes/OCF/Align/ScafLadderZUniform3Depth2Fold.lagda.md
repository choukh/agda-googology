> **机械克隆.** 由 `Uniform3Depth2Fold` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 统一形 (三): 一切深度 (三) 折叠定理与 $\Omega_\Omega$ 闭包

> 接 [Uniform3Depth2W](Uniform3Depth2W.lagda.md). 把 Uniform3Full §2, §6, §7 与 Uniform3Rel 的 `fold-≅1ᴬ` 搬到一般深度 $d+1$. 结论先说:
>
> 1. **`HΩ̂ᵍ : ∀ d → Gc (suc d) (Ω̂A d) []` (§4): 一切深度的 $\Omega_\Omega$ 闭包, 无前提.** `Gc 3 (Ω̂A 2) []` 是 $d=2$ 的实例. 证明对 $d$ 没有归纳.
> 2. **`OMain.FullH` (§2): 一般深度的折叠定理.** 诚实的尾巴 (`Hn`), 地板被首项见证 (`FH`), 任意层号.
> 3. **`foldR` (§1): 折叠尊重 $\cong^\mathsf A$, 一切深度.** 这就是 Uniform3Plus1 预言的 $\approx_2^\mathsf A$ 及其高阶形.
>
> 没有改树. 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 终止仍是 `(层号, Hn 推导)` 的字典序.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZUniform3Depth2Fold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
open import OCF.Align.ScafLadderZPrefix using (Ord₊ˢ; Ordˢ; Ωˢ; intoˢ; toZ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fsT-c1)
open import OCF.Align.ScafLadderZStandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.ScafLadderZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.ScafLadderZStage2Label using (one⁰)
open import OCF.Align.ScafLadderZDecoupleBase using (ΩΩ)
open import OCF.Align.ScafLadderZDecouple using (Idx; lvI; Ieq; Lab0[])
open import OCF.Align.ScafLadderZGoodLBase
open import OCF.Align.ScafLadderZOmegaExpBase using (OccΣ; repW; ωW)
open import OCF.Align.ScafLadderZUniformS
open import OCF.Align.ScafLadderZUniform3Base
open import OCF.Align.ScafLadderZUniform3Depth1 using (c1Ω; cωΩ; cΩΩ; penΩ)
open import OCF.Align.ScafLadderZUniform3Rel
open import OCF.Align.ScafLadderZUniform3SqABase
open import OCF.Align.ScafLadderZUniform3SqA using (FP0; FP0→FP; FP0-fz; FP0-z; Up0)
open import OCF.Align.ScafLadderZUniform3Hon
open import OCF.Align.ScafLadderZUniform3Full using (FH→FHc; FH-pred; FH→Ω; pred-Pr; flo≼; Zc; GA1ʰ; fl1ʰ; gw1ʰ; g01ʰ; gr1ʰ; goodΩ̂₀ʰ)
open import OCF.Align.ScafLadderZUniform3Depth2Class
open import OCF.Align.ScafLadderZUniform3Depth2W
```

## §1 折叠尊重 $\cong^\mathsf A$, 一切深度

```agda
foldR : ∀ d {flE flE′ φ φ′ k₁ k₂} {cv : ∀ {L} → Ev L φ → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k₂ L}
        {E : A (suc d) flE} {E′ : A (suc d) flE′} {a : Ordˢ k₁} {b : Ordˢ k₂} →
        flE ∼ᶠ flE′ → Rd (suc d) E E′ → k₁ ≅ᴵ k₂ → φ ∼ᶠ φ′ → a ≅ᴬ b → Rd (suc d) (fold (suc d) φ cv E a) (fold (suc d) φ′ cv′ E′ b)
foldR d sE HE ek sφ zᴬ = wkRd (suc d) _ _ HE
foldR d sE HE ek sφ (sᴬ e) s H = limRd d (λ m → repRd d s (⊔∼ sE sφ) H (foldR d sE HE ek sφ e) m)
foldR d sE HE ek sφ (lᴬ h) = limRd (suc d) (λ n → foldR d sE HE ek sφ (h n))
foldR d sE HE ek sφ (lᵢᴬ {p = q} e h) = limᵢRd (suc d) e (λ x y dd → foldR d sE HE ek sφ (h x y (≅→Rᴬ (<→◃ q) dd)))
foldR d {k₁ = suc k′} {k₂ = suc k″} sE HE (s≅ ek) sφ (uᴬ uz dd) = wkRd (suc d) _ _ (foldR d sE HE ek (flo-∼ ek) dd)
foldR d {k₁ = lim f r} {k₂ = lim g t} sE HE (l≅ hh) sφ (uᴬ (us n) dd) = wkRd (suc d) _ _ (foldR d sE HE (hh n) (flo-∼ (hh n)) dd)
foldR d {k₁ = zero} {k₂ = zero} sE HE ek sφ (ŝᴬ k ec et eg) =
  ĉRd (suc d) ec (toZ-≅ (≅ᴬ→≅ˢ₀ et)) (λ η e η′ e′ eη → toZ-≅ (≅ᴬ→≅ˢ₀ (eg η e η′ e′ eη))) (foldR d sE HE ek sφ et)
      (λ η e η′ e′ eη → foldR d sE HE ek sφ (eg η e η′ e′ eη))
foldR d {k₁ = zero} {k₂ = suc _}   sE HE ek sφ (ŝᴬ k ec et eg) = ⊥-elim (tf k)
foldR d {k₁ = zero} {k₂ = lim _ _} sE HE ek sφ (ŝᴬ k ec et eg) = ⊥-elim (tf k)
foldR d {k₁ = suc _}   {k₂ = zero} sE HE ek sφ (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
foldR d {k₁ = lim _ _} {k₂ = zero} sE HE ek sφ (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
foldR d {k₁ = suc _} {k₂ = suc _} sE HE ek sφ (ŝᴬ k ec et eg) =
  ŝRd (suc d) ec (foldR d sE HE ek sφ et) (λ η e η′ e′ eη → foldR d sE HE ek sφ (eg η e η′ e′ eη))
foldR d {k₁ = suc _} {k₂ = lim _ _} sE HE ek sφ (ŝᴬ k ec et eg) =
  ŝRd (suc d) ec (foldR d sE HE ek sφ et) (λ η e η′ e′ eη → foldR d sE HE ek sφ (eg η e η′ e′ eη))
foldR d {k₁ = lim _ _} {k₂ = suc _} sE HE ek sφ (ŝᴬ k ec et eg) =
  ŝRd (suc d) ec (foldR d sE HE ek sφ et) (λ η e η′ e′ eη → foldR d sE HE ek sφ (eg η e η′ e′ eη))
foldR d {k₁ = lim _ _} {k₂ = lim _ _} sE HE ek sφ (ŝᴬ k ec et eg) =
  ŝRd (suc d) ec (foldR d sE HE ek sφ et) (λ η e η′ e′ eη → foldR d sE HE ek sφ (eg η e η′ e′ eη))
foldR d sE HE ek sφ (ĉᴬ ec dt dg eo eO) =
  ĉRd (suc d) ec dt dg (foldR d sE HE ek sφ eo) (λ η e η′ e′ eη → foldR d sE HE ek sφ (eO η e η′ e′ eη))
```

## §2 目标 0 与折叠定理

`OMain d GE`: 好帧 $E$ (深度 $d+1$) 上的折叠定理. 终止仍是 `(层号, Hn 推导)` 的字典序. 与 Uniform3Full 的差别: 行引理在深度 $d+1$ 上调用, 所以证明里不出现 $P$, $\pi$, 也没有 `L0≡π` 一类的转换, 只有后继行落到深度 $d$.

```agda
Zc₀ : Ordᴵ → Flr → Set
Zc₀ zero φ = FP0 φ
Zc₀ (suc _) φ = ⊤
Zc₀ (lim _ _) φ = ⊤

Zc₀-of : ∀ {k φ w} (I : Idx w) → k ≅ᴵ lvI I → FH φ (Ωt w) → Zc₀ k φ
Zc₀-of {k = zero} I e f k₁ with f k₁
... | inj₁ e0 = inj₁ e0
... | inj₂ (inj₁ e1) = inj₂ e1
... | inj₂ (inj₂ (I′ , kw)) with ≼-trans kw (inj₂ (≅ᴵ-trans (Ieq I′ I) (≅ᴵ-sym e)))
...   | inj₁ (via _ ())
...   | inj₂ e0 = inj₁ e0
Zc₀-of {k = suc _} I e f = tt
Zc₀-of {k = lim _ _} I e f = tt

Zc₀-flo : ∀ k → Zc₀ k (flo k)
Zc₀-flo zero = FP0-fz
Zc₀-flo (suc k) = tt
Zc₀-flo (lim f s) = tt

upS : ∀ k′ {φ} (cv : ∀ {L} → Ev L φ → Simᴵ (suc k′) L) {fl L} → Ev L (fl ⊔ φ) → Ev L (fl ⊔ flo k′)
upS k′ cv ev = proj₁ ev , toFlo k′ (λ q → cv (proj₂ ev) (suc q))

upL : ∀ {f s} n {φ} (cv : ∀ {L} → Ev L φ → Simᴵ (lim f s) L) {fl L} → Ev L (fl ⊔ φ) → Ev L (fl ⊔ flo (f n))
upL {f} n cv ev = proj₁ ev , toFlo (f n) (λ q → cv (proj₂ ev) (lim n q))

InpO : (j : Ordᴵ) → T → Ordˢ j → Set
InpO j η x = LabL x η × (x ≅ᴬ x) × CH j η x

module OMain (d : ℕ) {flE} {E : A (suc d) flE} {ζ : T} (GE : Gc (suc d) E ζ) where
  FE : FlrLabΩ flE ζ
  FE = proj₁ GE
  WE : ∀ {c} → Wd c (suc d) E ζ
  WE {c} = proj₁ (proj₂ GE) {c}
  OE : Od (suc d) E ζ
  OE = proj₁ (proj₂ (proj₂ GE))
  RE : Rd (suc d) E E
  RE = proj₂ (proj₂ (proj₂ GE))

  selfF : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} → t ≅ᴬ t → Rd (suc d) (fold (suc d) φ cv E t) (fold (suc d) φ cv E t)
  selfF {k} {φ} ex = foldR d (∼ᶠ-refl flE) RE (≅ᴵ-refl k) (∼ᶠ-refl φ) ex

  sucO : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {a : Ordˢ k} {y ys} → cof (y ∷ ys) ≡ c1 →
         Gc (suc d) (fold (suc d) φ cv E a) (ζ ++ pred (y ∷ ys)) → Od (suc d) (fold (suc d) φ cv E (Ord₊ˢ.suc a)) (ζ ++ (y ∷ ys))
  sucO {φ = φ} {cv} {a} {y} {ys} cc F {fl} {Q} {ρ} G =
    limOd d {ps = ρ} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → repA d Q (fold (suc d) φ cv E a) m} (c1Ω ζ cc)
          (λ m → subst (λ v → Od d (repA d Q (fold (suc d) φ cv E a) m) (ρ ++ v)) (sym (repW Ωᵗ ζ y ys cc m))
                       (H→O d (copyH d G (proj₁ F) (proj₂ F) m)))

  OA : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → FP0 φ → Lab0ᴸ t y → t ≅ᴬ t → Od (suc d) (fold (suc d) φ cv E t) (ζ ++ y)
  FullA : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → FP0 φ → Lab0ᴸ t y → t ≅ᴬ t → Gc (suc d) (fold (suc d) φ cv E t) (ζ ++ y)

  FullA {φ} {cv} {y = y} fp l ex =
    FlrLabΩ-⊔ (FlrLabΩ-ext y FE) (FP→FlrLabΩ fp) ,
    (λ {c} → WGd.WA d c (FLΩ→[] FE) WE (FP0→FP fp) l) ,
    OA fp l ex ,
    selfF ex

  OA {y = []} fp (lz c) ex = subst (Od (suc d) _) (sym (++-identityʳ ζ)) (wkO (suc d) proj₁ OE)
  OA {y = y ∷ ys} fp (lz c) ex = ⊥-elim (cof-ne y ys c)
  OA {y = []} fp (ls () l) ex
  OA {y = y ∷ ys} fp (ls c l) ex = sucO c (FullA fp l (s-invᴬ ex))
  OA {y = []} fp (ll () h) ex
  OA {φ = φ} {cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} fp (ll c h) ex =
    limOd (suc d) {ps = ζ} {y = y} {ys = ys} {F = λ n → fold (suc d) φ cv E (G n)} c (λ n → OA fp (h n) (l-invᴬ ex n))
  OA {y = []} fp (lŝ₀ () K h₀ hk) ex
  OA {φ = φ} {cv} {y = y ∷ ys} fp (lŝ₀ {t₀ = t₀} {g = g} c K h₀ hk) ex =
    ĉOd (suc d) {ps = ζ} {y = y} {ys = ys} {O₀ = fold (suc d) φ cv E t₀} {O = λ η e → fold (suc d) φ cv E (g η e)} c K
        (OA {cv = cv} fp h₀ (ŝ-refl₀ᴬ ex)) (λ k → OA {cv = cv} fp (hk k) (ŝ-reflgᴬ ex _ _ _ _ (≅ᴵ-refl _)))
  OA {y = []} fp (lĉ () K h₀ hk) ex
  OA {φ = φ} {cv} {y = y ∷ ys} fp (lĉ {o₀ = o₀} {o = o} c K h₀ hk) ex =
    ĉOd (suc d) {ps = ζ} {y = y} {ys = ys} {O₀ = fold (suc d) φ cv E o₀} {O = λ η e → fold (suc d) φ cv E (o η e)} c K
        (OA {cv = cv} fp h₀ (ĉ-refl₀ᴬ ex)) (λ k → OA {cv = cv} fp (hk k) (ĉ-reflgᴬ ex _ _))

  OH : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FH φ y → Hn t y → LabL₊ k Ll t y → t ≅ᴬ t → Od (suc d) (fold (suc d) φ cv E t) (ζ ++ y)
  FullH : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {z u v vs} → z ≡ ψᵗ u v ∷ vs → FH φ z → Hn t z → LabL₊ k Ll t z → t ≅ᴬ t →
          Gc (suc d) (fold (suc d) φ cv E t) (ζ ++ z)
  OΩ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {k} → k ≅ᴵ toLevel Y hY → ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} → Zc₀ k φ →
       Od (suc d) (fold (suc d) φ cv E (Ωˢ k)) (ζ ++ Ωt θ)
  OΩs : ∀ {w ws j} → kd j ≡ false → cof (w ∷ ws) ≡ c1 → (I : Idx (pred (w ∷ ws))) → j ≅ᴵ lvI I → ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ (suc j) L} →
        Od (suc d) (fold (suc d) φ cv E (Ωˢ (suc j))) (ζ ++ Ωt (w ∷ ws))

  FullH {k = k} {φ} {cv} {z = z} refl fp n l ex =
    FlrLabΩ-⊔ (FlrLabΩ-ext z FE) (FH→Ω refl fp) ,
    (λ {c} → WHd.WH d c (FLΩ→[] FE) WE (FH→FHc fp) n l) ,
    OH fp n l ex ,
    selfF ex

  OH fp (hΩ refl (Y , hY , lY , nY) e) l ex = OΩ Y hY lY nY e (Zc₀-of (Y , hY , lY , nY) e fp)
  OH {y = []} fp hz (gz c) ex = subst (Od (suc d) _) (sym (++-identityʳ ζ)) (wkO (suc d) proj₁ OE)
  OH {y = y ∷ ys} fp hz (gz c) ex = ⊥-elim (cof-ne y ys c)
  OH {y = []} fp (hs () n) l ex
  OH {y = y@(ψᵗ _ _) ∷ ys} fp (hs nb n) (gs c l) ex =
    sucO c (FullH (proj₂ (proj₂ (pred-Pr nb c))) (FH-pred nb c fp) n l (s-invᴬ ex))
  OH {y = []} fp (hl () n) l ex
  OH {φ = φ} {cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} fp (hl nb n) (gl c h) ex =
    limOd (suc d) {ps = ζ} {y = y} {ys = ys} {F = λ m → fold (suc d) φ cv E (G m)} c (λ m → OH (FH-fsn nb fp m) (n m) (h m) (l-invᴬ ex m))
  OH {y = []} fp (hi () n) l ex
  OH {φ = φ} {cv} {y = y ∷ ys} fp (hi {q = q} {f = f} nb n) (gi c I ej h) ex =
    limᵢOᴬ (suc d) {ps = ζ} {y = y} {ys = ys} {ac = λ ev → cv (proj₂ ev) q} {H = λ x → fold (suc d) φ cv E (f (intoˢ (<→◃ q) x))} c I ej
           (λ η x l → WHd.WH d zero (FLΩ→[] FE) WE (FH→FHc (FH-fsT nb fp η)) (n η x l) (h η x (→Ll (<→◃ q) l)))
           (λ η x l xx → OH (FH-fsT nb fp η) (n η x l) (h η x (→Ll (<→◃ q) l)) (i-respᴬ ex xx) , selfF (i-respᴬ ex xx))
  OH {y = []} fp (hĉ () cw K g₀ n₀ gk nk) l ex
  OH {φ = φ} {cv} {y = y ∷ ys} fp (hĉ {o₀ = o₀} {o = o} nb cw K g₀ n₀ gk nk) l ex =
    ĉOd (suc d) {ps = ζ} {y = y} {ys = ys} {O₀ = fold (suc d) φ cv E o₀} {O = λ η e → fold (suc d) φ cv E (o η e)} cw K
        (OH {cv = cv} (FH-fsn nb fp 0) n₀ g₀ (ĉ-refl₀ᴬ ex))
        (λ k → OH {cv = cv} (FH-fsn nb fp (suc k)) (nk k) (gk k) (ĉ-reflgᴬ ex _ _))
  OH {k = zero} fp (hŝ nb n₀ nk) (gŝ () c Iw bw ob h₀ hg) ex
  OH {k = suc _} {y = []} fp (hŝ nb n₀ nk) (gŝ kk () Iw bw ob h₀ hg) ex
  OH {k = suc _} {φ = φ} {cv} {y = y ∷ ys} fp (hŝ nb n₀ nk) (gŝ {t₀ = t₀} {g = g} kk c Iw bw ob h₀ hg) ex =
    ŝOd (suc d) {ps = ζ} {y = y} {ys = ys} {T₀ = fold (suc d) φ cv E t₀} {G = λ η e → fold (suc d) φ cv E (g η e)} c Iw bw (λ θ → OccΣ ζ (ob θ))
        (OH {cv = cv} (FH-fsT nb fp (natT 1)) n₀ h₀ (ŝ-refl₀ᴬ ex))
        (λ θ Y hY lY nθ lt e → OH {cv = cv} (FH-fsT nb fp θ) (nk θ Y hY lY nθ lt e) (hg θ Y hY lY nθ lt e) (ŝ-reflgᴬ ex _ _ _ _ (≅ᴵ-refl _)))
  OH {k = lim _ _} {y = []} fp (hŝ nb n₀ nk) (gŝ kk () Iw bw ob h₀ hg) ex
  OH {k = lim _ _} {φ = φ} {cv} {y = y ∷ ys} fp (hŝ nb n₀ nk) (gŝ {t₀ = t₀} {g = g} kk c Iw bw ob h₀ hg) ex =
    ŝOd (suc d) {ps = ζ} {y = y} {ys = ys} {T₀ = fold (suc d) φ cv E t₀} {G = λ η e → fold (suc d) φ cv E (g η e)} c Iw bw (λ θ → OccΣ ζ (ob θ))
        (OH {cv = cv} (FH-fsT nb fp (natT 1)) n₀ h₀ (ŝ-refl₀ᴬ ex))
        (λ θ Y hY lY nθ lt e → OH {cv = cv} (FH-fsT nb fp θ) (nk θ Y hY lY nθ lt e) (hg θ Y hY lY nθ lt e) (ŝ-reflgᴬ ex _ _ _ _ (≅ᴵ-refl _)))

  OΩ {θ = []} Ord₊.zero hY l nθ z≅ zc = OA zc (atomL (LabL-Ω Ord₊.zero hY l nθ z≅)) (Ωˢ-≅ᴬ z≅)
  OΩ {θ = y ∷ ys} Ord₊.zero hY l nθ z≅ zc with Lab0[] l
  ... | ()
  OΩ (Ord₊.suc Y) hY (l0 c ()) nθ (s≅ e) zc
  OΩ (Ord₊.suc Y) hY (lω c () h) nθ (s≅ e) zc
  OΩ {θ = []} (Ord₊.suc Y) hY (l1 () (s≅ e′) l) nθ (s≅ e) zc
  OΩ {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c₁ (s≅ e′) l) nθ {k = suc (suc j)} (s≅ e) zc =
    OΩs refl c₁ (Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c₁) e
  OΩ {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c₁ (s≅ e′) l) nθ {k = suc (lim f s)} (s≅ e) zc =
    OΩs refl c₁ (Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c₁) e
  OΩ {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c₁ (s≅ e′) l) nθ {k = suc zero} (s≅ e) {φ} {cv} zc =
    limᵢOᴬ (suc d) {ps = ζ} {y = ψᵗ θ []} {ys = []} {ac = λ ev → cv (proj₂ ev) zero}
           {H = λ x → fold (suc d) φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x))} cΩθ I e
           (λ η x l′ → subst (λ v → Wd zero (suc d) (fold (suc d) φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x))) (ζ ++ v)) (sym (fsTΩ c₁ η))
                             (wkW (suc d) (upS zero cv) (WGd.WV d zero (FLΩ→[] FE) WE {φ = fz} {cv = σ⊥f} FP-fz (inj₂ lw0) l′)))
           (λ η x l′ xx → subst (λ v → Od (suc d) (fold (suc d) φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x))) (ζ ++ v)) (sym (fsTΩ c₁ η))
                                (wkO (suc d) (upS zero cv) (OA {φ = fz} {cv = σ⊥f} FP0-fz (atomL l′) xx)) ,
                          wkRd (suc d) (upS zero cv) (upS zero cv) (selfF {φ = fz} {cv = σ⊥f} xx))
    where
    θ : T
    θ = w ∷ ws
    cΩθ : cof (Ωt θ) ≡ cΩ (pred θ)
    cΩθ = cong (E.cofψ0 θ) c₁
    I : Idx (pred θ)
    I = Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c₁
    σ⊥f : ∀ {L} → Ev L fz → Simᴵ zero L
    σ⊥f = cvFlo zero
  OΩ (Ord₊.lim F′) hY (l0 c₁ ()) nθ (l≅ k) zc
  OΩ (Ord₊.lim F′) hY (l1 c₁ () l) nθ (l≅ k) zc
  OΩ {θ = []} (Ord₊.lim F′) hY (lω () (l≅ k′) h) nθ (l≅ k) zc
  OΩ {θ = w ∷ ws} (Ord₊.lim F′) hY (lω c₁ (l≅ k′) h) nθ {k = lim f s} (l≅ ee) {φ} {cv} zc =
    limOd (suc d) {ps = ζ} {y = ψᵗ (w ∷ ws) []} {ys = []} {F = λ n → fold (suc d) φ cv E (Ord₊ˢ.up (self n) (Ωˢ (f n)))} (cong (E.cofψ0 (w ∷ ws)) c₁)
          (λ n → subst (λ u → Od (suc d) (fold (suc d) φ cv E (Ord₊ˢ.up (self n) (Ωˢ (f n)))) (ζ ++ u)) (sym (E.fsn0-eq w ws n c₁))
                       (wkO (suc d) (upL n cv) (OΩ (F′ n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c₁ n) (ee n) {flo (f n)} {cvFlo (f n)} (Zc₀-flo (f n)))))
  OΩ (Ord₊.limᵢ () f) hY l nθ e zc
  OΩ (Ord₊.up () x) hY l nθ e zc

  OΩs {w} {ws} {j} kj c₁ I e {φ} {cv} =
    limᵢOᴾ (suc d) {ps = ζ} {y = ψᵗ θ []} {ys = []} {ac = λ ev → cv (proj₂ ev) zero}
           {H = λ x → fold (suc d) φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x))} kj cΩθ I e (InpO j) i₀ hC hW hR hO
    where
    θ : T
    θ = w ∷ ws
    cΩθ : cof (Ωt θ) ≡ cΩ (pred θ)
    cΩθ = cong (E.cofψ0 θ) c₁
    i₀ : InpO j (Ωt (pred θ)) (Ωˢ j)
    i₀ = LabL-Ω (proj₁ I) (proj₁ (proj₂ I)) (proj₁ (proj₂ (proj₂ I))) (proj₂ (proj₂ (proj₂ I))) e , Ωˢ-≅ᴬ (≅ᴵ-refl j) , λ _ → hΩ refl I e , FHν I e
    hC : ∀ {v x′} → Out x′ (ψᵗ (pred θ) v ∷ []) → x′ ≅ᴬ x′ → InpO j (ψᵗ (pred θ) v ∷ []) x′
    hC o xx = frL₊ kj (proj₁ o) , xx , λ _ → proj₂ o , FHν I e
    lvⱼ : LvOK j j
    lvⱼ = inj₁ (⊑-suc j)
    hW : ∀ {η x} → InpO j η x → Wd j (suc d) (fold (suc d) φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x))) (ζ ++ fsT (Ωt θ) η)
    hW {η} {x} (lx , xx , ch) = subst (λ v → Wd j (suc d) (fold (suc d) φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x))) (ζ ++ v)) (sym (fsTΩ c₁ η))
                                  (wkW (suc d) (upS j cv) (WGd.WV d j (FLΩ→[] FE) WE {φ = flo j} {cv = cvFlo j} (FP-flo′ lvⱼ) lvⱼ lx))
    hR : ∀ {η x} → InpO j η x → Rd (suc d) (fold (suc d) φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x))) (fold (suc d) φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)))
    hR (lx , xx , ch) = wkRd (suc d) (upS j cv) (upS j cv) (selfF {φ = flo j} {cv = cvFlo j} xx)
    hO : ∀ {η x} → InpO j η x → Od (suc d) (fold (suc d) φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x))) (ζ ++ fsT (Ωt θ) η)
    hO {η} {x} (lx , xx , ch) = subst (λ v → Od (suc d) (fold (suc d) φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x))) (ζ ++ v)) (sym (fsTΩ c₁ η))
                                  (wkO (suc d) (upS j cv) (OH {φ = flo j} {cv = cvFlo j} (proj₂ (ch kj)) (proj₁ (ch kj)) (toL₊ kj lx) xx))
```

## §3 $\Omega_\Omega$ 的闭包, 一切深度

弹栈的地板见证 `FWd`: 输入栈每一层的地板都被一个出现在 "该层之内一切点标签" 的下标支配. `FWh` 是它的单层形, `FWd-of` 对 $d$ 递归把它展开. 第 $0$ 层的前缀是 $\rho$ (裸出现), 第 $\ge1$ 层的出现在 $\psi_\Omega(\rho+\cdots)$ 之下: 这是深度带来的**唯一**分情形.

```agda
FWh : Ordᴵ → ℕ → Flr → T → PT → T → Set
FWh c zero    φ ps y ys = FW[ c ] φ ps y ys
FWh c (suc d) φ ps y ys = ∀ {K} (k : InF K φ) → IgnK c k ⊎ Σ T λ w → Σ (Idx w) λ Iw → (K ≼ lvI Iw) × (∀ θ → Occ w (ψᵗ Ωᵗ (ps ++ fsT (y ∷ ys) θ) ∷ []))

IgnK-up : ∀ {c c′ K φ} {k : InF K φ} → Up c c′ → IgnK c k → IgnK c′ k
IgnK-up u (inj₁ (inj₁ e0)) = inj₁ (inj₁ e0)
IgnK-up u (inj₁ (inj₂ kc)) = inj₁ (inj₂ (≼-trans kc u))
IgnK-up u (inj₂ (b , le))  = inj₂ (b , ⊑ᴵ-trans le (sB u))

FWh-step : ∀ d {c c′ φ fl ρ ps y ys} → cof (y ∷ ys) ≡ cΩ [] → Up c c′ → FWh c (suc d) φ ps y ys → FL c′ d fl ρ →
           FWh c′ d (fl ⊔ φ) ρ (ψᵗ Ωᵗ (ps ++ (y ∷ ys))) []
FWh-step zero u′ u F Fl (inl k) with Fl k
... | inj₁ g = inj₁ g
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → OccPre _ o)
FWh-step zero {ρ = ρ} {ps = ps} cs u F Fl (inr k) with F k
... | inj₁ g = inj₁ (IgnK-up u g)
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (λ v → Occ w (ρ ++ v)) (sym (penΩ ps cs I0 θ)) (OccΣ ρ (o θ)))
FWh-step (suc d) cs u F Fl (inl k) with Fl k
... | inj₁ g = inj₁ g
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → o _)
FWh-step (suc d) {ρ = ρ} {ps = ps} cs u F Fl (inr k) with F k
... | inj₁ g = inj₁ (IgnK-up u g)
... | inj₂ (w , Iw , kw , o) =
  inj₂ (w , Iw , kw , λ θ → subst (λ v → Occ w (ψᵗ Ωᵗ (ρ ++ v) ∷ [])) (sym (penΩ ps cs I0 θ)) (od (OccΣ ρ (o θ))))

FWd-of : ∀ d {c φ ps y ys} → cof (y ∷ ys) ≡ cΩ [] → FWh c d φ ps y ys → FWd c d φ ps y ys
FWd-of zero cs F (inl k) = F k
FWd-of zero cs F (inr ink) = inj₁ (inj₁ (inj₁ z≅))
FWd-of (suc d) {ps = ps} cs F u Fl = FWd-of d (cΩΩ ps cs I0) (FWh-step d cs u F Fl)

FWhₒ : ℕ → Flr → T → PT → T → Set
FWhₒ zero    φ ps y ys = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ Σ T λ w → Σ (Idx w) λ Iw → (K ≼ lvI Iw) × Ob w ps y ys
FWhₒ (suc d) φ ps y ys = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ Σ T λ w → Σ (Idx w) λ Iw → (K ≼ lvI Iw) × (∀ θ → Occ w (ψᵗ Ωᵗ (ps ++ fsT (y ∷ ys) θ) ∷ []))

FWhₒ-step : ∀ d {φ fl ρ ps y ys} → cof (y ∷ ys) ≡ cΩ [] → FWhₒ (suc d) φ ps y ys → FLg d fl ρ →
            FWhₒ d (fl ⊔ φ) ρ (ψᵗ Ωᵗ (ps ++ (y ∷ ys))) []
FWhₒ-step zero cs F Fl (inl k) with Fl k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → OccPre _ o)
FWhₒ-step zero {ρ = ρ} {ps = ps} cs F Fl (inr k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (λ v → Occ w (ρ ++ v)) (sym (penΩ ps cs I0 θ)) (OccΣ ρ (o θ)))
FWhₒ-step (suc d) cs F Fl (inl k) with Fl k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → o _)
FWhₒ-step (suc d) {ρ = ρ} {ps = ps} cs F Fl (inr k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) =
  inj₂ (w , Iw , kw , λ θ → subst (λ v → Occ w (ψᵗ Ωᵗ (ρ ++ v) ∷ [])) (sym (penΩ ps cs I0 θ)) (od (OccΣ ρ (o θ))))

FWo-of : ∀ d {φ ps y ys} → cof (y ∷ ys) ≡ cΩ [] → FWhₒ d φ ps y ys → FWo d φ ps y ys
FWo-of zero cs F (inl k) = F k
FWo-of zero cs F (inr ink) = inj₁ z≅
FWo-of (suc d) {ps = ps} cs F Fl = FWo-of d (cΩΩ ps cs I0) (FWhₒ-step d cs F Fl)

ZcK : ∀ {c} k → Zc c k (fk k)
ZcK zero = FP-z
ZcK (suc k) = tt
ZcK (lim f s) = tt

Zc₀K : ∀ k → Zc₀ k (fk k)
Zc₀K zero = FP0-z
Zc₀K (suc k) = tt
Zc₀K (lim f s) = tt

wΩ̂ : ∀ d {c flE} {E : A (suc d) flE} {ζ} → FLΩ[ c ] flE ζ → Wd c (suc d) E ζ → Wd c (suc d) (Ω̂A (suc d) E) (ζ ++ ΩΩ ∷ [])
wΩ̂ d {c} {flE} {E} {ζ} FE WE =
  cloWd (suc d) {ps = ζ} {y = ΩΩ} {ys = []}
        {t = fold (suc d) (fk zero) (λ e → e) E (Ωˢ (suc zero))} {g = λ η → fold (suc d) (fk η) (λ e q → e (suc q)) E (Ωˢ η)}
        (FWd-of (suc d) refl Fh) refl
        (WHd.WΩ d c FE WE one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _) {fk zero} {λ e → e} tt)
        (λ θ Y hY lY nθ lt → WHd.WΩ d c FE WE Y hY lY nθ (≅ᴵ-refl _) {fk (toLevel Y hY)} {λ e q → e (suc q)} (ZcK (toLevel Y hY)))
  where
  Fh : FWh c (suc d) flE ζ ΩΩ []
  Fh k with FE k
  ... | inj₁ g = inj₁ g
  ... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → o _)

oΩ̂ : ∀ d {flE} {E : A (suc d) flE} {ζ} → Gc (suc d) E ζ → Od (suc d) (Ω̂A (suc d) E) (ζ ++ ΩΩ ∷ [])
oΩ̂ d {flE} {E} {ζ} GE =
  cloOd (suc d) {ps = ζ} {y = ΩΩ} {ys = []}
        {t = fold (suc d) (fk zero) (λ e → e) E (Ωˢ (suc zero))} {g = λ η → fold (suc d) (fk η) (λ e q → e (suc q)) E (Ωˢ η)}
        (FWo-of (suc d) refl Fh) refl
        (OMain.OΩ d GE one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _) {fk zero} {λ e → e} tt)
        (λ θ Y hY lY nθ lt → OMain.OΩ d GE Y hY lY nθ (≅ᴵ-refl _) {fk (toLevel Y hY)} {λ e q → e (suc q)} (Zc₀K (toLevel Y hY)))
  where
  Fh : FWhₒ (suc d) flE ζ ΩΩ []
  Fh k with proj₁ GE k
  ... | inj₁ e = inj₁ e
  ... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → o _)

rΩ̂ : ∀ d {flE flE′} {E : A (suc d) flE} {E′ : A (suc d) flE′} → flE ∼ᶠ flE′ → Rd (suc d) E E′ → Rd (suc d) (Ω̂A (suc d) E) (Ω̂A (suc d) E′)
rΩ̂ d {flE} {flE′} {E} {E′} s H =
  cloRd (suc d) {t = fold (suc d) (fk zero) (λ e → e) E (Ωˢ (suc zero))} {g = λ η → fold (suc d) (fk η) (λ e q → e (suc q)) E (Ωˢ η)}
        {t′ = fold (suc d) (fk zero) (λ e → e) E′ (Ωˢ (suc zero))} {g′ = λ η → fold (suc d) (fk η) (λ e q → e (suc q)) E′ (Ωˢ η)} s
        (foldR d s H (≅ᴵ-refl (suc zero)) (fk∼ z≅) (Ωˢ-≅ᴬ (≅ᴵ-refl (suc zero))))
        (λ η η′ eη → foldR d s H eη (fk∼ eη) (Ωˢ-≅ᴬ eη))
```

## §4 主定理

`HΩ̂ᵍ d`: 一切深度的闭包. 深度 $0$ 是 Uniform3Full 的 `goodΩ̂₀ʰ` (经 `G1-of`), 深度 $d+1$ 是 `goodΩ̂`. **对 $d$ 没有归纳**: `goodΩ̂ d` 直接证明, 不用 `goodΩ̂ (d−1)`; 只有行引理对 $d$ 递归.

```agda
goodΩ̂ : ∀ d → Gc (suc (suc d)) {fk zero} (Ω̂A (suc d)) []
goodΩ̂ d = (λ { ink → inj₁ z≅ }) , (λ {c} u F hE → wΩ̂ d F hE) , (λ GE → oΩ̂ d GE) , (λ s H → rΩ̂ d s H)

G1-of : ∀ {φ} {E : A 1 φ} {ζ} → GA1ʰ E ζ → Gc 1 E ζ
G1-of G = fl1ʰ G , (λ {c} {c′} u F hP → gw1ʰ G {c′} F hP) , g01ʰ G , gr1ʰ G

HΩ̂ᵍ : ∀ d → Gc (suc d) {fk zero} (Ω̂A d) []
HΩ̂ᵍ zero    = G1-of goodΩ̂₀ʰ
HΩ̂ᵍ (suc d) = goodΩ̂ d
```
