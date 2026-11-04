> **机械克隆, 验收用.** 由 `ScafLadderZUniform3SqA` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆.** 由 `Uniform3SqA` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 统一形 (三): 层对齐的标签理论 (二) (OmegaSqA §1–§4 的移植)

> [OmegaSqA](OmegaSqA.lagda.md) §1–§4 在修正的折叠上重编译, 改动 23 行 (`Low` 代替 $\sqsubseteq2$, `toFlo` 的形状). `TΩ₃-label`、`Tη₂-label`、`TΩ2-targetᴬ` 都成立. OmegaSqA §5 的否定在这里**没有**对应: `Refute.leaf` 的 `MxL` 在新树上假 ([Uniform3Walk](Uniform3Walk.lagda.md)), `¬TΩ2-label` 被 [Uniform3Full](Uniform3Full.lagda.md) 的 `TΩ2-label` 取代.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZUniform3SqA where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.LadderLabZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; _+ˢ_)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; []<; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fsT-c1)
open import OCF.Align.Bachmann using (gt→<)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-fsn; walkD; tO-desc-NF)
open import OCF.Align.Standard using (d₀)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.Stage2 using (Ωᵗ; tO)
open import OCF.Align.LadderLabZStage2Label using (one⁰; Lab-oc)
open import OCF.Align.LadderLabZDecoupleBase using (ΩΩ)
open import OCF.Align.LadderLabZDecouple using (Idx; lvI)
open import OCF.Align.LadderLabZGoodLBase
open import OCF.Align.LadderLabZOmegaExpBase using (OccΣ; repW; ωW; snoc)
open import OCF.Align.LadderLabZOmegaExp using (ψΩ₀; tΩ1; tΩ1-NF)
open import OCF.Align.LadderLabZOmegaKBase using (tΩ2; tΩ2-NF)
open import OCF.Align.LadderLabZNonTightBase using (I₂)
open import OCF.Align.LadderLabZUniformS
open import OCF.Align.LadderLabZUniform3Base
open import OCF.Align.LadderLabZUniform3Depth1 using (wkLW; wkL0; c1Ω; cωΩ; cΩΩ; penΩ)
open import OCF.Align.LadderLabZUniform3 using (LΩ1; nf-pΩ; TΩ1-label)
open import OCF.Align.LadderLabZUniform3Rel
open import OCF.Align.LadderLabZUniform3SqABase
open GA1ᴬ
open BranchΩᴬ
```

## §1 深度 1 的折叠定理 (目标 0 部分), 第 $\le2$ 层

**目标 0 的地板策略.** 目标 0 处没有可忽略的项 (除 $\cong0$): `FP0 φ` 要求每项 $\cong0$ 或 $\cong1$. 第 $\le2$ 层尾巴的一切内部地板 (`fz`、`fk 0`、`fk 1`) 都满足. 目标 0 处 W 定理用 `LW[ zero ]`, 它与 `LW` 相同 (非零带 `Idx` 的目标都 $\succeq0$, `Up0`).

```agda
FP0 : Flr → Set
FP0 φ = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ (K ≅ᴵ one)

FP0→FP : ∀ {c φ} → FP0 φ → FP c φ
FP0→FP f k with f k
... | inj₁ e = inj₁ (inj₁ (inj₁ e))
... | inj₂ e = inj₂ e

FP0-fz : FP0 fz
FP0-fz ()

FP0-z : FP0 (fk zero)
FP0-z ink = inj₁ z≅

FP0-1 : FP0 (fk one)
FP0-1 ink = inj₂ (≅ᴵ-refl one)

FP0-flo : ∀ {k′} → Low (suc k′) → FP0 (flo k′)
FP0-flo lw1 ()
FP0-flo lw2 ink = inj₁ z≅

two-pred : ∀ {k′} → Low (suc k′) → Low k′
two-pred lw1 = lw0
two-pred lw2 = lw1

Up0 : ∀ {i w} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → Up zero i
Up0 {w = []} Iw ei ki = ⊥-elim (ne-w′ Iw ei ki)
  where
  ne-w′ : ∀ {i} (Iw : Idx []) → i ≅ᴵ lvI Iw → kd i ≡ false → ⊥
  ne-w′ Iw ei ki = tf (trans (sym (kdI[]′ Iw)) (trans (sym (kd-≅ ei)) ki))
    where
    kdI[]′ : (I : Idx []) → kd (lvI I) ≡ true
    kdI[]′ (Ord₊.zero , hY , lY , nY) = refl
    kdI[]′ (Ord₊.suc Y , hY , l0 c () , nY)
    kdI[]′ (Ord₊.suc Y , hY , l1 () e l , nY)
    kdI[]′ (Ord₊.suc Y , hY , lω () e h , nY)
    kdI[]′ (Ord₊.lim F , hY , l0 c () , nY)
    kdI[]′ (Ord₊.lim F , hY , l1 () e l , nY)
    kdI[]′ (Ord₊.lim F , hY , lω () e h , nY)
    kdI[]′ (Ord₊.limᵢ () f , hY , lY , nY)
    kdI[]′ (Ord₊.up () x , hY , lY , nY)
Up0 {w = x ∷ xs} (Y , hY , lY , nY) ei ki with one⊑lab hY lY nY []<
... | s⊑ e q = Up-≅ (inj₁ (via e q)) (≅ᴵ-sym ei)

LW0→LW : ∀ {φ} {R : Run φ} {u} → LW[ zero ] R u → LW R u
LW0→LW h ev p Iw ei ki = h ev p Iw ei ki (Up0 Iw ei ki)
```

**好帧的派生形式.** `gv1ᴴ`: 好帧作用于层对齐的好前缀给层对齐的好前缀 (Uniform2Depth1 `GV1` 的对应); 副本引理 `copyGAᴬ`/`copyGRᴬ`.

```agda
wkGRᴬ : ∀ {φ ψ} {R : Run φ} (le : ∀ {L} → Ev L ψ → Ev L φ) {u} → GRᴬ R u → GRᴬ (wk 0 le R) u
wkGRᴬ le (grᴬ a b c) = grᴬ (wkLW le a) (wkL0 le b) (wkRᴬ le le c)

gv1ᴴ : ∀ {φ} {F : A 1 φ} {b} → GA1ᴴ F b → ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π → GRᴬ (F P) (π ++ ψΩᵗ b)
gv1ᴴ G (F , GP) = grᴬ (LW0→LW (gw1ᴴ G (FlrLab→[] F) (LW→LW[] (gWᴬ GP)))) (g01ᴴ G (F , GP)) (gr1ᴴ G (∼ᶠ-refl _) (gRᴬ GP))

FP0-rep : ∀ {flE φ ζ b} → FlrLabΩ flE ζ → FP0 φ → ∀ m → FlrLab (flE ⊔ φ) (replicate (suc m) (ψᵗ Ωᵗ (ζ ++ b)))
FP0-rep {b = b} FE f m (inl k) with FE k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , occ-hd (o b))
FP0-rep FE f m (inr k) with f k
... | inj₁ e0 = inj₁ e0
... | inj₂ e1 with wit1 e1
...   | w , Iw , kw , o = inj₂ (w , Iw , kw , occ-hd (o _))

L0≡π : ∀ {φ} (R : Run φ) π {u v} → u ≡ v → L0 R (π ++ u) → L0 R (π ++ v)
L0≡π R π refl h = h

L0≡ζ : ∀ {φ} (R : Run φ) {π u v} → u ≡ v → L0 R (π ++ ψΩᵗ u) → L0 R (π ++ ψΩᵗ v)
L0≡ζ R refl h = h

module Depth1ᴴ {flE} {E : A 1 flE} {ζ : T} (GE : GA1ᴴ E ζ) where
  open WGen GE

  copyGAᴬ : ∀ {ψ fl} {P : Run fl} {π b} {fr : A 1 ψ} → GA0ᴬ P π → (∀ m → FlrLab ψ (replicate (suc m) (ψᵗ Ωᵗ b))) →
            (∀ {fl′} {Q : Run fl′} {ρ} → GA0ᴬ Q ρ → GRᴬ (fr Q) (ρ ++ ψΩᵗ b)) →
            ∀ m → GA0ᴬ (repA 0 P fr (suc m)) (π ++ replicate (suc m) (ψᵗ Ωᵗ b))
  copyGAᴬ (F , GP) Fψ Gfr zero = FlrLab-⊔ F (Fψ 0) , Gfr (F , GP)
  copyGAᴬ {π = π} {b = b} (F , GP) Fψ Gfr (suc m) =
    FlrLab-⊔ F (Fψ (suc m)) ,
    wkGRᴬ _ (subst (GRᴬ _) (snoc π (suc m) (ψᵗ Ωᵗ b)) (Gfr (copyGAᴬ (F , GP) Fψ Gfr m)))

  copyGRᴬ : ∀ {ψ fl} {P : Run fl} {π b} {fr : A 1 ψ} → GA0ᴬ P π → (∀ m → FlrLab ψ (replicate (suc m) (ψᵗ Ωᵗ b))) →
            (∀ {fl′} {Q : Run fl′} {ρ} → GA0ᴬ Q ρ → GRᴬ (fr Q) (ρ ++ ψΩᵗ b)) →
            ∀ m → GRᴬ (repA 0 P fr m) (π ++ replicate m (ψᵗ Ωᵗ b))
  copyGRᴬ {ψ = ψ} {π = π} (F , GP) Fψ Gfr zero =
    wkGRᴬ (proj₁ {B = λ _ → Ev _ ψ}) (subst (GRᴬ _) (sym (++-identityʳ π)) GP)
  copyGRᴬ GP Fψ Gfr (suc m) = proj₂ (copyGAᴬ GP Fψ Gfr m)
```

**互递归 (`O`/`Full`).** Uniform2Depth1 §11 的 `O1A`/`O1₁`/`FullA`/`Full₁` 推广到第 $\le2$ 层 (层号 $k\sqsubseteq2$, 地板策略 `FP0`), 互模拟由 Relative 的 `fold-≅1ᴬ` (无对齐前提), `gi` 行由 OmegaSqABase 的 `limᵢ0ᴬ` (`W₊` 给链点的标签, 递归给链点的目标 0 标签, `fold-≅1ᴬ` 给链点的互模拟).

```agda
  OA : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → FP0 φ → Lab0ᴸ t y → t ≅ᴬ t →
       ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π → L0 (fold 1 φ cv E t P) (π ++ ψΩᵗ (ζ ++ y))
  FullA : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → FP0 φ → Lab0ᴸ t y → t ≅ᴬ t →
          GA1ᴴ (fold 1 φ cv E t) (ζ ++ y)
  OV : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP0 φ → Low k → LabL t y → t ≅ᴬ t →
       ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π → L0 (fold 1 φ cv E t P) (π ++ ψΩᵗ (ζ ++ y))
  FullV : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP0 φ → Low k → LabL t y → t ≅ᴬ t →
          GA1ᴴ (fold 1 φ cv E t) (ζ ++ y)
  O₊ : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP0 φ → Low k → LabL₊ k Ll t y → t ≅ᴬ t →
       ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π → L0 (fold 1 φ cv E t P) (π ++ ψΩᵗ (ζ ++ y))
  Full₊ : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP0 φ → Low k → LabL₊ k Ll t y → t ≅ᴬ t →
          GA1ᴴ (fold 1 φ cv E t) (ζ ++ y)

  FullA {φ} {cv} {y = y} fp l ex =
    ga1ᴴ (FlrLabΩ-⊔ (FlrLabΩ-ext y (fl1ᴴ GE)) (FP→FlrLabΩ fp)) (λ {c} → WA (FP0→FP fp) l) (OA fp l ex)
         (fold-≅1ᴬ (∼ᶠ-refl flE) (gr1ᴴ GE) z≅ (∼ᶠ-refl φ) ex)

  FullV {k = zero}    fp lv at ex = FullA fp (atomL at) ex
  FullV {k = suc _}   fp lv h  ex = Full₊ fp lv h ex
  FullV {k = lim _ _} fp lv h  ex = Full₊ fp lv h ex

  Full₊ {k = k} {φ} {cv} {y = y} fp lv l ex =
    ga1ᴴ (FlrLabΩ-⊔ (FlrLabΩ-ext y (fl1ᴴ GE)) (FP→FlrLabΩ fp)) (λ {c} → W₊ (FP0→FP fp) (inj₂ lv) l) (O₊ fp lv l ex)
         (fold-≅1ᴬ (∼ᶠ-refl flE) (gr1ᴴ GE) (≅ᴵ-refl k) (∼ᶠ-refl φ) ex)

  OV {k = zero}    fp lv at ex = OA fp (atomL at) ex
  OV {k = suc _}   fp lv h  ex = O₊ fp lv h ex
  OV {k = lim _ _} fp lv h  ex = O₊ fp lv h ex

  OA {y = []} fp (lz c) ex {P = P} GP = wkL0 {R = E P} (λ ev → proj₁ ev , proj₁ (proj₂ ev)) (L0≡ζ (E P) (sym (++-identityʳ ζ)) (g01ᴴ GE GP))
  OA {y = y ∷ ys} fp (lz c) ex GP = ⊥-elim (cof-ne y ys c)
  OA {y = []} fp (ls () l) ex GP
  OA {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y ∷ ys} fp (ls c l) ex {P = P} {π = π} GP =
    lim0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → repA 0 P (fold 1 φ cv E a) m} (c1Ω ζ c)
         (λ m → L0≡π (repA 0 P (fold 1 φ cv E a) m) π (sym (repW Ωᵗ ζ y ys c m))
                      (g0ᴬ (copyGRᴬ GP (FP0-rep (fl1ᴴ GE) fp) (gv1ᴴ (FullA {cv = cv} fp l (s-invᴬ ex))) m)))
  OA {y = []} fp (ll () h) ex GP
  OA {φ = φ} {cv = cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} fp (ll c h) ex {P = P} {π = π} GP =
    lim0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → fold 1 φ cv E (G m) P} (cωΩ ζ c)
         (λ n → L0≡π (fold 1 φ cv E (G n) P) π (sym (ωW Ωᵗ ζ y ys c n)) (OA {cv = cv} fp (h n) (l-invᴬ ex n) GP))
  OA {y = []} fp (lŝ₀ () K h₀ hk) ex GP
  OA {φ = φ} {cv = cv} {y = y ∷ ys} fp (lŝ₀ {t₀ = t₀} {g = g} c K h₀ hk) ex {P = P} {π = π} GP =
    ĉ0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E t₀ P} {O = λ η e → fold 1 φ cv E (g η e) P}
       (cωΩ ζ c) K (L0≡π (fold 1 φ cv E t₀ P) π (sym (ωW Ωᵗ ζ y ys c 0)) (OA {cv = cv} fp h₀ (ŝ-refl₀ᴬ ex) GP))
       (λ k → L0≡π (fold 1 φ cv E (g (lvK K k) (dxK K k)) P) π (sym (ωW Ωᵗ ζ y ys c (suc k)))
                   (OA {cv = cv} fp (hk k) (ŝ-reflgᴬ ex _ _ _ _ (≅ᴵ-refl _)) GP))
  OA {y = []} fp (lĉ () K h₀ hk) ex GP
  OA {φ = φ} {cv = cv} {y = y ∷ ys} fp (lĉ {o₀ = o₀} {o = o} c K h₀ hk) ex {P = P} {π = π} GP =
    ĉ0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E o₀ P} {O = λ η e → fold 1 φ cv E (o η e) P}
       (cωΩ ζ c) K (L0≡π (fold 1 φ cv E o₀ P) π (sym (ωW Ωᵗ ζ y ys c 0)) (OA {cv = cv} fp h₀ (ĉ-refl₀ᴬ ex) GP))
       (λ k → L0≡π (fold 1 φ cv E (o (lvK K k) (dxK K k)) P) π (sym (ωW Ωᵗ ζ y ys c (suc k))) (OA {cv = cv} fp (hk k) (ĉ-reflgᴬ ex _ _) GP))

  O₊ {y = []} fp lv (gz c) ex {P = P} GP = wkL0 {R = E P} (λ ev → proj₁ ev , proj₁ (proj₂ ev)) (L0≡ζ (E P) (sym (++-identityʳ ζ)) (g01ᴴ GE GP))
  O₊ {y = y ∷ ys} fp lv (gz c) ex GP = ⊥-elim (cof-ne y ys c)
  O₊ {y = []} fp lv (gs () l) ex GP
  O₊ {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y ∷ ys} fp lv (gs c l) ex {P = P} {π = π} GP =
    lim0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → repA 0 P (fold 1 φ cv E a) m} (c1Ω ζ c)
         (λ m → L0≡π (repA 0 P (fold 1 φ cv E a) m) π (sym (repW Ωᵗ ζ y ys c m))
                      (g0ᴬ (copyGRᴬ GP (FP0-rep (fl1ᴴ GE) fp) (gv1ᴴ (Full₊ {cv = cv} fp lv l (s-invᴬ ex))) m)))
  O₊ {y = []} fp lv (gl () h) ex GP
  O₊ {φ = φ} {cv = cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} fp lv (gl c h) ex {P = P} {π = π} GP =
    lim0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → fold 1 φ cv E (G m) P} (cωΩ ζ c)
         (λ n → L0≡π (fold 1 φ cv E (G n) P) π (sym (ωW Ωᵗ ζ y ys c n)) (O₊ {cv = cv} fp lv (h n) (l-invᴬ ex n) GP))
  O₊ {k = suc k′} {cv = cv} fp lv (gu {r = zero} h) ex GP ev p =
    OV {φ = flo k′} {cv = cvFlo k′} (FP0-flo lv) (two-pred lv) h (u-reflᴬ zero ex) GP
       (proj₁ ev , (proj₁ (proj₂ ev) , toFlo k′ (λ q → cv (proj₂ (proj₂ ev)) (suc q)))) p
  O₊ {k = lim f s} fp () (gu {r = self n} h) ex
  O₊ {y = []} fp lv (gi () I ej h) ex GP
  O₊ {k = k} {φ = φ} {cv = cv} {y = y ∷ ys} fp lv (gi {q = q} {f = f} c I ej h) ex {fl = fl} {P = P} {π = π} GP =
    limᵢ0ᴬ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {ac = λ ev → cv (proj₂ (proj₂ ev)) q}
           {H = λ x → fold 1 φ cv E (f (intoˢ (<→◃ q) x)) P} (cΩΩ ζ c I) I ej
           (λ η x l → subst (λ u → LW _ (π ++ u)) (sym (penΩ ζ c I η))
                            (LW0→LW (W₊ (FP0→FP fp) (inj₂ lv) (h η x (→Ll (<→◃ q) l)) (FlrLab→[] (proj₁ GP)) (LW→LW[] (gWᴬ (proj₂ GP))))))
           (λ η x l xx → L0≡π (fold 1 φ cv E (f (intoˢ (<→◃ q) x)) P) π (sym (penΩ ζ c I η))
                               (O₊ {cv = cv} fp lv (h η x (→Ll (<→◃ q) l)) (i-respᴬ ex xx) GP) ,
                         fold-≅1ᴬ (∼ᶠ-refl flE) (gr1ᴴ GE) (≅ᴵ-refl k) (∼ᶠ-refl φ) (i-respᴬ ex xx) (∼ᶠ-refl fl) (gRᴬ (proj₂ GP)))
  O₊ {y = []} fp lv (gĉ () K h₀ hk) ex GP
  O₊ {φ = φ} {cv = cv} {y = y ∷ ys} fp lv (gĉ {o₀ = o₀} {o = o} c K h₀ hk) ex {P = P} {π = π} GP =
    ĉ0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E o₀ P} {O = λ η e → fold 1 φ cv E (o η e) P}
       (cωΩ ζ c) K (L0≡π (fold 1 φ cv E o₀ P) π (sym (ωW Ωᵗ ζ y ys c 0)) (O₊ {cv = cv} fp lv h₀ (ĉ-refl₀ᴬ ex) GP))
       (λ k → L0≡π (fold 1 φ cv E (o (lvK K k) (dxK K k)) P) π (sym (ωW Ωᵗ ζ y ys c (suc k))) (O₊ {cv = cv} fp lv (hk k) (ĉ-reflgᴬ ex _ _) GP))
  O₊ {k = zero} fp lv (gŝ () c Iw bw ob h₀ hg) ex GP
  O₊ {k = suc _} {y = []} fp lv (gŝ kk () Iw bw ob h₀ hg) ex GP
  O₊ {k = suc _} {φ = φ} {cv = cv} {y = y ∷ ys} fp lv (gŝ {w = w} {t₀ = t₀} {g = g} kk c Iw bw ob h₀ hg) ex {P = P} {π = π} GP =
    ŝ0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {T₀ = fold 1 φ cv E t₀ P} {G = λ η e → fold 1 φ cv E (g η e) P}
       (cΩΩ ζ c I0) Iw bw (λ θ → subst (λ u → Occ w (π ++ u)) (sym (penΩ ζ c I0 θ)) (OccΣ π (od (OccΣ ζ (ob θ)))))
       (L0≡π (fold 1 φ cv E t₀ P) π (sym (penΩ ζ c I0 (natT 1))) (O₊ {cv = cv} fp lv h₀ (ŝ-refl₀ᴬ ex) GP))
       (λ θ Y hY lY nθ lt e → L0≡π (fold 1 φ cv E (g (toLevel Y hY) e) P) π (sym (penΩ ζ c I0 θ))
                                    (O₊ {cv = cv} fp lv (hg θ Y hY lY nθ lt e) (ŝ-reflgᴬ ex _ _ _ _ (≅ᴵ-refl _)) GP))
  O₊ {k = lim _ _} {y = []} fp lv (gŝ kk () Iw bw ob h₀ hg) ex GP
  O₊ {k = lim _ _} {φ = φ} {cv = cv} {y = y ∷ ys} fp lv (gŝ {w = w} {t₀ = t₀} {g = g} kk c Iw bw ob h₀ hg) ex {P = P} {π = π} GP =
    ŝ0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {T₀ = fold 1 φ cv E t₀ P} {G = λ η e → fold 1 φ cv E (g η e) P}
       (cΩΩ ζ c I0) Iw bw (λ θ → subst (λ u → Occ w (π ++ u)) (sym (penΩ ζ c I0 θ)) (OccΣ π (od (OccΣ ζ (ob θ)))))
       (L0≡π (fold 1 φ cv E t₀ P) π (sym (penΩ ζ c I0 (natT 1))) (O₊ {cv = cv} fp lv h₀ (ŝ-refl₀ᴬ ex) GP))
       (λ θ Y hY lY nθ lt e → L0≡π (fold 1 φ cv E (g (toLevel Y hY) e) P) π (sym (penΩ ζ c I0 θ))
                                    (O₊ {cv = cv} fp lv (hg θ Y hY lY nθ lt e) (ŝ-reflgᴬ ex _ _ _ _ (≅ᴵ-refl _)) GP))
```

**读法.** 与 Uniform2Depth1 `O1₁` 比: 层号从 $\{0,1\}$ 放宽到 $\sqsubseteq2$, `TrivLeaf` 换成 `FP0`, `lowA` 消失 (互模拟不再需要对齐前提), `gi` 行里链点的标签来自一般层号的 `W₊` 而不是 `W1₁`. 第 2 层尾巴 (`Ω₂`、`Ω₂+1` 及**一切**带标签的第 2 层树) 一次覆盖: Uniform2 §1 的 `FullΩ₂`/`FullΩ₂₊` 是它的实例.

## §2 $\Omega_{k+1}$ 尾巴 ($k\sqsubseteq2$)

$\Omega_{k+1}=\mathrm{limᵢ}_k(\mathtt{up\ zero})$ 的根是 `gi` 行, 根地板 $\varphi$ 从不被读到; 输入 $x$ (第 $k$ 层) 的折叠以 `flo k` 为地板, 由 §1 处理. 这给出 $\Omega_3$ (层号 3 本身不满足 §1 的层号条件, 但它的输入在第 2 层). 标签侧: $\theta=w+1$ 的 $\Omega_\theta$ 的基本列在 $\eta$ 处是 $\eta$ (`fsT-c1`), 节点层的 `Idx` 是 $w$ 的.

```agda
  module ΩS {k} (lv : Low k) (fpk : FP0 (flo k)) {w ws} (c1θ : cof (w ∷ ws) ≡ c1) (I : Idx (pred (w ∷ ws)))
            (ej : k ≅ᴵ lvI I) {φ} {cv : ∀ {L} → Ev L φ → Simᴵ (suc k) L} where
    θ : T
    θ = w ∷ ws
    cΩθ : cof (Ωt θ) ≡ cΩ (pred θ)
    cΩθ = cong (E.cofψ0 θ) c1θ
    pen′ : ∀ η → fsT (ψᵗ Ωᵗ (ζ ++ Ωt θ) ∷ []) η ≡ ψᵗ Ωᵗ (ζ ++ η) ∷ []
    pen′ η = trans (penΩ ζ {y = ψᵗ θ []} {ys = []} cΩθ I η) (cong (λ u → ψᵗ Ωᵗ (ζ ++ u) ∷ []) (fsT-c1 θ (cof θ) c1θ η))

    le : ∀ {fl L} → Ev L (fl ⊔ (flE ⊔ φ)) → Ev L (fl ⊔ (flE ⊔ flo k))
    le ev = proj₁ ev , (proj₁ (proj₂ ev) , toFlo k (λ q → cv (proj₂ (proj₂ ev)) (suc q)))

    WΩ : ∀ {c} → GWᶜ c (fold 1 φ cv E (Ωˢ (suc k))) (ζ ++ Ωt θ)
    WΩ {c} {fl} {P} {π} F hP =
      limᵢWᶜ {φ = fl ⊔ (flE ⊔ φ)} {ps = π} {y = ψᵗ Ωᵗ (ζ ++ Ωt θ)} {ys = []} {ac = λ ev → cv (proj₂ (proj₂ ev)) zero}
             {H = λ x → fold 1 φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P} (cΩΩ ζ {y = ψᵗ θ []} {ys = []} cΩθ I) I ej
             (λ η x l → subst (λ u → LW[ c ] _ (π ++ u)) (sym (pen′ η))
                              (wkLWᶜ {φ = fl ⊔ (flE ⊔ flo k)} le (WV {φ = flo k} {cv = cvFlo k} (FP0→FP fpk) (inj₂ lv) l F hP)))

    OΩ : ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π → L0 (fold 1 φ cv E (Ωˢ (suc k)) P) (π ++ ψΩᵗ (ζ ++ Ωt θ))
    OΩ {fl} {P} {π} GP =
      limᵢ0ᴬ {φ = fl ⊔ (flE ⊔ φ)} {ps = π} {y = ψᵗ Ωᵗ (ζ ++ Ωt θ)} {ys = []} {ac = λ ev → cv (proj₂ (proj₂ ev)) zero}
             {H = λ x → fold 1 φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P} (cΩΩ ζ {y = ψᵗ θ []} {ys = []} cΩθ I) I ej
             (λ η x l → subst (λ u → LW _ (π ++ u)) (sym (pen′ η))
                              (wkLW {φ = fl ⊔ (flE ⊔ flo k)} le
                                    (LW0→LW (WV {φ = flo k} {cv = cvFlo k} (FP0→FP fpk) (inj₂ lv) l (FlrLab→[] (proj₁ GP)) (LW→LW[] (gWᴬ (proj₂ GP)))))))
             (λ η x l xx → L0≡π (fold 1 φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P) π (sym (pen′ η))
                                 (wkL0 {φ = fl ⊔ (flE ⊔ flo k)} {R = fold 1 (flo k) (cvFlo k) E (intoˢ (<→◃ zero) x) P} le
                                       (OV {φ = flo k} {cv = cvFlo k} fpk lv l xx GP)) ,
                           wkRᴬ le le (fold-≅1ᴬ {φ = flo k} {φ′ = flo k} {cv = cvFlo k} {cv′ = cvFlo k}
                                                 (∼ᶠ-refl flE) (gr1ᴴ GE) (≅ᴵ-refl k) (∼ᶠ-refl (flo k)) xx (∼ᶠ-refl fl) (gRᴬ (proj₂ GP))))

    FullΩ : FlrLabΩ φ (ζ ++ Ωt θ) → GA1ᴴ (fold 1 φ cv E (Ωˢ (suc k))) (ζ ++ Ωt θ)
    FullΩ flφ = ga1ᴴ (FlrLabΩ-⊔ (FlrLabΩ-ext (Ωt θ) (fl1ᴴ GE)) flφ) WΩ OΩ
                     (fold-≅1ᴬ (∼ᶠ-refl flE) (gr1ᴴ GE) (≅ᴵ-refl (suc k)) (∼ᶠ-refl φ) (Ωˢ-≅ᴬ (≅ᴵ-refl (suc k))))
```

## §3 深度 1 的 $\Omega_\Omega$ 闭包 (目标 0) 与 `TΩ2-target`

Uniform2 §6 `DepthOneΩ.vΩ` 的目标 0 部分, 底是 `GA1ᴴ`, 唯一前提是分支帧 $\psi_\Omega(\zeta+\Omega_\theta)$ 在目标 0 的标签 (`bV`). 第 0 点是第 1 层尾巴 $\Omega_1$ 的折叠 (§1 `Full₊`); 地板见证: 底的由 `GA0ᴬ` 的静态标签, 帧的由 `fl1ᴴ` (在一切 $\psi_\Omega(\zeta+b)$ 里出现, 这里 $b=\Omega_\theta$).

```agda
module ClosureO {flE} {E : A 1 flE} {ζ : T} (GE : GA1ᴴ E ζ)
                (bV : ∀ θ Y (hY : HS Y) → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π →
                      L0 (fold 1 (fk (toLevel Y hY)) (λ e q → e (suc q)) E (Ωˢ (toLevel Y hY)) P) (π ++ ψΩᵗ (ζ ++ Ωt θ))) where
  open Depth1ᴴ GE
  T₁ : A 1 (flE ⊔ fk zero)
  T₁ = fold 1 (fk zero) (λ e → e) E (Ωˢ (suc zero))
  Gη : (η : Ordᴵ) → A 1 (flE ⊔ fk η)
  Gη η = fold 1 (fk η) (λ e q → e (suc q)) E (Ωˢ η)
  F1 : GA1ᴴ T₁ (ζ ++ Ωt (natT 1))
  F1 = Full₊ FP0-z lw1 LΩ1 (Ωˢ-≅ᴬ (≅ᴵ-refl _))

  y₀ : PT
  y₀ = ψᵗ Ωᵗ (ζ ++ ΩΩ ∷ [])
  cs : cof (y₀ ∷ []) ≡ cΩ []
  cs = cΩΩ ζ {y = ΩΩ} {ys = []} refl I0
  pen : ∀ θ → fsT (y₀ ∷ []) θ ≡ ψᵗ Ωᵗ (ζ ++ Ωt θ) ∷ []
  pen θ = penΩ ζ {y = ΩΩ} {ys = []} refl I0 θ

  r : ∀ {fl L} → Ev L ((fl ⊔ flE) ⊔ fk zero) → Ev L (fl ⊔ (flE ⊔ fk zero))
  r ((u , v) , w) = u , (v , w)
  rη : ∀ {fl L η} → Ev L ((fl ⊔ flE) ⊔ fk η) → Ev L (fl ⊔ (flE ⊔ fk η))
  rη ((u , v) , w) = u , (v , w)
  r′ : ∀ {fl L} → Ev L (fl ⊔ (flE ⊔ fk zero)) → Ev L ((fl ⊔ flE) ⊔ fk zero)
  r′ (u , (v , w)) = (u , v) , w

  fwΩ : ∀ {fl π} → FlrLab fl π → FW ((fl ⊔ flE) ⊔ fk zero) π y₀ []
  fwΩ F (inr ink) = inj₁ z≅
  fwΩ F (inl (inl k)) with F k
  ... | inj₁ e = inj₁ e
  ... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → OccPre _ o)
  fwΩ {π = π} F (inl (inr k)) with fl1ᴴ GE k
  ... | inj₁ e = inj₁ e
  ... | inj₂ (w , Iw , kw , o) =
    inj₂ (w , Iw , kw , λ θ → subst (λ u → Occ w (π ++ u)) (sym (pen θ)) (OccΣ π (o (Ωt θ))))

  oΩ̂₁ : ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π → L0 (Ω̂A 1 E P) (π ++ ψΩᵗ (ζ ++ ΩΩ ∷ []))
  oΩ̂₁ {fl} {P} {π} GP =
    wkL0 {R = cloA 0 (wk 0 r (T₁ P)) (λ η → wk 0 rη (Gη η P))} r′
         (clo0 {φ = fl ⊔ flE} {ps = π} {y = y₀} {ys = []} {t = wk 0 r (T₁ P)} {g = λ η → wk 0 rη (Gη η P)} (fwΩ (proj₁ GP)) cs
                  (L0≡π (wk 0 r (T₁ P)) π (sym (pen (natT 1))) (wkL0 r (g01ᴴ F1 GP)))
                  (λ θ Y hY lY nθ lt → L0≡π (wk 0 rη (Gη (toLevel Y hY) P)) π (sym (pen θ)) (wkL0 rη (bV θ Y hY lY nθ lt GP))))
```

**`TΩ2-target` 有居留.** Relative 展望的条件定理类型: 由 `BranchΩᴬ` (只含标签部分) 推出统一树 $\psi_0(\Omega_\Omega^2)$ 的证书与标签. 证明三行: 取 `Ω̂A 0` 的好帧, 分支的目标 0 标签由 `bV₀`, 深度 0 取空前缀.

```agda
TΩ2-targetᴬ : TΩ2-target
TΩ2-targetᴬ Br ev z =
  wkL0 {φ = fz ⊔ (fk zero ⊔ fk zero)} {ψ = fz ⊔ (fk zero ⊔ (fk zero ⊔ fz))} {R = Ω̂A 1 (Ω̂A 0) ∅ᴿ}
       (λ {L} (ev′ : Ev L (fz ⊔ (fk zero ⊔ (fk zero ⊔ fz)))) → proj₁ ev′ , (proj₁ (proj₂ ev′) , proj₁ (proj₂ (proj₂ ev′))))
       (ClosureO.oΩ̂₁ goodΩ̂₀ᴴ (λ θ Y hY lY nθ lt GP → bV₀ Br θ Y hY lY nθ GP) ∅ᴿ-good) ev z tΩ2-NF
```

## §4 新标签: $\psi_0(\Omega_\Omega\cdot\Omega_3)$ 与第 2 层指数

```agda
tΩ₃ : T
tΩ₃ = ψΩ₀ (Ωt (natT 3))

tΩ₃-NF : NF₁ tΩ₃
tΩ₃-NF = tO-desc-NF (walkD d₀ (1 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ []) (refl , refl , refl , refl , refl , refl , refl , tt))

Tη₂-label : ∀ {t : Ordˢ two} {η} → LabL₊ two Ll t η → t ≅ᴬ t → NF₁ (ψΩ₀ η) →
            ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (tlᵀ (flo two) (cvFlo two) t)) ev z) (ψΩ₀ η)
Tη₂-label l ex nf ev z = Depth1ᴴ.O₊ goodΩ̂₀ᴴ FP0-1 lw2 l ex ∅ᴿ-good ev z nf

TΩ₃-label : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (tlᵀ (flo three) (cvFlo three) (Ωˢ three))) ev z) tΩ₃
TΩ₃-label ev z = Depth1ᴴ.ΩS.OΩ goodΩ̂₀ᴴ lw2 FP0-1 refl I₂ (≅ᴵ-refl two) ∅ᴿ-good ev z tΩ₃-NF
```

**读法.** `TΩ₃-label` 是此前的第一个未标记点 (Uniform2 §8、Relative §4 都把它列为停点). 它不需要 (a′) 的依目标见证 (第 2 层输入的地板 `fk 1` 总由 $\Omega_1$ 见证), 也不需要诚实前提 (第 $\le2$ 层尾巴的一切内部地板都 $\le$ `fk 1`); 需要的只是层对齐的互模拟与一般层号的 W 定理.

