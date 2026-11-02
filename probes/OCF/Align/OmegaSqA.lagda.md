# 层对齐的标签理论 (二): 深度 1 的折叠定理、$\psi_0(\Omega_\Omega\cdot\Omega_3)$ 与 $\psi_0(\Omega_\Omega^2)$ 的否定

> 接 [OmegaSqABase](OmegaSqABase.lagda.md). 本文: 深度 1 对第 $\le2$ 层一切带标签尾巴与 $\Omega_{k+1}$ ($k\le2$) 尾巴的折叠定理 (目标 0 部分), 第一个此前未标记的点 $\psi_0(\psi_\Omega(\Omega_3))=\psi_0(\Omega_\Omega\cdot\Omega_3)$ 的无条件标签, Relative 展望里 `TΩ2-target` 的证明, 以及它的前提 `BranchΩᴬ` 的**否定**: 统一形的树在 $\psi_0(\Omega_\Omega^2)$ 的目标 0 计值里确实读到 `up (self n)` 下未收紧的地板, 于是 $\psi_0(\Omega_\Omega^2)$ 的标签对 Uniform2 的树**为假**. 结论在 §6.
>
> 结论先说:
>
> 1. **深度 1 的折叠定理 (§1–§2).** 对第 $k\le2$ 层一切带标签、层对齐自互模拟的尾巴 (`Full₊`), 以及 $\Omega_{k+1}$ ($k\le2$, `ΩS.FullΩ`): 折叠是 `GA1ᴴ` 好帧. 地板 `fk 1` 由帧标签里的 $\Omega_1$ 见证, 所以第 2 层尾巴不需要任何诚实前提; AlignD/lowA 不再出现.
> 2. **新标签 (§4):** $\psi_0(\psi_\Omega(\Omega_3))=\psi_0(\Omega_\Omega\cdot\Omega_3)$ (`TΩ₃-label`), 以及第 2 层一切带标签指数 $\psi_0(\psi_\Omega(\eta))$ (`Tη₂-label`, 以 `NF₁` 为前提), 都对一切环境与证据成立.
> 3. **条件定理 (§3):** Relative 的 `TΩ2-target` 有居留 (`TΩ2-targetᴬ`): 由 `BranchΩᴬ` 的目标 0 部分推出 $\psi_0(\Omega_\Omega^2)$ 的标签; 互模拟与 W 部分都已是定理.
> 4. **否定 (§5).** `¬BranchΩᴬ`: 前提无居留. 在 $\psi_0(\Omega_\Omega^2)$ 的目标 0 计值里, 外层闭包的首个链点 $Y_1$ (标签 $\theta_1=\psi_0(\psi_\Omega(\Omega))$) 的层号 $L_1=\mathtt{toLevel}\,Y_1$ 是极限, 其分支 $\psi_\Omega(\Omega_{L_1})$ 沿路径 $[0,1,0,0,0]$ 到达 $\Omega_0=1$ 处的后继行, 地板仍是 `fk L₁` (`up (self n)` 不收紧), 第 2 份副本里 $\Omega_\Omega$ 弹栈的界是 $L_1+1$, 而该处标签 $\psi_0(\Omega_\Omega\cdot2)$ 的首个链点 $\psi_0(\Omega_\Omega+\Omega)<\theta_1$ 的层号 $\prec L_1$: 证书的支配字段不可满足. 进一步 **`¬TΩ2-label`**: 统一树 `ψᵀ (Ψ (Ψ ∅ᵀ))` 在任何环境下都没有 $\psi_0(\Omega_\Omega^2)$ 的证书与标签. 这推翻了 Relative §4 的分析 ("偏差不在目标 0 出现"): 它出现, 且正是链点层号的 fs-下降到 0 的位置. 修正在定义层: `fold` 的 `up (self n)` 子句须把地板换成 `flo (f n)`.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OmegaSqA where

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
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; _+ˢ_)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; []<; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fsT-c1)
open import OCF.Align.Bachmann using (gt→<)
open import OCF.Align.StandardOmega using (NF₁; NF₁-fsn; walkD; tO-desc-NF)
open import OCF.Align.Standard using (d₀)
open import OCF.Align.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Align.Stage2 using (Ωᵗ; tO)
open import OCF.Align.Stage2Label using (one⁰; Lab-oc)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.Decouple using (Idx; lvI)
open import OCF.Align.GoodLBase
open import OCF.Align.OmegaExpBase using (OccΣ; repW; ωW; snoc)
open import OCF.Align.OmegaExp using (ψΩ₀; tΩ1; tΩ1-NF)
open import OCF.Align.OmegaKBase using (tΩ2; tΩ2-NF)
open import OCF.Align.NonTightBase using (I₂)
open import OCF.Align.UniformS
open import OCF.Align.Uniform2Base
open import OCF.Align.Uniform2Depth1 using (wkLW; wkL0; c1Ω; cωΩ; cΩΩ; penΩ)
open import OCF.Align.Uniform2 using (LΩ1; nf-pΩ; TΩ1-label)
open import OCF.Align.RelativeBase using (Up; ≺≼; ≼≺; Up-≅; Up-≺; Ign; LW[_]; LW→LW[]; FW[_]; FlrLab[_]; FlrLab→[];
  s⊑s→≼; ≼→⊑; one; three)
open import OCF.Align.Relative
open import OCF.Align.OmegaSqABase
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
... | inj₁ e = inj₁ (inj₁ e)
... | inj₂ e = inj₂ e

FP0-fz : FP0 fz
FP0-fz ()

FP0-z : FP0 (fk zero)
FP0-z ink = inj₁ z≅

FP0-1 : FP0 (fk one)
FP0-1 ink = inj₂ (≅ᴵ-refl one)

FP0-flo : ∀ {k′} → suc k′ ⊑ᴵ two → FP0 (flo k′)
FP0-flo {k′ = zero} le ()
FP0-flo {k′ = suc k″} le ink with s⊑s→≼ le
... | inj₁ (via () zero)
... | inj₁ (via e (suc ()))
... | inj₂ (s≅ e) = inj₁ e
FP0-flo {k′ = lim f s} le ink with s⊑s→≼ le
... | inj₁ (via () zero)
... | inj₁ (via e (suc ()))
... | inj₂ ()

two-pred : ∀ {k′} → suc k′ ⊑ᴵ two → k′ ⊑ᴵ two
two-pred le = ⊑ᴵ-trans (≼→⊑ (s⊑s→≼ le)) (⊑-suc one)

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
  OV : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP0 φ → k ⊑ᴵ two → LabL t y → t ≅ᴬ t →
       ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π → L0 (fold 1 φ cv E t P) (π ++ ψΩᵗ (ζ ++ y))
  FullV : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP0 φ → k ⊑ᴵ two → LabL t y → t ≅ᴬ t →
          GA1ᴴ (fold 1 φ cv E t) (ζ ++ y)
  O₊ : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP0 φ → k ⊑ᴵ two → LabL₊ k Ll t y → t ≅ᴬ t →
       ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π → L0 (fold 1 φ cv E t P) (π ++ ψΩᵗ (ζ ++ y))
  Full₊ : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP0 φ → k ⊑ᴵ two → LabL₊ k Ll t y → t ≅ᴬ t →
          GA1ᴴ (fold 1 φ cv E t) (ζ ++ y)

  FullA {φ} {cv} {y = y} fp l ex =
    ga1ᴴ (FlrLabΩ-⊔ (FlrLabΩ-ext y (fl1ᴴ GE)) (FP→FlrLabΩ (FP0→FP fp))) (λ {c} → WA (FP0→FP fp) l) (OA fp l ex)
         (fold-≅1ᴬ (∼ᶠ-refl flE) (gr1ᴴ GE) z≅ (∼ᶠ-refl φ) ex)

  FullV {k = zero}    fp lv at ex = FullA fp (atomL at) ex
  FullV {k = suc _}   fp lv h  ex = Full₊ fp lv h ex
  FullV {k = lim _ _} fp lv h  ex = Full₊ fp lv h ex

  Full₊ {k = k} {φ} {cv} {y = y} fp lv l ex =
    ga1ᴴ (FlrLabΩ-⊔ (FlrLabΩ-ext y (fl1ᴴ GE)) (FP→FlrLabΩ (FP0→FP fp))) (λ {c} → W₊ (FP0→FP fp) (inj₂ lv) l) (O₊ fp lv l ex)
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
       (proj₁ ev , (proj₁ (proj₂ ev) , toFlo k′ (cv (proj₂ (proj₂ ev))))) p
  O₊ {k = lim f s} {cv = cv} fp lv (gu {r = self n} h) ex =
    OV {cv = λ e q → cv e (lim n q)} fp (⊑ᴵ-trans (Sim→⊑ᴵ (λ q → lim n q)) lv) h (u-reflᴬ (self n) ex)
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
  module ΩS {k} (lv : k ⊑ᴵ two) (fpk : FP0 (flo k)) {w ws} (c1θ : cof (w ∷ ws) ≡ c1) (I : Idx (pred (w ∷ ws)))
            (ej : k ≅ᴵ lvI I) {φ} {cv : ∀ {L} → Ev L φ → Simᴵ (suc k) L} where
    θ : T
    θ = w ∷ ws
    cΩθ : cof (Ωt θ) ≡ cΩ (pred θ)
    cΩθ = cong (E.cofψ0 θ) c1θ
    pen′ : ∀ η → fsT (ψᵗ Ωᵗ (ζ ++ Ωt θ) ∷ []) η ≡ ψᵗ Ωᵗ (ζ ++ η) ∷ []
    pen′ η = trans (penΩ ζ {y = ψᵗ θ []} {ys = []} cΩθ I η) (cong (λ u → ψᵗ Ωᵗ (ζ ++ u) ∷ []) (fsT-c1 θ (cof θ) c1θ η))

    le : ∀ {fl L} → Ev L (fl ⊔ (flE ⊔ φ)) → Ev L (fl ⊔ (flE ⊔ flo k))
    le ev = proj₁ ev , (proj₁ (proj₂ ev) , toFlo k (cv (proj₂ (proj₂ ev))))

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
  F1 = Full₊ FP0-z (⊑-suc one) LΩ1 (Ωˢ-≅ᴬ (≅ᴵ-refl _))

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
Tη₂-label l ex nf ev z = Depth1ᴴ.O₊ goodΩ̂₀ᴴ FP0-1 ⊑ᴵ-refl l ex ∅ᴿ-good ev z nf

TΩ₃-label : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (tlᵀ (flo three) (cvFlo three) (Ωˢ three))) ev z) tΩ₃
TΩ₃-label ev z = Depth1ᴴ.ΩS.OΩ goodΩ̂₀ᴴ ⊑ᴵ-refl FP0-1 refl I₂ (≅ᴵ-refl two) ∅ᴿ-good ev z tΩ₃-NF
```

**读法.** `TΩ₃-label` 是此前的第一个未标记点 (Uniform2 §8、Relative §4 都把它列为停点). 它不需要 (a′) 的依目标见证 (第 2 层输入的地板 `fk 1` 总由 $\Omega_1$ 见证), 也不需要诚实前提 (第 $\le2$ 层尾巴的一切内部地板都 $\le$ `fk 1`); 需要的只是层对齐的互模拟与一般层号的 W 定理.

## §5 否定: `BranchΩᴬ` 无居留, $\psi_0(\Omega_\Omega^2)$ 的标签对统一树为假

**位置.** $\psi_0(\Omega_\Omega^2)$ 在目标 0 处是外层闭包 $\psi_0(\psi_\Omega(\Omega_\Omega))$, 首个链点 $Y_1$ 带标签 $\theta_1=\psi_0(\psi_\Omega(\Omega_1))$ (`tΩ1`, 即 `fsn tΩ2 0`), 它的分支是 $\psi_\Omega(\Omega_{L_1})$ 的深度 1 折叠, $L_1=\mathtt{toLevel}\,Y_1$. $\theta_1$ 的共尾度是 $\omega$, 所以 $Y_1$ 是 `lim`, $L_1$ 是极限层号, $\Omega_{L_1}=\lim_n\mathtt{up}(\mathtt{self}\,n)\,\Omega_{L_1[n]}$, 折叠沿 `up (self n)` 保持地板 `fk L₁`. 记号侧 $\theta_1$ 沿基本列 $[0,1,0,0,0]$ 到达 $0$:
$\theta_1[0]=\psi_0(\psi_\Omega(1))$, $[1]\to\psi_0(\Omega_\Omega)$, $[0]\to\psi_0(\Omega)$, $[0]\to\psi_0(1)=\omega$, $[0]\to0$; 树侧 $Y_1$ 沿同一路径到达 `zero`, 层号到达 $0$, $\Omega_0=\mathtt{suc\ zero}$ 处是后继行: 第 $m$ 份副本是 $E^m(\varnothing)$ 带地板 `fk L₁`, 第 2 份的 $\Omega_\Omega$ 弹栈以 $L_1$ 为最大者, 界 $L_1+1$. 该处标签 $\psi_0(\psi_\Omega(\Omega_0))[2]=\psi_0(\Omega_\Omega\cdot2)$, 其首个链点 $\psi_0(\Omega_\Omega+\Omega)<\theta_1$, 层号 $\prec L_1$ (`Lab-oc`), 但证书的 `d₀` 要求 $L_1+1\sqsubseteq$ 该层号. 记号侧的计算 (全部 `refl`):

```agda
θ₁ : T
θ₁ = tΩ1

_ : fsn tΩ2 0 ≡ θ₁
_ = refl

labB : T                           -- the branch label at θ₁ (π = ζ = [])
labB = ψ₀ᵗ (ψΩᵗ (Ωt θ₁))

lab₅ : T                           -- after [0,1,0,0,0]: ψ₀(ψ_Ω(1))
lab₅ = fsn (fsn (fsn (fsn (fsn labB 0) 1) 0) 0) 0

_ : lab₅ ≡ ψΩ₀ (𝟏 ∷ [])
_ = refl
_ : fsn lab₅ 2 ≡ ψᵗ [] (ΩΩ ∷ ΩΩ ∷ []) ∷ []
_ = refl
_ : fsn (fsn lab₅ 2) 0 ≡ ψ₀ᵗ (ΩΩ ∷ Ωt (natT 1))
_ = refl
_ : fsn (fsn (fsn (fsn (fsn θ₁ 0) 1) 0) 0) 0 ≡ []
_ = refl
_ : fsn (fsn (fsn (fsn (fsn θ₁ 0) 1) 0) 0) 1 ≡ 𝟏 ∷ []
_ = refl
```

**树侧的两条通用反演.** `Lab₀-lim`: `lim` 的证书与标签给每个分支的; `closure-info`: 闭包 `ŝ c t₀ g` 的证书给第 0 点的证书 $G_0$、支配 $c\sqsubseteq\mathtt{toLevel}(\mathtt{force}\,G_0)$ 与它的标签 (标签来自输出证书 $Go_0$, 经 `forceᴸ-≅` 搬到 $G_0$, 要 $t_0$ 的自互模拟).

```agda
Lab₀-lim : ∀ {f : ℕ → Ordˢ zero} {t} → Lab₀ (Ord₊ˢ.lim f) t → ∀ n → Lab₀ (f n) (fsn t n)
Lab₀-lim (gl G st , l0 c ()) n
Lab₀-lim (gl G st , l1 c () l) n
Lab₀-lim (gl G st , lω c (l≅ k) h) n = G n , Lab-≅ (k n) (h n)

closure-info : ∀ {c t₀ g u} → toZ t₀ ≅ᶻ toZ t₀ → Lab₀ (Ord₊ˢ.ŝ c t₀ g) u →
               Σ (Goodᴸ (toZ t₀)) λ G₀ → (c ⊑ᴵ toLevel (forceᴸ _ G₀) (forceᴸ-HS _ G₀)) × Lab (forceᴸ _ G₀) (fsn u 0)
closure-info rt (gc γ′ G₀′ l₀′ dd₀ Gg′ lE′ dE′ Go₀′ Go′ mo₀′ mo′ , l0 c ())
closure-info rt (gc γ′ G₀′ l₀′ dd₀ Gg′ lE′ dE′ Go₀′ Go′ mo₀′ mo′ , l1 c () l)
closure-info rt (gc γ′ G₀′ l₀′ dd₀ Gg′ lE′ dE′ Go₀′ Go′ mo₀′ mo′ , lω c (l≅ k) h) =
  G₀′ , dd₀ , Lab-≅ (forceᴸ-≅ rt G₀′ Go₀′) (Lab-≅ (k 0) (h 0))
```

**弹栈的界.** 底的地板是 `(fz ⊔ (fk zero ⊔ fk L)) ⊔ fk zero` (第 1 份副本的类型地板加帧的 `fk zero`), 目标 0: 平凡项不改最大者 (`insT`), 项 $L\succ0$ 成为最大者 (`insL`), 界 $L+1$.

```agda
¬<0 : ∀ {a} → a <ᴵ zero → ⊥
¬<0 ()

insL : ∀ {ℓ φ L} (t : Top zero ℓ φ) (ek : Simᴵ (suc L) ℓ) → Mx t ≡ zero → zero ≺ᴵ L → Mx (ins t ek) ≡ L
insL t ek eq s with <ᴵ-dec (ek zero) (mx t)
... | injᵃ (via e r) = ⊥-elim (¬<0 (subst (_ <ᴵ_) eq r))
... | injᶜ e = ⊥-elim (≺0 s (subst (λ M → _ ≅ᴵ M) eq e))
... | injᵇ (via e r) = refl

MxL : ∀ {ℓ L} (x₁ : Ev ℓ fz) (x₂ : Ev ℓ (fk zero)) (x₃ : Ev ℓ (fk L)) (x₄ : Ev ℓ (fk zero)) (p : zero <ᴵ ℓ) → zero ≺ᴵ L →
      Mx (bound ((fz ⊔ (fk zero ⊔ fk L)) ⊔ fk zero) ((x₁ , (x₂ , x₃)) , x₄) p) ≡ L
MxL {L = L} x₁ x₂ x₃ x₄ p s =
  trans (insT (accT (top₀ p) (fz ⊔ (fk zero ⊔ fk L)) (x₁ , (x₂ , x₃))) x₄ z≅)
        (insL (ins (accT (top₀ p) fz x₁) x₂) x₃ (insT (accT (top₀ p) fz x₁) x₂ z≅) s)
```

**沿路径下降.** 对带标签 $\theta_1$ 的任意 $Y$ (不必是具体的树: 标签的反演给出 $Y$ 的 `lim`/`suc`/`zero` 结构), 分支树 $\psi_\Omega(\Omega_{\mathtt{toLevel}\,Y})$ 在目标 0、底 $\varnothing$ 处 (任意环境与证据) 没有带标签 $\psi_0(\psi_\Omega(\Omega_{\theta_1}))$ 的证书. 先由标签反演得 $0<L$ (`posL`, 路径 $[0,1,0,0,1]$ 到 `suc`), 再沿 $[0,1,0,0,0]$ 把假设的证书推到后继行的第 2 份副本.

```agda
module Refute (Y₀ : Ordᶜ zero) (hY₀ : HS Y₀) (lY₀ : Lab Y₀ θ₁) where
  L₀ : Ordᴵ
  L₀ = toLevel Y₀ hY₀

  pos₅ : ∀ Y hY → Lab Y (𝟏 ∷ []) → zero <ᴵ toLevel Y hY
  pos₅ Y hY (l0 () e)
  pos₅ (Ord₊.suc Y′) hY (l1 c (s≅ e) (l1 () e′ l))
  pos₅ (Ord₊.suc Y′) hY (l1 c (s≅ e) (lω () e′ h))
  pos₅ (Ord₊.suc Ord₊.zero) hY (l1 c (s≅ z≅) (l0 c′ z≅)) = zero
  pos₅ Y hY (lω () e h)
  pos₄ : ∀ Y hY → Lab Y (fsn (fsn (fsn (fsn θ₁ 0) 1) 0) 0) → zero <ᴵ toLevel Y hY
  pos₄ Y hY (l0 () e)
  pos₄ Y hY (l1 () e l)
  pos₄ (Ord₊.lim F) hY (lω c (l≅ k) h) = lim 1 (pos₅ (F 1) (hl₁ hY 1) (Lab-≅ (k 1) (h 1)))
  pos₃ : ∀ Y hY → Lab Y (fsn (fsn (fsn θ₁ 0) 1) 0) → zero <ᴵ toLevel Y hY
  pos₃ Y hY (l0 () e)
  pos₃ Y hY (l1 () e l)
  pos₃ (Ord₊.lim F) hY (lω c (l≅ k) h) = lim 0 (pos₄ (F 0) (hl₁ hY 0) (Lab-≅ (k 0) (h 0)))
  pos₂ : ∀ Y hY → Lab Y (fsn (fsn θ₁ 0) 1) → zero <ᴵ toLevel Y hY
  pos₂ Y hY (l0 () e)
  pos₂ Y hY (l1 () e l)
  pos₂ (Ord₊.lim F) hY (lω c (l≅ k) h) = lim 0 (pos₃ (F 0) (hl₁ hY 0) (Lab-≅ (k 0) (h 0)))
  pos₁ : ∀ Y hY → Lab Y (fsn θ₁ 0) → zero <ᴵ toLevel Y hY
  pos₁ Y hY (l0 () e)
  pos₁ Y hY (l1 () e l)
  pos₁ (Ord₊.lim F) hY (lω c (l≅ k) h) = lim 1 (pos₂ (F 1) (hl₁ hY 1) (Lab-≅ (k 1) (h 1)))
  pos₀ : ∀ Y hY → Lab Y θ₁ → zero <ᴵ toLevel Y hY
  pos₀ Y hY (l0 () e)
  pos₀ Y hY (l1 () e l)
  pos₀ (Ord₊.lim F) hY (lω c (l≅ k) h) = lim 0 (pos₁ (F 0) (hl₁ hY 0) (Lab-≅ (k 0) (h 0)))

  pos : zero <ᴵ L₀
  pos = pos₀ Y₀ hY₀ lY₀

  Hyp : ∀ ℓ (σ₁ : Simᴵ (suc zero) ℓ) (σ₂ : Simᴵ (suc L₀) ℓ) (p : zero <ᴵ ℓ)
        (Y : Ordᶜ zero) (hY : HS Y) (cv : ∀ {L} → Ev L (fk L₀) → Simᴵ (toLevel Y hY) L) (u : T) → Set
  Hyp ℓ σ₁ σ₂ p Y hY cv u = Lab₀ (fold 1 (fk L₀) cv (Ω̂A 0) (Ωˢ (toLevel Y hY)) ∅ᴿ (tt , (σ₁ , σ₂)) p) u

  -- the leaf: Ω₀ = suc zero under floor fk L₀; the 2nd copy pops with bound L₀+1
  leaf : ∀ ℓ (σ₁ : Simᴵ (suc zero) ℓ) (σ₂ : Simᴵ (suc L₀) ℓ) (p : zero <ᴵ ℓ) Y hY → Lab Y [] →
         (cv : ∀ {L} → Ev L (fk L₀) → Simᴵ (toLevel Y hY) L) → Hyp ℓ σ₁ σ₂ p Y hY cv lab₅ → ⊥
  leaf ℓ σ₁ σ₂ p Y hY (l1 () e l) cv H
  leaf ℓ σ₁ σ₂ p Y hY (lω () e h) cv H
  leaf ℓ σ₁ σ₂ p Ord₊.zero hY (l0 c z≅) cv H = ≺ᴵ-irrefl (≺ᴵ-trans L≺Z Z≺L)
    where
    Q : Run (fz ⊔ (fk zero ⊔ fk L₀))
    Q = wk 0 (λ { (u , v) → u , proj₁ v }) (Ω̂A 0 ∅ᴿ)
    HQ : Q ≈ᴬ Q
    HQ = wkRᴬ (λ { (u , v) → u , proj₁ v }) (λ { (u , v) → u , proj₁ v }) (selfΩ̂0ᴬ fz∼ ∅ᴿ-ᴬ)
    ev₁ : Ev ℓ ((fz ⊔ (fk zero ⊔ fk L₀)) ⊔ fk zero)
    ev₁ = (tt , (σ₁ , σ₂)) , σ₁
    t₀′ : Ordˢ zero
    t₀′ = fold 0 (fk zero) (λ e → e) Q (Ωˢ (suc zero)) ev₁ p
    rt : toZ t₀′ ≅ᶻ toZ t₀′
    rt = toZ-≅ (≅ᴬ→≅ˢ₀ (fold-≅0ᴬ {P = Q} {P′ = Q} HQ (Ωˢ-≅ᴬ (≅ᴵ-refl (suc zero))) ev₁ p ev₁ p z≅))
    H₂ : Lab₀ (repA 0 ∅ᴿ (fold 1 (fk L₀) cv (Ω̂A 0) Ord₊ˢ.zero) 2 (tt , (σ₁ , σ₂)) p) (fsn lab₅ 2)
    H₂ = Lab₀-lim H 2
    info = closure-info {c = suc (Mx (bound ((fz ⊔ (fk zero ⊔ fk L₀)) ⊔ fk zero) ev₁ p))} {t₀ = t₀′} rt H₂
    G₀ = proj₁ info
    Zc : Ordᶜ zero
    Zc = forceᴸ _ G₀
    hZ : HS Zc
    hZ = forceᴸ-HS _ G₀
    lZ : Lab Zc (ψ₀ᵗ (ΩΩ ∷ Ωt (natT 1)))
    lZ = proj₂ (proj₂ info)
    Z≺L : toLevel Zc hZ ≺ᴵ L₀
    Z≺L = toLevel-≺ hZ hY₀ (Lab-oc lY₀ tΩ1-NF lZ nf-pΩ (gt→< θ₁ _ refl))
    L≺Z : L₀ ≺ᴵ toLevel Zc hZ
    L≺Z = ≺ᴵ-respˡ (≅ᴵ-sym (subst (λ M → M ≅ᴵ L₀) (sym (MxL tt σ₁ σ₂ σ₁ p (via z≅ pos))) (≅ᴵ-refl L₀)))
                   (sim (proj₁ (proj₂ info)) zero)

  step₄ : ∀ ℓ (σ₁ : Simᴵ (suc zero) ℓ) (σ₂ : Simᴵ (suc L₀) ℓ) (p : zero <ᴵ ℓ) Y hY → Lab Y (fsn (fsn (fsn (fsn θ₁ 0) 1) 0) 0) → (cv : ∀ {L} → Ev L (fk L₀) → Simᴵ (toLevel Y hY) L) →
          Hyp ℓ σ₁ σ₂ p Y hY cv (fsn (fsn (fsn (fsn labB 0) 1) 0) 0) → ⊥
  step₄ ℓ σ₁ σ₂ p Y hY (l0 () e) cv H
  step₄ ℓ σ₁ σ₂ p Y hY (l1 () e l) cv H
  step₄ ℓ σ₁ σ₂ p (Ord₊.lim F) hY (lω c (l≅ k) h) cv H =
    leaf ℓ σ₁ σ₂ p (F 0) (hl₁ hY 0) (Lab-≅ (k 0) (h 0)) (λ e q → cv e (lim 0 q)) (Lab₀-lim H 0)

  step₃ : ∀ ℓ (σ₁ : Simᴵ (suc zero) ℓ) (σ₂ : Simᴵ (suc L₀) ℓ) (p : zero <ᴵ ℓ) Y hY → Lab Y (fsn (fsn (fsn θ₁ 0) 1) 0) → (cv : ∀ {L} → Ev L (fk L₀) → Simᴵ (toLevel Y hY) L) →
          Hyp ℓ σ₁ σ₂ p Y hY cv (fsn (fsn (fsn labB 0) 1) 0) → ⊥
  step₃ ℓ σ₁ σ₂ p Y hY (l0 () e) cv H
  step₃ ℓ σ₁ σ₂ p Y hY (l1 () e l) cv H
  step₃ ℓ σ₁ σ₂ p (Ord₊.lim F) hY (lω c (l≅ k) h) cv H =
    step₄ ℓ σ₁ σ₂ p (F 0) (hl₁ hY 0) (Lab-≅ (k 0) (h 0)) (λ e q → cv e (lim 0 q)) (Lab₀-lim H 0)

  step₂ : ∀ ℓ (σ₁ : Simᴵ (suc zero) ℓ) (σ₂ : Simᴵ (suc L₀) ℓ) (p : zero <ᴵ ℓ) Y hY → Lab Y (fsn (fsn θ₁ 0) 1) → (cv : ∀ {L} → Ev L (fk L₀) → Simᴵ (toLevel Y hY) L) →
          Hyp ℓ σ₁ σ₂ p Y hY cv (fsn (fsn labB 0) 1) → ⊥
  step₂ ℓ σ₁ σ₂ p Y hY (l0 () e) cv H
  step₂ ℓ σ₁ σ₂ p Y hY (l1 () e l) cv H
  step₂ ℓ σ₁ σ₂ p (Ord₊.lim F) hY (lω c (l≅ k) h) cv H =
    step₃ ℓ σ₁ σ₂ p (F 0) (hl₁ hY 0) (Lab-≅ (k 0) (h 0)) (λ e q → cv e (lim 0 q)) (Lab₀-lim H 0)

  step₁ : ∀ ℓ (σ₁ : Simᴵ (suc zero) ℓ) (σ₂ : Simᴵ (suc L₀) ℓ) (p : zero <ᴵ ℓ) Y hY → Lab Y (fsn θ₁ 0) → (cv : ∀ {L} → Ev L (fk L₀) → Simᴵ (toLevel Y hY) L) →
          Hyp ℓ σ₁ σ₂ p Y hY cv (fsn labB 0) → ⊥
  step₁ ℓ σ₁ σ₂ p Y hY (l0 () e) cv H
  step₁ ℓ σ₁ σ₂ p Y hY (l1 () e l) cv H
  step₁ ℓ σ₁ σ₂ p (Ord₊.lim F) hY (lω c (l≅ k) h) cv H =
    step₂ ℓ σ₁ σ₂ p (F 1) (hl₁ hY 1) (Lab-≅ (k 1) (h 1)) (λ e q → cv e (lim 1 q)) (Lab₀-lim H 1)

  step₀ : ∀ ℓ (σ₁ : Simᴵ (suc zero) ℓ) (σ₂ : Simᴵ (suc L₀) ℓ) (p : zero <ᴵ ℓ) Y hY → Lab Y θ₁ → (cv : ∀ {L} → Ev L (fk L₀) → Simᴵ (toLevel Y hY) L) →
          Hyp ℓ σ₁ σ₂ p Y hY cv labB → ⊥
  step₀ ℓ σ₁ σ₂ p Y hY (l0 () e) cv H
  step₀ ℓ σ₁ σ₂ p Y hY (l1 () e l) cv H
  step₀ ℓ σ₁ σ₂ p (Ord₊.lim F) hY (lω c (l≅ k) h) cv H =
    step₁ ℓ σ₁ σ₂ p (F 0) (hl₁ hY 0) (Lab-≅ (k 0) (h 0)) (λ e q → cv e (lim 0 q)) (Lab₀-lim H 0)

  refute : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ (fk zero ⊔ fk L₀))) (p : zero <ᴵ ℓ) → Lab₀ (Branch L₀ ∅ᴿ ev p) labB → ⊥
  refute {ℓ} ev p H = step₀ ℓ (proj₁ (proj₂ ev)) (proj₂ (proj₂ ev)) p Y₀ hY₀ lY₀ (λ e q → e (suc q)) H
```

**`BranchΩᴬ` 无居留.** 取 $\theta=\theta_1$, $Y$ 为 `TΩ1-label` 给出的树 (任何带标签 $\theta_1$ 的树都行), 底 $\varnothing$, 环境 $L_1+1$.

```agda
Y₁-pack : Σ (Ordᶜ zero) λ Y → Σ (HS Y) λ hY → Lab Y θ₁
Y₁-pack = forceᴸ _ (proj₁ TL₁) , forceᴸ-HS _ (proj₁ TL₁) , proj₂ TL₁
  where TL₁ = TΩ1-label {ℓ = suc zero} (tt , ((λ q → q) , (λ q → q))) zero

¬BranchΩᴬ : BranchΩᴬ → ⊥
¬BranchΩᴬ Br = refute (tt , (σ₁ , (λ q → q))) (suc pos) (bV₀ Br θ₁ Y₁ hY₁ lY₁ tΩ1-NF ∅ᴿ-good _ (suc pos) nfB)
  where
  Y₁ = proj₁ Y₁-pack
  hY₁ = proj₁ (proj₂ Y₁-pack)
  lY₁ = proj₂ (proj₂ Y₁-pack)
  open Refute Y₁ hY₁ lY₁
  σ₁ : Simᴵ (suc zero) (suc L₀)
  σ₁ zero = suc pos
  σ₁ (suc ())
  nfB : NF₁ labB
  nfB = NF₁-fsn tΩ2-NF refl 1
```

**统一树本身.** 不只是 `BranchΩᴬ`: 对任意环境与证据, 统一树 `ψᵀ (Ψ (Ψ ∅ᵀ))` 都没有带标签 $\psi_0(\Omega_\Omega^2)$ 的证书. 从假设的证书读出外层闭包的首个链点 $Y_1$ (标签 $\theta_1$)、它的层号处的分支的证书与标签 (`closure-branch`: `gc` 的 `Go 0` 与外层 `lω` 的第 1 项), 再交给 `Refute`.

```agda
closure-branch : ∀ {c t₀ g u} → toZ t₀ ≅ᶻ toZ t₀ → Lab₀ (Ord₊ˢ.ŝ c t₀ g) u →
                 Σ (Goodᴸ (toZ t₀)) λ G₀ → Lab (forceᴸ _ G₀) (fsn u 0) ×
                 Σ (c ⊑ᴵ toLevel (forceᴸ _ G₀) (forceᴸ-HS _ G₀)) λ e →
                 Lab₀ (g (toLevel (forceᴸ _ G₀) (forceᴸ-HS _ G₀)) e) (fsn u 1)
closure-branch rt (gc γ′ G₀′ l₀′ dd₀ Gg′ lE′ dE′ Go₀′ Go′ mo₀′ mo′ , l0 c ())
closure-branch rt (gc γ′ G₀′ l₀′ dd₀ Gg′ lE′ dE′ Go₀′ Go′ mo₀′ mo′ , l1 c () l)
closure-branch rt (gc γ′ G₀′ l₀′ dd₀ Gg′ lE′ dE′ Go₀′ Go′ mo₀′ mo′ , lω c (l≅ k) h) =
  G₀′ , Lab-≅ (forceᴸ-≅ rt G₀′ Go₀′) (Lab-≅ (k 0) (h 0)) , dd₀ , (Go′ 0 , Lab-≅ (k 1) (h 1))

_ : fsn tΩ2 1 ≡ labB
_ = refl

¬TΩ2-label : (∀ {ℓ} (ev : Ev ℓ (fz ⊔ (fk zero ⊔ (fk zero ⊔ fz)))) (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (Ψ ∅ᵀ)) ev z) tΩ2) → ⊥
¬TΩ2-label lab = Refute.refute Y₁ hY₁ lY₁ _ _ (proj₂ (proj₂ (proj₂ info)))
  where
  evT : Ev (suc zero) (fz ⊔ (fk zero ⊔ fk zero))
  evT = tt , ((λ q → q) , (λ q → q))
  F1 : GA1ᴴ (fold 1 (fk zero) (λ e → e) (Ω̂A 0) (Ωˢ (suc zero))) ([] ++ Ωt (natT 1))
  F1 = Depth1ᴴ.Full₊ goodΩ̂₀ᴴ FP0-z (⊑-suc one) LΩ1 (Ωˢ-≅ᴬ (≅ᴵ-refl _))
  t₀ : Ordˢ zero
  t₀ = fold 1 (fk zero) (λ e → e) (Ω̂A 0) (Ωˢ (suc zero)) ∅ᴿ evT zero
  rt : toZ t₀ ≅ᶻ toZ t₀
  rt = toZ-≅ (≅ᴬ→≅ˢ₀ (gRᴬ (gv1ᴴ F1 ∅ᴿ-good) evT zero evT zero z≅))
  info = closure-branch {t₀ = t₀} rt (lab {ℓ = suc zero} (tt , ((λ q → q) , ((λ q → q) , tt))) zero)
  Y₁ = forceᴸ _ (proj₁ info)
  hY₁ = forceᴸ-HS _ (proj₁ info)
  lY₁ : Lab Y₁ θ₁
  lY₁ = proj₁ (proj₂ info)
```

**读法.** 两个否定都不依赖具体的树: `Refute` 只用标签的反演 (带标签 $\theta_1$ 的任何树沿 $[0,1,0,0,0]$ 都到 `zero`, 沿 $[0,1,0,0,1]$ 到 `suc`), 统一折叠在 `up (self n)` 处保持地板这一条定义, 与 `Goodᴸ.gc` 的支配字段 `d₀`. Relative §4 的分析 ("链点的树沿第 0 项下降最终到 `suc zero`, 所以极限层分支里不出现地板为 `fk η` 的后继") 错在第二步: $\theta_1$ 沿第 0 项下降经过 $\psi_0(\psi_\Omega(1))$, 它的第 1 项是 $\psi_0(\Omega_\Omega)$, 再沿第 0 项到 $\psi_0(\Omega)$、$\psi_0(1)=\omega$、$0$: 一切 $\psi_0(\alpha+1)$ 的第 0 项都是 $0$, 所以链点层号的 fs-下降**必然**经过 $0$, 而 $\Omega_0=\mathtt{suc\ zero}$ 处的后继行正是读地板的地方. 这不是 (a′)/(b′) 或诚实前提能修的: 树在该处的闭包界 $L_1+1$ 比标签所指的链点层号大, 证书的类型无居留.

## §6 结论与边界

**任务 1 (标签理论移到 $\cong^\mathsf A$ 上).** 做成. 深度 0: `tlGRᴬ`、`goodΩ̂0ᴬ` (OmegaSqABase §2); 深度 1: `GA1ᴴ`, 一般层号的 W 定理 `W₊` (OmegaSqABase §4), 第 $\le2$ 层尾巴与 $\Omega_{k+1}$ ($k\le2$) 的 `Full₊`/`FullΩ` (本文 §1–§2). Relative 展望的 `GRᴬ`/`GA0ᴬ`/`GA1ᴬ` 都有居留 (`tlGRᴬ`、`∅ᴿ-good`、`goodΩ̂₀ᴬ`), `bR` 是定理 (Relative `bRᴬ`), `AlignD`/`lowA`/`alΩ₂` 不再出现.

**任务 2 (一般层号的深度 1 定理).** W 部分对**一切层号**成立 (`W₊`, 前提是地板策略与层号条件, 不需要诚实前提); 目标 0 部分对第 $\le2$ 层与 $\Omega_{k+1}$ ($k\le2$) 成立. 第 $\ge3$ 层尾巴的目标 0 部分 (地板 `fk 2` 起) 需要链点标签的首项见证 (RelativeBase `FL-head`) 沿输出推导遗传, 本文未做; 但由任务 4 的否定, 它对现在的树族已无意义 (见下).

**任务 3 (决定性检验).**

| 点 | 状态 |
|---|---|
| $\psi_0(\psi_\Omega(\Omega_3))=\psi_0(\Omega_\Omega\cdot\Omega_3)$ | **无条件定理** `TΩ₃-label` (首个此前未标记的点) |
| $\psi_0(\psi_\Omega(\eta))$, 第 2 层一切带标签 $\eta$ | **无条件定理** `Tη₂-label` (前提 `NF₁`) |
| $\psi_0(\psi_\Omega(\Omega_4))$ | 未得; 需要第 3 层链点的目标 0 定理 (地板 `fk 2` 的见证) |
| $\psi_0(\Omega_\Omega^2)$, 条件形式 | **`TΩ2-targetᴬ : TΩ2-target`** (Relative 展望的类型有居留) |
| $\psi_0(\Omega_\Omega^2)$, 无条件 | **假**: `¬BranchΩᴬ` (前提无居留), `¬TΩ2-label` (统一树在任何环境下都没有证书与标签) |

**任务 4 (`up (self n)` 偏差).** 否定: 它**出现**在 $\psi_0(\Omega_\Omega^2)$ 的目标 0 计值里, 位置是外层闭包首个链点 $Y_1$ 的分支 $\psi_\Omega(\Omega_{L_1})$ 沿 $[0,1,0,0,0]$ 的 $\Omega_0$ 后继行的第 2 份副本, 界 $L_1+1$, 标签 $\psi_0(\Omega_\Omega\cdot2)$ 的首个链点 $\psi_0(\Omega_\Omega+\Omega)<\theta_1$ (`gt→< θ₁ _ refl`). 所以 Uniform2 的树族对 $\psi_0(\Omega_\Omega^2)$ **不是**正确的定义; 这一轮的标签理论 (任务 1–3) 对不经过极限层分支的点仍然有效 ($\Omega_3$、第 2 层指数).

**修正的方向 (定义层, 纸面).** `fold` 的 `up (self n)` 子句须把地板换成 "第 $f\,n$ 层的紧地板". `flo (f n)` 的字面证据 `Simᴵ (suc (pred (f n))) ℓ` 在 $f\,n$ 为后继或 $0$ 时可从 `Simᴵ (lim f s) ℓ` 造出 (`λ q → σ (lim n q)`), 在 $f\,n$ 为极限时造不出 (`Simᴵ (suc (lim g t)) ℓ` 要 $\lim g<\ell$ 的字面见证, 而退化序列只给 $\sqsubseteq$). 所以地板语法要加一种 "严格在 $K$ 之下" 的项 `fb K` (证据 `Simᴵ K ℓ`, 弹栈时最大者取 $\max(i+1,K)$ 而不是 $K+1$), `flo` 对极限层取 `fb (lim g t)`; `Top`/`ins`/`bound-≅`/`FlrLab`/`FW` 都要加这一项的子句 (一个新构造子, 每处一条). 之后 `up (self n)` 处地板紧, 本文的 W/O 定理对极限层分支的后继行只需 `fb` 的策略条款 ($K\preceq c$ 或 $K\cong$ 当前层号时可忽略). 这是下一轮的定义修订; 标签理论 (本文与 OmegaSqABase) 的结构不变.

**字面与模 $\cong$.** `refl`: §5 的记号侧计算 (十条), `fsn tΩ2 1 ≡ labB`. 其余是对一切环境与证据的定理或否定.

**边界.** 不改 `src/`、`archive/` 与任何已有文件; README 未更新. 本文没有名为 `TΩ2-label` 的定理, 且证明了它不可能有 (对现在的树族).

**工程注记.**

1. `u-reflᴬ` 直接对 `uᴬ (us .n) d` 匹配在 `--without-K` 下失败 (`Cannot eliminate reflexive equation n = n`): 改为先证两侧 `r r′` 任意的 `u-invᴬ`, 忽略 `UpK` 见证.
2. `wkL0` 不给出 `{R = …}` 时报 `[UnsolvedConstraints]` (Uniform2Base §12 第 1 条的同一现象), 一律显式给出.
3. 以 `Simᴵ` 为类型的参数 (`σ₁ σ₂`) 在 `∀ ℓ σ₁ σ₂ …` 里不标类型时报 `[MetaCannotDependOn]` (隐式函数类型下的 η 展开让 ℓ 的元变量逃出作用域); 一律标出 `(σ₁ : Simᴵ (suc zero) ℓ)` 并把 ℓ 作显式参数.
4. `where` 里的局部名 `Z`、`TL`、`d₀` 与导入的 `Prefix.Z`、`Relative.TL`、`Standard.d₀` 冲突 (`[ClashingDefinition]`/`[ConstructorPatternInWrongDatatype]`), 改名.
