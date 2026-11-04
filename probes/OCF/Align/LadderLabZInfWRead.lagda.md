> **机械克隆, 验收用.** 由 `LadderInfWRead` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆, 验收用.** 由 `LadderInfRead` 经 `Survey/scripts/laddernf/mk_infw.py` 复制, 只改导入, 落在标签阶梯的世界. 见 [LadderInfAccept](LadderInfAccept.lagda.md).

# 高度抽象: 读数 $\succeq 1$, $\succ 1$

> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 对高度结构 `HtS` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNFRead](LadderNFRead.lagda.md) 生成, 下面的说明是原文件的. `read1ᵀ`: 尾巴 $\sqsupseteq 1$ 推出层号 $\sqsupseteq 1$, 对一切上下文. `Twᵀ`: 层号 $\succ 1$. 与 `OCF.Free.Good`, `OCF.Free.Omega` 同形, `pι` 之下转到 `One`. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderLabZInfWRead (𝕊 : HtS) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Align.Level
open import OCF.Align.LadderLabZNFWPrefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ)
open import OCF.Align.LadderLabZNFWEq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; toZ-≅; addˢ-≅; self-trˢ; self-tr⁻ˢ)
open import OCF.Align.LadderLabZNFWFloor using (Flr; fz; fk; _⊔_; Ev; InF; inl; inr; ink; inb; Dem; _∼ᶠ_; ∼ᶠ-refl; flo; cvFlo; toFlo)
open import OCF.Align.LadderLabZNFWForce using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Align.LadderLabZNFWAux using (one⁰)
open import OCF.Align.LadderLabZInfWTree 𝕊
open import OCF.Align.LadderLabZInfWRel 𝕊
open import OCF.Align.LadderLabZInfWCx 𝕊
open import OCF.Align.LadderLabZInfWRules 𝕊
open import OCF.Align.LadderLabZInfWRules2 𝕊
open import OCF.Align.LadderLabZInfWRules3 𝕊
open import OCF.Align.LadderLabZInfWStrict 𝕊
open import OCF.Align.LadderLabZInfWStrict2 𝕊
open import OCF.Align.LadderLabZInfWClass 𝕊
open import OCF.Align.LadderLabZInfWGood 𝕊

oneH : (H : Goodᴺ (Z.suc Z.zero)) {X : Ordᶜ zero} → forceᴺ _ H ⊑⁰ X → suc zero ⊑⁰ X
oneH (gs gz) h = h

read1  : ∀ {k} (O : Obs k) → Ctx O → (t : Ordˢ k) → t ≅ˢ t → 𝟏 ⊑ᴱ t → (G : Goodᴺ (toZ (run O t))) → suc zero ⊑ᴵ lvG G
read1ᵀ : ∀ {m c φ χ} (C : Cx m c φ χ) → Ctxᶜ C → (t : Q m c φ χ) → Rq m c c t t → 𝟏q c ⊑ᵀ t → (G : Goodᴺ (toZ (runᶜ C t))) → suc zero ⊑ᴵ lvG G
read1ᴺ : ∀ {m c φ χ} (C : Cx m c φ χ) → Nd C → Ctxᶜ C → (t : Q m c φ χ) → Rq m c c t t → One t → (G : Goodᴺ (toZ (runᶜ C t))) → suc zero ⊑ᴵ lvG G
read1 idO c t et one G = toLevel-⊑ (hs hz) (forceᴺ-HS _ G) (oneH (proj₁ (one idO G)) (proj₂ (one idO G)))
read1 (tlo {k = k} C) c t et one G = read1ᵀ C c (tl (flo k) (cvFlo k) t) (R-tl et) (tl-cong one) G
read1 (addo O a σ) (afl e₁ one₁ _ , c) t et one G = read1 O c _ (addˢ-≅ (≅ᴵ-refl _) e₁ et) (add-floorᴱ {σ = σ} t one₁ et) G
read1 (tro O e) c t et one G = read1 O c _ (self-trˢ e et) (fl-tr e (s≅ z≅ z≅) one) G
read1 (tr⁻o O e) c t et one G = read1 O c _ (self-tr⁻ˢ e et) (fl-tr⁻ e (s≅ z≅ z≅) one) G
read1ᵀ (top {i = i} O ev p ok e) c t rt one G = read1 O c (ψ̄ᵠ ok e t ev p) (R→≈ᵠ rt ok e ok e ev p ev p (≅ᴵ-refl i)) (⊑ᴱ-trans (Ω1ᴱ i) (F0ᵀ rt)) G
read1ᵀ {m} {χ = χ} (pa {a = a} {b = b} W C) (w , c) t rt one G = read1ᵀ C c (W ⊞ t) (R-⊞ (∼ᶠ-refl a) (Sim∼-refl b) (WFl.rW w) rt) (B1ᵀ rt (WFl.oneW w)) G
read1ᵀ {m} (pψ {t = t₀} q C) c t rt one G = read1ᵀ C c (ψᵠ q t) (R-ψᵠ q q (≅ᴵ-refl _) rt) (P0ᵀ {q = q} rt (𝟏⊑Ω̇ m t₀)) G
read1ᵀ (pΨ {H = H} {t = t₀} qH ok e p C) c t rt one G = read1ᵀ C c (Ψ qH ok e p t) (R-Ψ qH ok e p ok e p (≅ᴵ-refl _) rt) (H0ᵀ rt (𝟏⊑Ω̇ H t₀)) G
read1ᵀ (pι q C) (n , c) t rt one G = read1ᴺ C n c (ι q t) (R-ι q q rt) (One-ι q (⊑→One one)) G
read1ᵀ (pD {q = qd} C) c t rt one G = read1ᵀ C c (ι↓ qd t) (R-ι↓ qd (≅ᴵ-refl _) rt) (𝟏-D {qd = qd} one) G
read1ᵀ (ptr e C) c t rt one G = read1ᵀ C c (trQ e t) (R-tr₂ e e rt) (𝟏-tr e one) G
read1ᵀ (ptr⁻ e C) c t rt one G = read1ᵀ C c (tr⁻Q e t) (R-tr⁻₂ e e rt) (𝟏-tr⁻ e one) G
read1ᴺ (top {i = i} O ev p ok e) n c t rt one G = read1 O c (ψ̄ᵠ ok e t ev p) (R→≈ᵠ rt ok e ok e ev p ev p (≅ᴵ-refl i)) (⊑ᴱ-trans (Ω1ᴱ i) (F0ᵀ rt)) G
read1ᴺ (pa {a = a} {b = b} W C) n (w , c) t rt one G = read1ᵀ C c (W ⊞ t) (R-⊞ (∼ᶠ-refl a) (Sim∼-refl b) (WFl.rW w) rt) (B1ᵀ rt (WFl.oneW w)) G
read1ᴺ {m} (pψ {t = t₀} q C) n c t rt one G = read1ᵀ C c (ψᵠ q t) (R-ψᵠ q q (≅ᴵ-refl _) rt) (P0ᵀ {q = q} rt (𝟏⊑Ω̇ m t₀)) G
read1ᴺ (pΨ {H = H} {t = t₀} qH ok e p C) n c t rt one G = read1ᵀ C c (Ψ qH ok e p t) (R-Ψ qH ok e p ok e p (≅ᴵ-refl _) rt) (H0ᵀ rt (𝟏⊑Ω̇ H t₀)) G
read1ᴺ (pι q C) n (n₁ , c) t rt one G = read1ᴺ C n₁ c (ι q t) (R-ι q q rt) (One-ι q one) G
read1ᴺ (pD C) () c t rt one G
read1ᴺ (ptr e C) n c t rt one G = read1ᴺ C n c (trQ e t) (R-tr₂ e e rt) (One-tr e one) G
read1ᴺ (ptr⁻ e C) n c t rt one G = read1ᴺ C n c (tr⁻Q e t) (R-tr⁻₂ e e rt) (One-tr⁻ e one) G

𝟐 : Ordˢ zero
𝟐 = Ord₊ˢ.suc 𝟏

𝟏⊑𝟐 : 𝟏 ⊑ᴱ 𝟐
𝟏⊑𝟐 = suc-rᴱ (≅→⊑ᴱ (s≅ z≅ z≅))

h2N : (G : Goodᴺ (Z.suc (Z.suc Z.zero))) → one⁰ ≺ forceᴺ _ G
h2N (gs (gs gz)) = ≺z (s≅ z≅)

Twᵛ : ∀ {k} (O : Obs k) → NZ k → Ctx O → ∀ {y : Ordˢ k} → y ≅ˢ y → 𝟏 ⊑ᴱ y → (G : Goodᴺ (toZ (run O y))) → one⁰ ≺ forceᴺ _ G
V₀ : (O : Obs zero) → Ctx O → ∀ {y : Ordˢ zero} → y ≅ˢ y → 𝟐 ⊑ᴱ y → (G : Goodᴺ (toZ (run O y))) → one⁰ ≺ forceᴺ _ G
Twᵀ : ∀ {m c φ χ} (C : Cx m c φ χ) → Ctxᶜ C → ∀ {y : Q m c φ χ} → Rq m c c y y → 𝟏q c ⊑ᵀ y → (G : Goodᴺ (toZ (runᶜ C y))) → one⁰ ≺ forceᴺ _ G
Twᴺ : ∀ {m c φ χ} (C : Cx m c φ χ) → Nd C → Ctxᶜ C → ∀ {y : Q m c φ χ} → Rq m c c y y → One y → (G : Goodᴺ (toZ (runᶜ C y))) → one⁰ ≺ forceᴺ _ G
Twᵛ idO () c ey one G
Twᵛ (tlo {k = k} C) nz c {y = y} ey one G = Twᵀ C c {y = tl (flo k) (cvFlo k) y} (R-tl ey) (tl-cong one) G
Twᵛ (addo O a σ) nz (afl ea oa nzA , c) {y = y} ey one G = Twᵛ O nzA c {y = addˢ a σ y} (addˢ-≅ (≅ᴵ-refl _) ea ey) (add-floorᴱ {σ = σ} y oa ey) G
Twᵛ (tro O e) nz c {y = y} ey one G = Twᵛ O (NZ-e′ e nz) c {y = trˢ e y} (self-trˢ e ey) (fl-tr e (s≅ z≅ z≅) one) G
Twᵛ (tr⁻o O e) nz c {y = y} ey one G = Twᵛ O (NZ-e e nz) c {y = tr⁻ˢ e y} (self-tr⁻ˢ e ey) (fl-tr⁻ e (s≅ z≅ z≅) one) G
V₀ idO c ey two G = proj₂ L (h2N (proj₁ L))
  where L = two idO G
V₀ (tlo C) c {y = y} ey two G = Twᵀ C c {y = tl (flo zero) (cvFlo zero) y} (R-tl ey) (tl-cong (⊑ᴱ-trans 𝟏⊑𝟐 two)) G
V₀ (addo O a σ) (afl ea oa nzA , c) {y = y} ey two G = Twᵛ O nzA c {y = addˢ a σ y} (addˢ-≅ (≅ᴵ-refl _) ea ey) (add-floorᴱ {σ = σ} y oa ey) G
V₀ (tro O z≅) c {y = y} ey two G = V₀ O c {y = trˢ z≅ y} (self-trˢ z≅ ey) (fl-tr z≅ (s≅ z≅ (s≅ z≅ z≅)) two) G
V₀ (tr⁻o O z≅) c {y = y} ey two G = V₀ O c {y = tr⁻ˢ z≅ y} (self-tr⁻ˢ z≅ ey) (fl-tr⁻ z≅ (s≅ z≅ (s≅ z≅ z≅)) two) G
Twᵀ (top {i = zero} O ev p ok e) c {y = y} ry one G = V₀ O c {y = ψ̄ᵠ ok e y ev p} (R→≈ᵠ ry ok e ok e ev p ev p z≅) (S1ᵀ (⊑→One one)) G
Twᵀ (top {i = suc i} O ev p ok e) c {y = y} ry one G = Twᵛ O tt c {y = ψ̄ᵠ ok e y ev p} (R→≈ᵠ ry ok e ok e ev p ev p (≅ᴵ-refl _)) (⊑ᴱ-trans (Ω1ᴱ _) (F0ᵀ ry)) G
Twᵀ (top {i = lim f s} O ev p ok e) c {y = y} ry one G = Twᵛ O tt c {y = ψ̄ᵠ ok e y ev p} (R→≈ᵠ ry ok e ok e ev p ev p (≅ᴵ-refl _)) (⊑ᴱ-trans (Ω1ᴱ _) (F0ᵀ ry)) G
Twᵀ (pa {a = a} {b = b} W C) (w , c) {y = y} ry one G = Twᵀ C c {y = W ⊞ y} (R-⊞ (∼ᶠ-refl a) (Sim∼-refl b) (WFl.rW w) ry) (B1ᵀ ry (WFl.oneW w)) G
Twᵀ {m} (pψ {t = t} q C) c {y = y} ry one G = Twᵀ C c {y = ψᵠ q y} (R-ψᵠ q q (≅ᴵ-refl _) ry) (P0ᵀ {q = q} ry (𝟏⊑Ω̇ m t)) G
Twᵀ (pΨ {H = H} {t = t} qH ok e p C) c {y = y} ry one G = Twᵀ C c {y = Ψ qH ok e p y} (R-Ψ qH ok e p ok e p (≅ᴵ-refl _) ry) (H0ᵀ ry (𝟏⊑Ω̇ H t)) G
Twᵀ (pι q C) (n , c) {y = y} ry one G = Twᴺ C n c {y = ι q y} (R-ι q q ry) (One-ι q (⊑→One one)) G
Twᵀ (pD {q = qd} C) c {y = y} ry one G = Twᵀ C c {y = ι↓ qd y} (R-ι↓ qd (≅ᴵ-refl _) ry) (𝟏-D {qd = qd} one) G
Twᵀ (ptr e C) c {y = y} ry one G = Twᵀ C c {y = trQ e y} (R-tr₂ e e ry) (𝟏-tr e one) G
Twᵀ (ptr⁻ e C) c {y = y} ry one G = Twᵀ C c {y = tr⁻Q e y} (R-tr⁻₂ e e ry) (𝟏-tr⁻ e one) G
Twᴺ (top {i = zero} O ev p ok e) n c {y = y} ry one G = V₀ O c {y = ψ̄ᵠ ok e y ev p} (R→≈ᵠ ry ok e ok e ev p ev p z≅) (S1ᵀ one) G
Twᴺ (top {i = suc i} O ev p ok e) n c {y = y} ry one G = Twᵛ O tt c {y = ψ̄ᵠ ok e y ev p} (R→≈ᵠ ry ok e ok e ev p ev p (≅ᴵ-refl _)) (⊑ᴱ-trans (Ω1ᴱ _) (F0ᵀ ry)) G
Twᴺ (top {i = lim f s} O ev p ok e) n c {y = y} ry one G = Twᵛ O tt c {y = ψ̄ᵠ ok e y ev p} (R→≈ᵠ ry ok e ok e ev p ev p (≅ᴵ-refl _)) (⊑ᴱ-trans (Ω1ᴱ _) (F0ᵀ ry)) G
Twᴺ (pa {a = a} {b = b} W C) n (w , c) {y = y} ry one G = Twᵀ C c {y = W ⊞ y} (R-⊞ (∼ᶠ-refl a) (Sim∼-refl b) (WFl.rW w) ry) (B1ᵀ ry (WFl.oneW w)) G
Twᴺ {m} (pψ {t = t} q C) n c {y = y} ry one G = Twᵀ C c {y = ψᵠ q y} (R-ψᵠ q q (≅ᴵ-refl _) ry) (P0ᵀ {q = q} ry (𝟏⊑Ω̇ m t)) G
Twᴺ (pΨ {H = H} {t = t} qH ok e p C) n c {y = y} ry one G = Twᵀ C c {y = Ψ qH ok e p y} (R-Ψ qH ok e p ok e p (≅ᴵ-refl _) ry) (H0ᵀ ry (𝟏⊑Ω̇ H t)) G
Twᴺ (pι q C) n (n₁ , c) {y = y} ry one G = Twᴺ C n₁ c {y = ι q y} (R-ι q q ry) (One-ι q one) G
Twᴺ (pD C) () c ry one G
Twᴺ (ptr e C) n c {y = y} ry one G = Twᴺ C n c {y = trQ e y} (R-tr₂ e e ry) (One-tr e one) G
Twᴺ (ptr⁻ e C) n c {y = y} ry one G = Twᴺ C n c {y = tr⁻Q e y} (R-tr⁻₂ e e ry) (One-tr⁻ e one) G
```
