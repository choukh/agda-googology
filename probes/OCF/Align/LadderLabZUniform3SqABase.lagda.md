> **机械克隆, 验收用.** 由 `ScafLadderZUniform3SqABase` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆.** 由 `Uniform3SqABase` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 统一形 (三): 层对齐的标签理论 (一) (OmegaSqABase 的移植)

> [OmegaSqABase](OmegaSqABase.lagda.md) 在修正的折叠上重编译, 改动 44 行. 内容上的改动只有: (1) `FP c φ` 的可忽略项带种类 (`IgnK`, Uniform3Rel), `fb K` 项可以是 $K\sqsubseteq c+1$; (2) `LvOK` 的第二支从 $k\sqsubseteq2$ 收紧为字面的 `Low k` ($k$ 为 $0,1,2$): 退化极限 $\lim[2,2,\dots]\sqsubseteq2$ 现在地板是 `fb`, 没有 $\Omega_1$ 的见证, 也用不到; (3) `W₊` 的 `up (self n)` 子句换地板.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZUniform3SqABase where

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
open import OCF.Align.LadderLabZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; _+ˢ_; trˢ; tr⁻ˢ; H1-pen)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; sucT; cmpᵀ; lt; eq; gt; []<; cofA)
  renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.Bachmann using (pen→<; gt→≤; clash)
open import OCF.Align.Closure using (Pen)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-fsn)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.LadderLabZStage2Label using (one⁰)
open import OCF.Align.LadderLabZDecoupleBase using (ΩΩ)
open import OCF.Align.LadderLabZDecouple using (Idx; lvI; Ilt; Ieq; kdI; kdI′; gtν; kdI[]; cofP)
open import OCF.Align.LadderLabZGoodLBase
open import OCF.Align.LadderLabZOmegaExpBase using (πw; OccΣ; cofW; repW; ωW; γW; gtW; penW; H1W; ne-w; 1<γ; snoc)
open import OCF.Align.LadderLabZOmegaSq using (I₁)
open import OCF.Align.LadderLabZUniformS
open import OCF.Align.LadderLabZUniform3Base
open import OCF.Align.LadderLabZUniform3Depth1 using (wkLW; wkL0; c1Ω; cωΩ; cΩΩ; penΩ)
open import OCF.Align.LadderLabZUniform3Rel
open GRᴬ public
```

## §1 $\cong^\mathsf A$ 的反演

自互模拟 $t\cong^\mathsf At$ 的子项都由构造子直接给出: `sᴬ`/`lᴬ`/`lᵢᴬ`/`uᴬ`/`ŝᴬ`/`ĉᴬ` 的两侧同形, 所以不需要 UniformS 里经 `≅ˢ-reflˡ` 的绕行 (那里要剥单侧的 `upʳ`). 第 0 层的 $\cong^\mathsf s$ 推导没有 `up` 与 `limᵢ`, 于是蕴含 $\cong^\mathsf A$ (`≅ˢ₀→≅ᴬ`, 与 Relative 的 `≅ᴬ→≅ˢ₀` 互逆).

```agda
s-invᴬ : ∀ {k} {a : Ordˢ k} → Ord₊ˢ.suc a ≅ᴬ Ord₊ˢ.suc a → a ≅ᴬ a
s-invᴬ (sᴬ d) = d

l-invᴬ : ∀ {k} {f : ℕ → Ordˢ k} → Ord₊ˢ.lim f ≅ᴬ Ord₊ˢ.lim f → ∀ n → f n ≅ᴬ f n
l-invᴬ (lᴬ h) = h

i-respᴬ : ∀ {k j} {p : j <ᴵ k} {f : Uˢ j (<→◃ p) → Ordˢ k} → Ord₊ˢ.limᵢ p f ≅ᴬ Ord₊ˢ.limᵢ p f →
          ∀ {z z′ : Ordˢ j} → z ≅ᴬ z′ → f (intoˢ (<→◃ p) z) ≅ᴬ f (intoˢ (<→◃ p) z′)
i-respᴬ {p = p} (lᵢᴬ e h) d = h _ _ (≅→Rᴬ (<→◃ p) d)

u-invᴬ : ∀ {k k′ ℓ ℓ′} (r : k ◃₁ ℓ) (r′ : k′ ◃₁ ℓ′) {x : Uˢ k (◃₁→◃ r)} {y : Uˢ k′ (◃₁→◃ r′)} →
         Ord₊ˢ.up r x ≅ᴬ Ord₊ˢ.up r′ y → outˢ (◃₁→◃ r) x ≅ᴬ outˢ (◃₁→◃ r′) y
u-invᴬ zero     r′ (uᴬ _ d) = d
u-invᴬ (self n) r′ (uᴬ _ d) = d

u-reflᴬ : ∀ {k ℓ} (r : k ◃₁ ℓ) {x : Uˢ k (◃₁→◃ r)} → Ord₊ˢ.up r x ≅ᴬ Ord₊ˢ.up r x →
          outˢ (◃₁→◃ r) x ≅ᴬ outˢ (◃₁→◃ r) x
u-reflᴬ r e = u-invᴬ r r e

ŝ-refl₀ᴬ : ∀ {k c t₀ g} → Ord₊ˢ.ŝ {ℓ = k} c t₀ g ≅ᴬ Ord₊ˢ.ŝ c t₀ g → t₀ ≅ᴬ t₀
ŝ-refl₀ᴬ (ŝᴬ _ _ et _) = et

ŝ-reflgᴬ : ∀ {k c t₀ g} → Ord₊ˢ.ŝ {ℓ = k} c t₀ g ≅ᴬ Ord₊ˢ.ŝ c t₀ g → ∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᴬ g η′ e′
ŝ-reflgᴬ (ŝᴬ _ _ _ eg) = eg

ĉ-refl₀ᴬ : ∀ {k c t₀ g o₀ o} → Ord₊ˢ.ĉᴸ {ℓ = k} c t₀ g o₀ o ≅ᴬ Ord₊ˢ.ĉᴸ c t₀ g o₀ o → o₀ ≅ᴬ o₀
ĉ-refl₀ᴬ (ĉᴬ _ _ _ eo _) = eo

ĉ-reflgᴬ : ∀ {k c t₀ g o₀ o} → Ord₊ˢ.ĉᴸ {ℓ = k} c t₀ g o₀ o ≅ᴬ Ord₊ˢ.ĉᴸ c t₀ g o₀ o → ∀ η e → o η e ≅ᴬ o η e
ĉ-reflgᴬ (ĉᴬ _ _ _ _ eO) η e = eO η e η e (≅ᴵ-refl η)

≅ˢ₀→≅ᴬ : ∀ {x y : Ordˢ zero} → x ≅ˢ y → x ≅ᴬ y
≅ˢ₀→≅ᴬ z≅ = zᴬ
≅ˢ₀→≅ᴬ (s≅ d) = sᴬ (≅ˢ₀→≅ᴬ d)
≅ˢ₀→≅ᴬ (l≅ h) = lᴬ (λ n → ≅ˢ₀→≅ᴬ (h n))
≅ˢ₀→≅ᴬ (lᵢ≅ {p = ()} e h)
≅ˢ₀→≅ᴬ (upˡ {r = ()} d)
≅ˢ₀→≅ᴬ (upʳ {r = ()} d)
≅ˢ₀→≅ᴬ (ŝ≅ k ec et eg) = ŝᴬ k ec (≅ˢ₀→≅ᴬ et) (λ η e η′ e′ eη → ≅ˢ₀→≅ᴬ (eg η e η′ e′ eη))
≅ˢ₀→≅ᴬ (ĉ≅ ec dt dg eo eO) = ĉᴬ ec dt dg (≅ˢ₀→≅ᴬ eo) (λ η e η′ e′ eη → ≅ˢ₀→≅ᴬ (eO η e η′ e′ eη))
```

## §2 深度 0 的标签理论在 $\cong^\mathsf A$ 上

`limᵢ0ᴬ`: Uniform2Base `limᵢ0` 的 $\cong^\mathsf A$ 版, 前提 `H0ᴬ` 的互模拟换成 $\approx^\mathsf A$. 节点层 0 的链原子要 $\cong^\mathsf s$ (`Atomᴸ`), 由 §1 的两个转换互换.

```agda
H0ᴬ : ∀ {φ j} → (Ordˢ j → Run φ) → (T → T) → Set
H0ᴬ {j = j} H lab = ∀ η (x : Ordˢ j) → LabL x η → x ≅ᴬ x → L0 (H x) (lab η) × (H x ≈ᴬ H x)

limᵢ0ᴬ : ∀ {φ j ν} {ps : T} {y : PT} {ys : T} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → Run φ} →
         cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
         (∀ η x → LabL x η → LW (H x) (ps ++ fsT (y ∷ ys) η)) → H0ᴬ H (λ η → ps ++ fsT (y ∷ ys) η) →
         L0 (limᵢA 0 ac H) (ps ++ (y ∷ ys))
limᵢ0ᴬ {j = zero} {ν = ν} {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} c Iν ej hW h0 ev p nu =
  subst (λ W → Lab₀ W (ψ₀ᵗ (ps ++ (y ∷ ys)))) (sym eqf)
        (limᴸ nu cω′ (λ m → proj₁ (outp m)) (λ m → subst (Lab _) (sym (gtW [] ps y ys [] c₀ refl m)) (proj₂ (outp m))))
  where
  c₀ : cof (y ∷ ys) ≡ cΩ []
  c₀ = trans c (cong cΩ (kdI Iν (sym (kd-≅ ej))))
  cω′ = trans (cofW [] ps y ys) (cong (cofA []) c₀)
  eqf = fold1A {ac = ac} {H = H} {ev = ev} {p = p} (inj₂ z≅)
  nfγ : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
  nfγ m = subst NF₁ (gtW [] ps y ys [] c₀ refl m) (NF₁-fsn nu cω′ m)
  atm : ∀ m → Atomᴸ (chainA ac H ev m) (γW ps (y ∷ ys) [] m)
  atm zero    = Ωˢ-refl zero , gs gz , l1 refl (s≅ z≅) (l0 refl z≅)
  atm (suc m) = ≅ᴬ→≅ˢ₀ (proj₂ (h0 _ _ (atm m) (≅ˢ₀→≅ᴬ (proj₁ (atm m)))) ev (ac ev) ev (ac ev) z≅) ,
                proj₁ (h0 _ _ (atm m) (≅ˢ₀→≅ᴬ (proj₁ (atm m)))) ev (ac ev) (nfγ m)
  outp : ∀ m → Lab₀ (H (chainA ac H ev m) ev p) (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
  outp m = proj₁ (h0 _ _ (atm m) (≅ˢ₀→≅ᴬ (proj₁ (atm m)))) ev p (nfγ m)
limᵢ0ᴬ {j = suc j′} {ν = []} c Iν ej hW h0 ev p nu = ⊥-elim (tf (trans (sym (kdI[] Iν)) (sym (kd-≅ ej))))
limᵢ0ᴬ {j = suc j′} {ν = v ∷ vs} {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} c Iν ej hW h0 ev p nu =
  subst (λ W → Lab₀ W (ψ₀ᵗ (ps ++ (y ∷ ys)))) (sym eqf)
        (limᴸ nu cω′ (λ m → proj₁ (outp m)) (λ m → subst (Lab _) (sym (gtW [] ps y ys (v ∷ vs) c refl m)) (proj₂ (outp m))))
  where
  cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
  eqf = fold1A {ac = ac} {H = H} {ev = ev} {p = p} (inj₁ (z≺I Iν ej (λ ())))
  nf : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  nf m = subst NF₁ (gtW [] ps y ys (v ∷ vs) c refl m) (NF₁-fsn nu cω′ m)
  chainL : ∀ m → LabL (chainA ac H ev m) (γW ps (y ∷ ys) (v ∷ vs) m)
  chainL zero    = LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
  chainL (suc m) = hW _ _ (chainL m) ev (ac ev) Iν ej refl
  selfC : ∀ m → chainA ac H ev m ≅ᴬ chainA ac H ev m
  selfC zero    = Ωˢ-≅ᴬ (≅ᴵ-refl _)
  selfC (suc m) = proj₂ (h0 _ _ (chainL m) (selfC m)) ev (ac ev) ev (ac ev) (≅ᴵ-refl _)
  outp : ∀ m → Lab₀ (H (chainA ac H ev m) ev p) (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  outp m = proj₁ (h0 _ _ (chainL m) (selfC m)) ev p (nf m)
limᵢ0ᴬ {j = lim f s} {ν = []} c Iν ej hW h0 ev p nu = ⊥-elim (tf (trans (sym (kdI[] Iν)) (sym (kd-≅ ej))))
limᵢ0ᴬ {j = lim f s} {ν = v ∷ vs} {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} c Iν ej hW h0 ev p nu =
  subst (λ W → Lab₀ W (ψ₀ᵗ (ps ++ (y ∷ ys)))) (sym eqf)
        (limᴸ nu cω′ (λ m → proj₁ (outp m)) (λ m → subst (Lab _) (sym (gtW [] ps y ys (v ∷ vs) c refl m)) (proj₂ (outp m))))
  where
  cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
  eqf = fold1A {ac = ac} {H = H} {ev = ev} {p = p} (inj₁ (z≺I Iν ej (λ ())))
  nf : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  nf m = subst NF₁ (gtW [] ps y ys (v ∷ vs) c refl m) (NF₁-fsn nu cω′ m)
  chainL : ∀ m → LabL (chainA ac H ev m) (γW ps (y ∷ ys) (v ∷ vs) m)
  chainL zero    = LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
  chainL (suc m) = hW _ _ (chainL m) ev (ac ev) Iν ej refl
  selfC : ∀ m → chainA ac H ev m ≅ᴬ chainA ac H ev m
  selfC zero    = Ωˢ-≅ᴬ (≅ᴵ-refl _)
  selfC (suc m) = proj₂ (h0 _ _ (chainL m) (selfC m)) ev (ac ev) ev (ac ev) (≅ᴵ-refl _)
  outp : ∀ m → Lab₀ (H (chainA ac H ev m) ev p) (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  outp m = proj₁ (h0 _ _ (chainL m) (selfC m)) ev p (nf m)
```

`Tl0ᴬ`: Uniform2Base `Tl0` 逐字, 反演换成 §1 的, `gi` 行的互模拟由 Relative 的 `fold-≅0ᴬ`. `tlGRᴬ` 是 TopDown `goodTl` 在深度 0 的层对齐形式.

```agda
module Tl0ᴬ {fl} {P : Run fl} {π : T} (hP : LW P π) (h0P : L0 P π) (hR : P ≈ᴬ P) where
  open TlW hP
  tl0Aᴬ : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → Lab0ᴸ t y → t ≅ᴬ t → L0 (fold 0 φ cv P t) (π ++ y)
  tl0Vᴬ : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → LabL t y → t ≅ᴬ t → L0 (fold 0 φ cv P t) (π ++ y)
  tl0₊ᴬ : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → LabL₊ k Ll t y → t ≅ᴬ t → L0 (fold 0 φ cv P t) (π ++ y)

  tl0Aᴬ {φ = φ} {y = []} (lz c) ex = z0 {φ = φ} {P = P} h0P
  tl0Aᴬ {y = y ∷ ys} (lz c) ex = ⊥-elim (cof-ne y ys c)
  tl0Aᴬ {y = []} (ls () l) ex
  tl0Aᴬ {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y ∷ ys} (ls c l) ex = suc0 {R = fold 0 φ cv P a} c (tl0Aᴬ {cv = cv} l (s-invᴬ ex))
  tl0Aᴬ {y = []} (ll () h) ex
  tl0Aᴬ {φ = φ} {cv = cv} {t = Ord₊ˢ.lim F} {y = y ∷ ys} (ll c h) ex =
    lim0 {F = λ n → fold 0 φ cv P (F n)} c (λ n → tl0Aᴬ {cv = cv} (h n) (l-invᴬ ex n))
  tl0Aᴬ {y = []} (lŝ₀ () K h₀ hk) ex
  tl0Aᴬ {φ = φ} {cv = cv} {y = y ∷ ys} (lŝ₀ {t₀ = t₀} {g = g} c K h₀ hk) ex =
    ĉ0 {O₀ = fold 0 φ cv P t₀} {O = λ η e → fold 0 φ cv P (g η e)} c K (tl0Aᴬ h₀ (ŝ-refl₀ᴬ ex))
       (λ k → tl0Aᴬ (hk k) (ŝ-reflgᴬ ex _ _ _ _ (≅ᴵ-refl _)))
  tl0Aᴬ {y = []} (lĉ () K h₀ hk) ex
  tl0Aᴬ {φ = φ} {cv = cv} {y = y ∷ ys} (lĉ {o₀ = o₀} {o = o} c K h₀ hk) ex =
    ĉ0 {O₀ = fold 0 φ cv P o₀} {O = λ η e → fold 0 φ cv P (o η e)} c K (tl0Aᴬ h₀ (ĉ-refl₀ᴬ ex))
       (λ k → tl0Aᴬ (hk k) (ĉ-reflgᴬ ex _ _))

  tl0Vᴬ {k = zero}    at ex = tl0Aᴬ (atomL at) ex
  tl0Vᴬ {k = suc _}   h  ex = tl0₊ᴬ h ex
  tl0Vᴬ {k = lim _ _} h  ex = tl0₊ᴬ h ex

  tl0₊ᴬ {φ = φ} {y = []} (gz c) ex = z0 {φ = φ} {P = P} h0P
  tl0₊ᴬ {y = y ∷ ys} (gz c) ex = ⊥-elim (cof-ne y ys c)
  tl0₊ᴬ {y = []} (gs () l) ex
  tl0₊ᴬ {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y ∷ ys} (gs c l) ex = suc0 {R = fold 0 φ cv P a} c (tl0₊ᴬ {cv = cv} l (s-invᴬ ex))
  tl0₊ᴬ {y = []} (gl () h) ex
  tl0₊ᴬ {φ = φ} {cv = cv} {t = Ord₊ˢ.lim F} {y = y ∷ ys} (gl c h) ex =
    lim0 {F = λ n → fold 0 φ cv P (F n)} c (λ n → tl0₊ᴬ {cv = cv} (h n) (l-invᴬ ex n))
  tl0₊ᴬ {k = suc k′} {φ = φ} {cv = cv} (gu {r = zero} h) ex =
    λ ev p → tl0Vᴬ {φ = flo k′} {cv = cvFlo k′} h (u-reflᴬ zero ex) (proj₁ ev , toFlo k′ (λ q → cv (proj₂ ev) (suc q))) p
  tl0₊ᴬ {k = lim f s} {φ = φ} {cv = cv} (gu {r = self n} h) ex =
    λ ev p → tl0Vᴬ {φ = flo (f n)} {cv = cvFlo (f n)} h (u-reflᴬ (self n) ex) (proj₁ ev , toFlo (f n) (λ q → cv (proj₂ ev) (lim n q))) p
  tl0₊ᴬ {y = []} (gi () I ej h) ex
  tl0₊ᴬ {φ = φ} {cv = cv} {y = y ∷ ys} (gi {q = q} {f = f} c I ej h) ex =
    limᵢ0ᴬ {ac = λ ev → cv (proj₂ ev) q} {H = λ x → fold 0 φ cv P (f (intoˢ (<→◃ q) x))} c I ej
           (λ η x l → tlW₊ (h η x (→Ll (<→◃ q) l)))
           (λ η x l xx → tl0₊ᴬ (h η x (→Ll (<→◃ q) l)) (i-respᴬ ex xx) , fold-≅0ᴬ hR (i-respᴬ ex xx))
  tl0₊ᴬ {y = []} (gĉ () K h₀ hk) ex
  tl0₊ᴬ {φ = φ} {cv = cv} {y = y ∷ ys} (gĉ {o₀ = o₀} {o = o} c K h₀ hk) ex =
    ĉ0 {O₀ = fold 0 φ cv P o₀} {O = λ η e → fold 0 φ cv P (o η e)} c K (tl0₊ᴬ h₀ (ĉ-refl₀ᴬ ex))
       (λ k → tl0₊ᴬ (hk k) (ĉ-reflgᴬ ex _ _))
  tl0₊ᴬ {k = zero} (gŝ () c Iw bw ob h₀ hg) ex
  tl0₊ᴬ {k = suc _} {y = []} (gŝ kk () Iw bw ob h₀ hg) ex
  tl0₊ᴬ {k = suc _} {φ = φ} {cv = cv} {y = y ∷ ys} (gŝ {t₀ = t₀} {g = g} kk c Iw bw ob h₀ hg) ex =
    ŝ0 {T₀ = fold 0 φ cv P t₀} {G = λ η e → fold 0 φ cv P (g η e)} c Iw bw (λ θ → OccΣ π (ob θ)) (tl0₊ᴬ h₀ (ŝ-refl₀ᴬ ex))
       (λ θ Y hY lY nθ lt e → tl0₊ᴬ (hg θ Y hY lY nθ lt e) (ŝ-reflgᴬ ex _ _ _ _ (≅ᴵ-refl _)))
  tl0₊ᴬ {k = lim _ _} {y = []} (gŝ kk () Iw bw ob h₀ hg) ex
  tl0₊ᴬ {k = lim _ _} {φ = φ} {cv = cv} {y = y ∷ ys} (gŝ {t₀ = t₀} {g = g} kk c Iw bw ob h₀ hg) ex =
    ŝ0 {T₀ = fold 0 φ cv P t₀} {G = λ η e → fold 0 φ cv P (g η e)} c Iw bw (λ θ → OccΣ π (ob θ)) (tl0₊ᴬ h₀ (ŝ-refl₀ᴬ ex))
       (λ θ Y hY lY nθ lt e → tl0₊ᴬ (hg θ Y hY lY nθ lt e) (ŝ-reflgᴬ ex _ _ _ _ (≅ᴵ-refl _)))

tlGRᴬ : ∀ {fl} {P : Run fl} {π} → GRᴬ P π → ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} →
        LabL t y → t ≅ᴬ t → GRᴬ (fold 0 φ cv P t) (π ++ y)
tlGRᴬ (grᴬ hW h0 hR) l ex = grᴬ (TlW.tlWV hW l) (Tl0ᴬ.tl0Vᴬ hW h0 hR l ex) (fold-≅0ᴬ hR ex)
```

**$\Omega_\Omega$ 的闭包, 深度 0.** Uniform2Base `goodΩ̂0` 逐字, 互模拟由 `cloRᴬ`/`fold-≅0ᴬ`.

```agda
goodΩ̂0ᴬ : ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π → GRᴬ (Ω̂A 0 P) (π ++ ΩΩ ∷ [])
goodΩ̂0ᴬ {fl} {P} {π} (F , GP) =
  grᴬ (cloW {t = T₁} {g = Gη} (FW-pop F) refl (gWᴬ Lt) (λ θ Y hY lY nθ lt → gWᴬ (Lg θ Y hY lY nθ)))
      (clo0 {t = T₁} {g = Gη} (FW-pop F) refl (g0ᴬ Lt) (λ θ Y hY lY nθ lt → g0ᴬ (Lg θ Y hY lY nθ)))
      (cloRᴬ {t = T₁} {g = Gη} {t′ = T₁} {g′ = Gη} (∼ᶠ-refl fl) (fold-≅0ᴬ (gRᴬ GP) (Ωˢ-≅ᴬ (≅ᴵ-refl (suc zero))))
             (λ η η′ eη → fold-≅0ᴬ (gRᴬ GP) (Ωˢ-≅ᴬ eη)))
  where
  T₁ : Run (fl ⊔ fk zero)
  T₁ = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))
  Gη : (η : Ordᴵ) → Run (fl ⊔ fk η)
  Gη η = fold 0 (fk η) (λ e q → e (suc q)) P (Ωˢ η)
  Lt : GRᴬ T₁ (π ++ Ωt (natT 1))
  Lt = tlGRᴬ GP (LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _)) (Ωˢ-≅ᴬ (≅ᴵ-refl (suc zero)))
  Lg : ∀ θ Y (hY : HS Y) → Lab Y θ → NF₁ θ → GRᴬ (Gη (toLevel Y hY)) (π ++ Ωt θ)
  Lg θ Y hY lY nθ = tlGRᴬ GP (LabL-Ω Y hY lY nθ (≅ᴵ-refl _)) (Ωˢ-≅ᴬ (≅ᴵ-refl _))

GA0ᴬ-Ω̂ : ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π → GA0ᴬ (Ω̂A 0 P) (π ++ ΩΩ ∷ [])
GA0ᴬ-Ω̂ (F , GP) = FlrLab-⊔ F FlrLab-z , goodΩ̂0ᴬ (F , GP)
```

## §3 依目标的行引理

RelativeBase 的 `LW[ c ]` 只在目标 $i\succeq c$ 处要求标签. 下面是 Uniform2Base §7 的 `…W` 引理在 `LW[ c ]` 上的逐字复制 (后缀 `ᶜ`): 多一个 `Up c i` 参数, 原样传给前提. 唯一有内容的地方是 `limᵢWᶜ` 的折叠情形: 链在节点层 $j$ 上算, 由 $i\preceq j$ (`gt→≤`) 把下界抬到 $j$ (`Up-ij`).

```agda
Up-ij : ∀ {c i j} → Up c i → (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → Up c j
Up-ij u (inj₁ s) = Up-≺ u s
Up-ij u (inj₂ e) = Up-≅ u e

wkLWᶜ : ∀ {c φ ψ} {R : Run φ} (le : ∀ {L} → Ev L ψ → Ev L φ) {u} → LW[ c ] R u → LW[ c ] (wk 0 le R) u
wkLWᶜ le h ev p = h (le ev) p

zWᶜ : ∀ {c φ fl} {P : Run fl} {π} → LW[ c ] P π → LW[ c ] (wk 0 (proj₁ {B = λ _ → Ev _ φ}) P) (π ++ [])
zWᶜ {π = π} h ev p Iw ei ki u = subst (λ v → LabL₊ _ Ll _ (ψᵗ _ v ∷ [])) (sym (++-identityʳ π)) (h (proj₁ ev) p Iw ei ki u)

module _ {c φ} {ps : T} {y : PT} {ys : T} where
  limWᶜ : ∀ {F : ℕ → Run φ} → cof (y ∷ ys) ≡ cω → (∀ n → LW[ c ] (F n) (ps ++ fsn (y ∷ ys) n)) →
          LW[ c ] (limA 0 F) (ps ++ (y ∷ ys))
  limWᶜ {F} cc h {w = w} ev p Iw ei ki u =
    gl (trans (cofW w ps y ys) (cong (cofA w) cc)) (λ n → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys cc n)) (h n ev p Iw ei ki u))

  sucWᶜ : ∀ {R : Run φ} → cof (y ∷ ys) ≡ c1 → LW[ c ] R (ps ++ pred (y ∷ ys)) → LW[ c ] (sucRun R) (ps ++ (y ∷ ys))
  sucWᶜ {R} cc h {w = w} ev p Iw ei ki u =
    gl (trans (cofW w ps y ys) (cong (cofA w) cc))
       (λ m → subst (LabL₊ _ Ll _) (sym (repW w ps y ys cc m)) (LRep ki (h ev p Iw ei ki u) m))

module _ {c φ j ν} {ps : T} {y : PT} {ys : T} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → Run φ}
         (cc : cof (y ∷ ys) ≡ cΩ ν) (Iν : Idx ν) (ej : j ≅ᴵ lvI Iν) where

  limᵢWᶜ : (∀ η x → LabL x η → LW[ c ] (H x) (ps ++ fsT (y ∷ ys) η)) → LW[ c ] (limᵢA 0 ac H) (ps ++ (y ∷ ys))
  limᵢWᶜ hW {i = i} {w = w} ev p Iw ei ki u = go (cmpᵀ (sucT ν) w) refl
    where
    pen : Pen (cmpᵀ (sucT ν) w) → LabL₊ i Ll (limᵢA 0 ac H ev p) (πw w ps (y ∷ ys))
    pen pn with pen1A {ac = ac} {H = H} {ev = ev} {p = p} (≅ᴵ-refl j)
                      (≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei))
    ... | j′ , e , r , eqn =
      subst (λ W → LabL₊ i Ll W (πw w ps (y ∷ ys))) (sym eqn)
            (gi cofE Iν (≅ᴵ-trans (≅ᴵ-sym e) ej)
                (λ η x l → subst (λ v → LabL₊ i Ll (H (tr⁻ˢ e v) ev p) (fsT (πw w ps (y ∷ ys)) η))
                                 (sym (out-intoˢ (<→◃ r) x))
                                 (subst (LabL₊ i Ll _) (sym (penW w ps y ys ν cc pn η))
                                        (hW η (tr⁻ˢ e x) (LabL-tr⁻ e (Ll→ (<→◃ r) l)) ev p Iw ei ki u))))
      where
      cofE : cof (πw w ps (y ∷ ys)) ≡ cΩ ν
      cofE = trans (cofW w ps y ys) (trans (cong (cofA w) cc) (cofP pn))
    fld : cmpᵀ (sucT ν) w ≡ gt → LabL₊ i Ll (limᵢA 0 ac H ev p) (πw w ps (y ∷ ys))
    fld em =
      subst (λ W → LabL₊ i Ll W (πw w ps (y ∷ ys))) (sym (fold1A {ac = ac} {H = H} {ev = ev} {p = p} ij))
            (gl (trans (cofW w ps y ys) (trans (cong (cofA w) cc) (cong (E.cofψ₊ w ν) em)))
                (λ m → subst (LabL₊ i Ll _) (sym (gtW w ps y ys ν cc em m)) (hW _ _ (chainL m) ev p Iw ei ki u)))
      where
      gev : (lvI Iw ≺ᴵ lvI Iν) ⊎ (lvI Iw ≅ᴵ lvI Iν)
      gev with gt→≤ ν w em
      ... | inj₁ pw   = inj₁ (Ilt Iw Iν pw)
      ... | inj₂ refl = inj₂ (Ieq Iw Iν)
      ij : (i ≺ᴵ j) ⊎ (i ≅ᴵ j)
      ij with gev
      ... | inj₁ s  = inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ ei s) (≅ᴵ-sym ej))
      ... | inj₂ c′ = inj₂ (≅ᴵ-trans ei (≅ᴵ-trans c′ (≅ᴵ-sym ej)))
      kj : kd j ≡ false
      kj = trans (kd-≅ ej) (kdI′ Iν (gtν em (ne-w Iw ei ki)))
      uj : Up c j
      uj = Up-ij u ij
      chainL : ∀ m → LabL (chainA ac H ev m) (γW ps (y ∷ ys) ν m)
      chainL zero    = LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
      chainL (suc m) = frL₊ kj (hW _ _ (chainL m) ev (ac ev) Iν ej kj uj)
    go : ∀ m → cmpᵀ (sucT ν) w ≡ m → LabL₊ i Ll (limᵢA 0 ac H ev p) (πw w ps (y ∷ ys))
    go lt em = pen (inj₁ em)
    go eq em = pen (inj₂ em)
    go gt em = fld em

module _ {c φ c₀ t₀} {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {ps : T} {y : PT} {ys : T} where
  ĉWᶜ : ∀ {O₀ : Run φ} {O : (η : Ordᴵ) → c₀ ⊑ᴵ η → Run φ} → cof (y ∷ ys) ≡ cω → (K : CCᴸ c₀ t₀ g) →
        LW[ c ] O₀ (ps ++ fsn (y ∷ ys) 0) → (∀ k → LW[ c ] (O (lvK K k) (dxK K k)) (ps ++ fsn (y ∷ ys) (suc k))) →
        LW[ c ] (ĉA 0 c₀ t₀ g O₀ O) (ps ++ (y ∷ ys))
  ĉWᶜ cw K h₀ hk {w = w} ev p Iw ei ki u =
    gĉ (trans (cofW w ps y ys) (cong (cofA w) cw)) K
       (subst (LabL₊ _ Ll _) (sym (ωW w ps y ys cw 0)) (h₀ ev p Iw ei ki u))
       (λ k → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys cw (suc k))) (hk k ev p Iw ei ki u))

module _ {c φ c₀ w′} {ps : T} {y : PT} {ys : T} {T₀ : Run φ} {G : (η : Ordᴵ) → c₀ ⊑ᴵ η → Run φ}
         (cs : cof (y ∷ ys) ≡ cΩ []) (Iw′ : Idx w′) (bw : c₀ ⊑ᴵ suc (lvI Iw′)) (ob : Ob w′ ps y ys) where
  ŝWᶜ : LW[ c ] T₀ (ps ++ fsT (y ∷ ys) (natT 1)) →
        (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c₀ ⊑ᴵ toLevel Y hY) → LW[ c ] (G (toLevel Y hY) e) (ps ++ fsT (y ∷ ys) θ)) →
        LW[ c ] (ŝA 0 c₀ T₀ G) (ps ++ (y ∷ ys))
  ŝWᶜ h₀ hg {w = []} ev p Iw ei ki u = ⊥-elim (ne-w Iw ei ki refl)
  ŝWᶜ h₀ hg {w = x ∷ xs} ev p Iw ei ki u =
    gŝ ki (trans (cofW (x ∷ xs) ps y ys) (trans (cong (cofA (x ∷ xs)) cs) (H1-pen x xs))) Iw′ bw
       (λ θ → subst (Occ _) (sym (H1W x xs ps y ys cs θ)) (od (ob θ)))
       (subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys cs (natT 1))) (h₀ ev p Iw ei ki u))
       (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys cs θ)) (hg θ Y hY lY nθ lt e ev p Iw ei ki u))
```

**深度 0 的尾巴递归 (`TlWᶜ`).** Uniform2Base `TlW` 逐字, 底与结论都依目标. 这是让 `GA1ᴴ` 的 W 部分可以接受依目标的底 (副本的底只有依目标的标签) 所需要的.

```agda
module TlWᶜ {c fl} {P : Run fl} {π : T} (hP : LW[ c ] P π) where
  tlWAᶜ : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → Lab0ᴸ t y → LW[ c ] (fold 0 φ cv P t) (π ++ y)
  tlWVᶜ : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → LabL t y → LW[ c ] (fold 0 φ cv P t) (π ++ y)
  tlW₊ᶜ : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → LabL₊ k Ll t y → LW[ c ] (fold 0 φ cv P t) (π ++ y)

  tlWAᶜ {y = []} (lz cc) = zWᶜ hP
  tlWAᶜ {y = y ∷ ys} (lz cc) = ⊥-elim (cof-ne y ys cc)
  tlWAᶜ {y = []} (ls () l)
  tlWAᶜ {y = y ∷ ys} (ls cc l) = sucWᶜ cc (tlWAᶜ l)
  tlWAᶜ {y = []} (ll () h)
  tlWAᶜ {y = y ∷ ys} (ll cc h) = limWᶜ cc (λ n → tlWAᶜ (h n))
  tlWAᶜ {y = []} (lŝ₀ () K h₀ hk)
  tlWAᶜ {φ = φ} {cv = cv} {y = y ∷ ys} (lŝ₀ {t₀ = t₀} {g = g} cc K h₀ hk) =
    ĉWᶜ {O₀ = fold 0 φ cv P t₀} {O = λ η e → fold 0 φ cv P (g η e)} cc K (tlWAᶜ h₀) (λ k → tlWAᶜ (hk k))
  tlWAᶜ {y = []} (lĉ () K h₀ hk)
  tlWAᶜ {φ = φ} {cv = cv} {y = y ∷ ys} (lĉ {o₀ = o₀} {o = o} cc K h₀ hk) =
    ĉWᶜ {O₀ = fold 0 φ cv P o₀} {O = λ η e → fold 0 φ cv P (o η e)} cc K (tlWAᶜ h₀) (λ k → tlWAᶜ (hk k))

  tlWVᶜ {k = zero}    at = tlWAᶜ (atomL at)
  tlWVᶜ {k = suc _}   h  = tlW₊ᶜ h
  tlWVᶜ {k = lim _ _} h  = tlW₊ᶜ h

  tlW₊ᶜ {y = []} (gz cc) = zWᶜ hP
  tlW₊ᶜ {y = y ∷ ys} (gz cc) = ⊥-elim (cof-ne y ys cc)
  tlW₊ᶜ {y = []} (gs () l)
  tlW₊ᶜ {y = y ∷ ys} (gs cc l) = sucWᶜ cc (tlW₊ᶜ l)
  tlW₊ᶜ {y = []} (gl () h)
  tlW₊ᶜ {y = y ∷ ys} (gl cc h) = limWᶜ cc (λ n → tlW₊ᶜ (h n))
  tlW₊ᶜ {k = suc k′} {φ = φ} {cv = cv} (gu {r = zero} h) = λ ev p → tlWVᶜ {φ = flo k′} {cv = cvFlo k′} h (proj₁ ev , toFlo k′ (λ q → cv (proj₂ ev) (suc q))) p
  tlW₊ᶜ {k = lim f s} {φ = φ} {cv = cv} (gu {r = self n} h) = λ ev p → tlWVᶜ {φ = flo (f n)} {cv = cvFlo (f n)} h (proj₁ ev , toFlo (f n) (λ q → cv (proj₂ ev) (lim n q))) p
  tlW₊ᶜ {y = []} (gi () I ej h)
  tlW₊ᶜ {y = y ∷ ys} (gi {q = q} cc I ej h) = limᵢWᶜ cc I ej (λ η x l → tlW₊ᶜ (h η x (→Ll (<→◃ q) l)))
  tlW₊ᶜ {y = []} (gĉ () K h₀ hk)
  tlW₊ᶜ {φ = φ} {cv = cv} {y = y ∷ ys} (gĉ {o₀ = o₀} {o = o} cc K h₀ hk) =
    ĉWᶜ {O₀ = fold 0 φ cv P o₀} {O = λ η e → fold 0 φ cv P (o η e)} cc K (tlW₊ᶜ h₀) (λ k → tlW₊ᶜ (hk k))
  tlW₊ᶜ {k = zero} (gŝ () cc Iw bw ob h₀ hg)
  tlW₊ᶜ {k = suc _} {y = []} (gŝ kk () Iw bw ob h₀ hg)
  tlW₊ᶜ {k = suc _} {φ = φ} {cv = cv} {y = y ∷ ys} (gŝ {t₀ = t₀} {g = g} kk cc Iw bw ob h₀ hg) =
    ŝWᶜ {T₀ = fold 0 φ cv P t₀} {G = λ η e → fold 0 φ cv P (g η e)} cc Iw bw (λ θ → OccΣ π (ob θ)) (tlW₊ᶜ h₀) (λ θ Y hY lY nθ lt e → tlW₊ᶜ (hg θ Y hY lY nθ lt e))
  tlW₊ᶜ {k = lim _ _} {y = []} (gŝ kk () Iw bw ob h₀ hg)
  tlW₊ᶜ {k = lim _ _} {φ = φ} {cv = cv} {y = y ∷ ys} (gŝ {t₀ = t₀} {g = g} kk cc Iw bw ob h₀ hg) =
    ŝWᶜ {T₀ = fold 0 φ cv P t₀} {G = λ η e → fold 0 φ cv P (g η e)} cc Iw bw (λ θ → OccΣ π (ob θ)) (tlW₊ᶜ h₀) (λ θ Y hY lY nθ lt e → tlW₊ᶜ (hg θ Y hY lY nθ lt e))
```

## §4 地板策略、层号条件与一般层号尾巴的 W 定理

**地板策略.** `FP c φ`: 当前地板的每一项 $K$ 可忽略 (RelativeBase 的 `Ign c K`: $K\cong0$ 或 $K\preceq c$) 或 $K\cong1$. 可忽略的项在目标 $\succeq c$ 处永不成为弹栈的最大者 (RelativeBase §1), $\cong1$ 的项由帧标签 $\psi_\Omega(\cdot)$ 里的 $\Omega=\Omega_1$ 见证 (RelativeBase `FL-Ω₁`). **层号条件** `LvOK c k`: $k\sqsubseteq c+1$ 或 $k\sqsubseteq2$; 它保证 `up zero` 之后的新地板 `flo k′` 满足策略 (`FP-flo`), 并沿 `up zero`/`up (self n)` 遗传 (`LvOK-pred`/`LvOK-self`). 第 2 层尾巴 ($k=2$, 地板 `fk 1`) 对**一切** $c$ 满足两者: 这是 $\psi_\Omega(\Omega_3)$ 可标记的来源.

```agda
FP : Ordᴵ → Flr → Set
FP c φ = ∀ {K} (k : InF K φ) → IgnK c k ⊎ (K ≅ᴵ one)

FP-fz : ∀ {c} → FP c fz
FP-fz ()

FP-z : ∀ {c} → FP c (fk zero)
FP-z ink = inj₁ (inj₁ (inj₁ z≅))

FP-1 : ∀ {c} → FP c (fk one)
FP-1 ink = inj₂ (≅ᴵ-refl one)

FP-⊔ : ∀ {c a b} → FP c a → FP c b → FP c (a ⊔ b)
FP-⊔ f g (inl k) = f k
FP-⊔ f g (inr k) = g k

IgnL→FP : ∀ {c φ} → IgnL c φ → FP c φ
IgnL→FP g k = inj₁ (g k)

data Low : Ordᴵ → Set where
  lw0 : Low zero
  lw1 : Low one
  lw2 : Low two

LvOK : Ordᴵ → Ordᴵ → Set
LvOK c k = (k ⊑ᴵ suc c) ⊎ Low k

FP-flo′ : ∀ {c k} → LvOK c k → FP c (flo k)
FP-flo′ {k = k} (inj₁ le) = IgnL→FP (floIgn k le)
FP-flo′ (inj₂ lw0) ()
FP-flo′ (inj₂ lw1) ink = inj₁ (inj₁ (inj₁ z≅))
FP-flo′ (inj₂ lw2) ink = inj₂ (≅ᴵ-refl one)

LvOK-pred : ∀ {c k′} → LvOK c (suc k′) → LvOK c k′
LvOK-pred (inj₁ le) = inj₁ (⊑ᴵ-trans (≼→⊑ (s⊑s→≼ le)) (⊑-suc _))
LvOK-pred (inj₂ lw1) = inj₂ lw0
LvOK-pred (inj₂ lw2) = inj₂ lw1

FP-flo : ∀ {c k′} → LvOK c (suc k′) → FP c (flo k′)
FP-flo lv = FP-flo′ (LvOK-pred lv)

LvOK-self : ∀ {c f s} → LvOK c (lim f s) → ∀ n → LvOK c (f n)
LvOK-self (inj₁ le) n = inj₁ (⊑ᴵ-trans (Sim→⊑ᴵ (λ q → lim n q)) le)
LvOK-self (inj₂ ()) n

FP→FP : ∀ {c c′ φ} → Up c c′ → FP c φ → FP c′ φ
FP→FP u f k with f k
... | inj₁ (inj₁ (inj₁ e0)) = inj₁ (inj₁ (inj₁ e0))
... | inj₁ (inj₁ (inj₂ kc)) = inj₁ (inj₁ (inj₂ (≼-trans kc u)))
... | inj₁ (inj₂ (b , le)) = inj₁ (inj₂ (b , ⊑ᴵ-trans le (sB u)))
... | inj₂ e1 = inj₂ e1
```

**帧的静态地板标签 `FlrLabΩ`.** 帧 $E$ (标签 $\zeta$) 的地板项要么平凡, 要么被一个在**一切**帧标签 $\psi_\Omega(\zeta+b)$ 里出现的带 `Idx` 下标支配 (见证与 $b$ 无关, 这是弹栈行 `Ob` 所需). 它同时覆盖 Uniform2 的静态 `FlrLab φ ζ` (下标出现在 $\zeta$ 里, 经 `od`) 与 $\Omega_1$ 的出现 (`os oh`).

```agda
FlrLabΩ : Flr → T → Set
FlrLabΩ φ ζ = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ Σ T λ w → Σ (Idx w) λ Iw → ((K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw)) ×
                                                              (∀ b → Occ w (ψᵗ Ωᵗ (ζ ++ b) ∷ []))

FlrLab→Ω : ∀ {φ ζ} → FlrLab φ ζ → FlrLabΩ φ ζ
FlrLab→Ω F k with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ b → od (OccPre b o))

FlrLabΩ-⊔ : ∀ {a b ζ} → FlrLabΩ a ζ → FlrLabΩ b ζ → FlrLabΩ (a ⊔ b) ζ
FlrLabΩ-⊔ F G (inl k) = F k
FlrLabΩ-⊔ F G (inr k) = G k

FlrLabΩ-ext : ∀ {φ ζ} y → FlrLabΩ φ ζ → FlrLabΩ φ (ζ ++ y)
FlrLabΩ-ext {ζ = ζ} y F k with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ b → subst (λ u → Occ w (ψᵗ Ωᵗ u ∷ [])) (sym (++-assoc ζ y b)) (o (y ++ b)))

-- K ≅ 1 is witnessed by Ω₁ inside every ψ_Ω(…)
wit1 : ∀ {K} → K ≅ᴵ one → Σ T λ w → Σ (Idx w) λ Iw → ((K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw)) × (∀ b → Occ w (ψᵗ Ωᵗ b ∷ []))
wit1 e = natT 1 , I₁ , inj₂ e , (λ b → os oh)

FP₀ : Flr → Set
FP₀ φ = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ (K ≅ᴵ one)

FP₀→FP : ∀ {φ} → FP₀ φ → FP zero φ
FP₀→FP f k with f k
... | inj₁ e0 = inj₁ (inj₁ (inj₁ e0))
... | inj₂ e1 = inj₂ e1

FP→FlrLabΩ : ∀ {φ ζ} → FP₀ φ → FlrLabΩ φ ζ
FP→FlrLabΩ f k with f k
... | inj₁ e0 = inj₁ e0
... | inj₂ e1 with wit1 e1
...   | w , Iw , kw , o = inj₂ (w , Iw , kw , λ b → o _)

occ-hd : ∀ {w x xs} → Occ w (x ∷ []) → Occ w (x ∷ xs)
occ-hd oh = oh
occ-hd (od o) = od o
occ-hd (os o) = os o
occ-hd (oτ t) = oτ t
occ-hd (ot ())

FlrLab[]-mono : ∀ {c φ ps qs} → (∀ {w} → Occ w ps → Occ w qs) → FlrLab[ c ] φ ps → FlrLab[ c ] φ qs
FlrLab[]-mono f F k with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , f o)

FlrLab[]-⊔ : ∀ {c fl φ π x} → FlrLab[ c ] fl π → FlrLab[ c ] φ x → FlrLab[ c ] (fl ⊔ φ) (π ++ x)
FlrLab[]-⊔ {x = x} F G (inl k) = FlrLab[]-mono (OccPre x) F k
FlrLab[]-⊔ {π = π} F G (inr k) = FlrLab[]-mono (OccΣ π) G k

-- the copies' floor (frame floor ⊔ tail floor) is labelled in every copy label
FP-rep : ∀ {c flE φ ζ b} → FlrLabΩ flE ζ → FP c φ → ∀ m → FlrLab[ c ] (flE ⊔ φ) (replicate (suc m) (ψᵗ Ωᵗ (ζ ++ b)))
FP-rep {b = b} FE f m (inl k) with FE k
... | inj₁ e = inj₁ (inj₁ (inj₁ e))
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , occ-hd (o b))
FP-rep FE f m (inr k) with f k
... | inj₁ g = inj₁ g
... | inj₂ e1 with wit1 e1
...   | w , Iw , kw , o = inj₂ (w , Iw , kw , occ-hd (o _))
```

**好帧记录.** `GA1ᴴ E ζ`: 静态地板标签 `FlrLabΩ`, 依目标的 W (底的地板标签与标签都依目标), 目标 0 对层对齐的好底 `GA0ᴬ`, 帧互模拟 $\approx^\mathsf A_1$. 与 Relative 展望里的 `GA1ᴬ` 相比只把 W 的底从 `LW` 改成 `LW[ c ]`, 并把静态标签改为 `FlrLabΩ`.

```agda
GWᶜ : ∀ {φ} → Ordᴵ → A 1 φ → T → Set
GWᶜ c F u = ∀ {fl} {P : Run fl} {π} → FlrLab[ c ] fl π → LW[ c ] P π → LW[ c ] (F P) (π ++ ψΩᵗ u)

record GA1ᴴ {φ} (E : A 1 φ) (ζ : T) : Set where
  constructor ga1ᴴ
  field
    fl1ᴴ : FlrLabΩ φ ζ
    gw1ᴴ : ∀ {c} → GWᶜ c E ζ
    g01ᴴ : ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π → L0 (E P) (π ++ ψΩᵗ ζ)
    gr1ᴴ : E ≈₁ᴬ E
open GA1ᴴ public
```

**W 定理.** 对尾巴推导递归 (Uniform2Depth1 `W1A`/`W1₁` 的一般层号版): 任意层号 $k$, 当前地板 $\varphi$ 满足策略, 层号满足条件, 则深度 1 的折叠在目标 $\succeq c$ 处带标签. 后继行的副本的地板标签由 `FP-rep`; `up zero` 行由 `FP-flo`/`LvOK-pred` 重建前提; `gi` 行的两种情形都由 `limᵢWᶜ` 处理, 分支对**一切**带标签输入用同一个前提递归 (穿透目标处输入的地板 $\preceq$ 节点层 $\prec$ 目标, 可忽略; 折叠目标处目标 $\cong$ 节点层 $\cong c$).

```agda
module WGen {flE} {E : A 1 flE} {ζ : T} (GE : GA1ᴴ E ζ) where

  copyWᶜ : ∀ {c ψ fl} {P : Run fl} {π x} {fr : A 1 ψ} → FlrLab[ c ] fl π → (∀ m → FlrLab[ c ] ψ (replicate (suc m) x)) →
           LW[ c ] P π → (∀ {fl′} {Q : Run fl′} {ρ} → FlrLab[ c ] fl′ ρ → LW[ c ] Q ρ → LW[ c ] (fr Q) (ρ ++ x ∷ [])) →
           ∀ m → LW[ c ] (repA 0 P fr m) (π ++ replicate m x)
  copyWᶜ {ψ = ψ} F Fψ hP hF zero = zWᶜ {φ = ψ} hP
  copyWᶜ F Fψ hP hF (suc zero) = hF F hP
  copyWᶜ {c = c} {π = π} {x = x} F Fψ hP hF (suc (suc m)) =
    wkLWᶜ _ (subst (λ u → LW[ c ] _ u) (snoc π (suc m) x) (hF (FlrLab[]-⊔ F (Fψ m)) (copyWᶜ F Fψ hP hF (suc m))))

  WA : ∀ {c φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → FP c φ → Lab0ᴸ t y → GWᶜ c (fold 1 φ cv E t) (ζ ++ y)
  WV : ∀ {c k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP c φ → LvOK c k → LabL t y → GWᶜ c (fold 1 φ cv E t) (ζ ++ y)
  W₊ : ∀ {c k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP c φ → LvOK c k → LabL₊ k Ll t y →
       GWᶜ c (fold 1 φ cv E t) (ζ ++ y)

  WA {c = c} {y = []} fp (lz cc) F hP = wkLWᶜ _ (subst (λ u → LW[ c ] _ (_ ++ ψΩᵗ u)) (sym (++-identityʳ ζ)) (gw1ᴴ GE F hP))
  WA {y = y ∷ ys} fp (lz cc) F hP = ⊥-elim (cof-ne y ys cc)
  WA {y = []} fp (ls () l) F hP
  WA {c = c} {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y ∷ ys} fp (ls cc l) {P = P} {π = π} F hP =
    limWᶜ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → repA 0 P (fold 1 φ cv E a) m} (c1Ω ζ cc)
          (λ m → subst (λ u → LW[ c ] _ (π ++ u)) (sym (repW Ωᵗ ζ y ys cc m))
                       (copyWᶜ F (FP-rep (fl1ᴴ GE) fp) hP (WA fp l) m))
  WA {y = []} fp (ll () h) F hP
  WA {c = c} {φ = φ} {cv = cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} fp (ll cc h) {P = P} {π = π} F hP =
    limWᶜ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → fold 1 φ cv E (G m) P} (cωΩ ζ cc)
          (λ n → subst (λ u → LW[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc n)) (WA fp (h n) F hP))
  WA {y = []} fp (lŝ₀ () K h₀ hk) F hP
  WA {c = c} {φ = φ} {cv = cv} {y = y ∷ ys} fp (lŝ₀ {t₀ = t₀} {g = g} cc K h₀ hk) {P = P} {π = π} F hP =
    ĉWᶜ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E t₀ P} {O = λ η e → fold 1 φ cv E (g η e) P}
        (cωΩ ζ cc) K (subst (λ u → LW[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc 0)) (WA fp h₀ F hP))
        (λ k → subst (λ u → LW[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc (suc k))) (WA fp (hk k) F hP))
  WA {y = []} fp (lĉ () K h₀ hk) F hP
  WA {c = c} {φ = φ} {cv = cv} {y = y ∷ ys} fp (lĉ {o₀ = o₀} {o = o} cc K h₀ hk) {P = P} {π = π} F hP =
    ĉWᶜ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E o₀ P} {O = λ η e → fold 1 φ cv E (o η e) P}
        (cωΩ ζ cc) K (subst (λ u → LW[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc 0)) (WA fp h₀ F hP))
        (λ k → subst (λ u → LW[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc (suc k))) (WA fp (hk k) F hP))

  WV {k = zero}    fp lv at = WA fp (atomL at)
  WV {k = suc _}   fp lv h  = W₊ fp lv h
  WV {k = lim _ _} fp lv h  = W₊ fp lv h

  W₊ {c = c} {y = []} fp lv (gz cc) F hP = wkLWᶜ _ (subst (λ u → LW[ c ] _ (_ ++ ψΩᵗ u)) (sym (++-identityʳ ζ)) (gw1ᴴ GE F hP))
  W₊ {y = y ∷ ys} fp lv (gz cc) F hP = ⊥-elim (cof-ne y ys cc)
  W₊ {y = []} fp lv (gs () l) F hP
  W₊ {c = c} {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y ∷ ys} fp lv (gs cc l) {P = P} {π = π} F hP =
    limWᶜ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → repA 0 P (fold 1 φ cv E a) m} (c1Ω ζ cc)
          (λ m → subst (λ u → LW[ c ] _ (π ++ u)) (sym (repW Ωᵗ ζ y ys cc m))
                       (copyWᶜ F (FP-rep (fl1ᴴ GE) fp) hP (W₊ fp lv l) m))
  W₊ {y = []} fp lv (gl () h) F hP
  W₊ {c = c} {φ = φ} {cv = cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} fp lv (gl cc h) {P = P} {π = π} F hP =
    limWᶜ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → fold 1 φ cv E (G m) P} (cωΩ ζ cc)
          (λ n → subst (λ u → LW[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc n)) (W₊ fp lv (h n) F hP))
  W₊ {k = suc k′} {cv = cv} fp lv (gu {r = zero} h) F hP ev p =
    WV {φ = flo k′} {cv = cvFlo k′} (FP-flo lv) (LvOK-pred lv) h F hP (proj₁ ev , (proj₁ (proj₂ ev) , toFlo k′ (λ q → cv (proj₂ (proj₂ ev)) (suc q)))) p
  W₊ {k = lim f s} {cv = cv} fp lv (gu {r = self n} h) F hP ev p =
    WV {φ = flo (f n)} {cv = cvFlo (f n)} (FP-flo′ (LvOK-self lv n)) (LvOK-self lv n) h F hP (proj₁ ev , (proj₁ (proj₂ ev) , toFlo (f n) (λ q → cv (proj₂ (proj₂ ev)) (lim n q)))) p
  W₊ {y = []} fp lv (gi () I ej h) F hP
  W₊ {c = c} {φ = φ} {cv = cv} {y = y ∷ ys} fp lv (gi {q = q} {f = f} cc I ej h) {P = P} {π = π} F hP =
    limᵢWᶜ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {ac = λ ev → cv (proj₂ (proj₂ ev)) q}
           {H = λ x → fold 1 φ cv E (f (intoˢ (<→◃ q) x)) P} (cΩΩ ζ cc I) I ej
           (λ η x l → subst (λ u → LW[ c ] _ (π ++ u)) (sym (penΩ ζ cc I η)) (W₊ fp lv (h η x (→Ll (<→◃ q) l)) F hP))
  W₊ {y = []} fp lv (gĉ () K h₀ hk) F hP
  W₊ {c = c} {φ = φ} {cv = cv} {y = y ∷ ys} fp lv (gĉ {o₀ = o₀} {o = o} cc K h₀ hk) {P = P} {π = π} F hP =
    ĉWᶜ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E o₀ P} {O = λ η e → fold 1 φ cv E (o η e) P}
        (cωΩ ζ cc) K (subst (λ u → LW[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc 0)) (W₊ fp lv h₀ F hP))
        (λ k → subst (λ u → LW[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc (suc k))) (W₊ fp lv (hk k) F hP))
  W₊ {k = zero} fp lv (gŝ () cc Iw bw ob h₀ hg)
  W₊ {k = suc _} {y = []} fp lv (gŝ kk () Iw bw ob h₀ hg)
  W₊ {c = c} {k = suc _} {φ = φ} {cv = cv} {y = y ∷ ys} fp lv (gŝ {w = w} {t₀ = t₀} {g = g} kk cc Iw bw ob h₀ hg) {P = P} {π = π} F hP =
    ŝWᶜ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {T₀ = fold 1 φ cv E t₀ P} {G = λ η e → fold 1 φ cv E (g η e) P}
        (cΩΩ ζ cc I0) Iw bw (λ θ → subst (λ u → Occ w (π ++ u)) (sym (penΩ ζ cc I0 θ)) (OccΣ π (od (OccΣ ζ (ob θ)))))
        (subst (λ u → LW[ c ] _ (π ++ u)) (sym (penΩ ζ cc I0 (natT 1))) (W₊ fp lv h₀ F hP))
        (λ θ Y hY lY nθ lt e → subst (λ u → LW[ c ] _ (π ++ u)) (sym (penΩ ζ cc I0 θ)) (W₊ fp lv (hg θ Y hY lY nθ lt e) F hP))
  W₊ {k = lim _ _} {y = []} fp lv (gŝ kk () Iw bw ob h₀ hg)
  W₊ {c = c} {k = lim _ _} {φ = φ} {cv = cv} {y = y ∷ ys} fp lv (gŝ {w = w} {t₀ = t₀} {g = g} kk cc Iw bw ob h₀ hg) {P = P} {π = π} F hP =
    ŝWᶜ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {T₀ = fold 1 φ cv E t₀ P} {G = λ η e → fold 1 φ cv E (g η e) P}
        (cΩΩ ζ cc I0) Iw bw (λ θ → subst (λ u → Occ w (π ++ u)) (sym (penΩ ζ cc I0 θ)) (OccΣ π (od (OccΣ ζ (ob θ)))))
        (subst (λ u → LW[ c ] _ (π ++ u)) (sym (penΩ ζ cc I0 (natT 1))) (W₊ fp lv h₀ F hP))
        (λ θ Y hY lY nθ lt e → subst (λ u → LW[ c ] _ (π ++ u)) (sym (penΩ ζ cc I0 θ)) (W₊ fp lv (hg θ Y hY lY nθ lt e) F hP))
```

**读法.** 与 Uniform2Depth1 `W1₁` 比, 多的只是两个前提沿行的重建; 少的是 `TrivF`. 停机一次通过: 递归都在尾巴推导的子项上. `gi` 行不分穿透与折叠: 两种情形里被读到的地板项都被策略覆盖 (穿透: 输入在节点层 $j\prec i$, 它的地板 $\prec j\prec i$, 在 $i$ 处可忽略; 折叠: $i\preceq j$, 由层号条件 $j\prec k\sqsubseteq c+1$ 得 $j\preceq c\preceq i\preceq j$, 一切 $\cong$, 链点的地板 $\prec j\cong c$ 可忽略; 第 2 层尾巴: 节点层 $\le1$, 地板 $\le$ `fk 0`).

## §5 $\Omega_\Omega$ 闭包的好帧

```agda
goodΩ̂₀ᴴ : GA1ᴴ (Ω̂A 0) []
goodΩ̂₀ᴴ = ga1ᴴ (FlrLab→Ω FlrLab-z) gw g01 selfΩ̂0ᴬ
  where
  gw : ∀ {c} → GWᶜ c (Ω̂A 0) []
  gw {c} {fl} {P} {π} F hP =
    cloWᵗ {t = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))} {g = λ η → fold 0 (fk η) (λ e q → e (suc q)) P (Ωˢ η)}
          (FW-popᵗ F) refl
          (TlWᶜ.tlWVᶜ hP {φ = fk zero} {cv = λ e → e} {t = Ωˢ (suc zero)} (LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _)))
          (λ θ Y hY lY nθ lt → TlWᶜ.tlWVᶜ hP {φ = fk (toLevel Y hY)} {cv = λ e q → e (suc q)} {t = Ωˢ (toLevel Y hY)}
                                                (LabL-Ω Y hY lY nθ (≅ᴵ-refl _)))
  g01 : ∀ {fl} {P : Run fl} {π} → GA0ᴬ P π → L0 (Ω̂A 0 P) (π ++ ψΩᵗ [])
  g01 GP = g0ᴬ (goodΩ̂0ᴬ GP)

goodΩ̂₀ᴬ : GA1ᴬ (Ω̂A 0) []
goodΩ̂₀ᴬ = record { fl1ᴬ = FlrLab-z ; gw1ᴬ = λ F hP → gw1ᴴ goodΩ̂₀ᴴ F (LW→LW[] hP) ; g01ᴬ = g01ᴴ goodΩ̂₀ᴴ ; gr1ᴬ = selfΩ̂0ᴬ }
```

**读法.** `goodΩ̂₀ᴬ` 居留 Relative §5 展望的 `GA1ᴬ (Ω̂A 0) []`; W 部分来自 RelativeBase 的 `cloWᵗ` 与 §3 的 `TlWᶜ`, 目标 0 部分来自 §2 的 `goodΩ̂0ᴬ`, 互模拟来自 Relative 的 `selfΩ̂0ᴬ`. 这就是任务 1 的 "把标签理论移到 $\cong^\mathsf A$ 上" 在深度 0 与 $\Omega_\Omega$ 闭包处的全部内容; 深度 1 的尾巴定理在 OmegaSqA.
