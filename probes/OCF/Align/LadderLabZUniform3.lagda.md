> **机械克隆, 验收用.** 由 `ScafLadderZUniform3` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆.** 由 `Uniform3` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 统一形 (三): 校准 (Uniform2 的移植)

> [Uniform2](Uniform2.lagda.md) 在修正的折叠上重编译. **九个标签全部成立, 证明不变** (改动 18 行, 都在 `domSrc`/`dom′` 与 `toFlo` 的参数形状). `low-pop-bound` 等 `refl` 检验也不变. 正文的 "`suc (Mx B)`" 读作 `Bd B`. 本文的条件定理 (`TΩ2-cond`、`BranchΩ`) 留作对照; 无条件的结果在 [Uniform3Full](Uniform3Full.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZUniform3 where

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
open import OCF.Align.LadderLabZPrefix using (Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ; kind; kl; kc; kz; walkˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsT; cof; pred; c1; cΩ; Ωt; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-fsn; walk; t2-NF; tO-desc-NF)
open import OCF.Align.LadderLabZPrefix using (X₂-NF)
open import OCF.Align.Symbolic using (X₂ᵗ)
open import OCF.Align.LadderLabZStage2Label using (one⁰)
open import OCF.Align.LadderLabZGoodL using (lab2; nf2; T2ᴸ; T2-label)
open import OCF.Align.LadderLabZOmegaK using (Tkᴸ; Tk-label)
open import OCF.Align.LadderLabZOmegaSq using (TΩ₂ᴸ; TΩ₂-label)
open import OCF.Align.LadderLabZNonTight using (GLΩ₂₊; TΩ₂₊-label)
open import OCF.Align.Stage2 using (Lab-uniq)
open import OCF.Align.LadderLabZOmegaSqBase using (ψ₂1ˢ)
import OCF.Align.LadderLabZTopDown as TD
open import OCF.Align.Standard using (c[]; c∷)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.Stage2 using (Ωᵗ; t2)
open import OCF.Align.LadderLabZUniformS using (_≅ˢ_; z≅; s≅; upʳ; Ωˢ-refl; Ωˢ-≅; two)
open import OCF.Align.LadderLabZDecoupleBase using (ΩΩ)
open import OCF.Align.LadderLabZDecouple using (Idx; lvI)
open import OCF.Align.LadderLabZGoodLBase using (LabL; LabL₊; Ll; Lab0ᴸ; Atomᴸ; atomL; gs; gz; gu; lab1; nf1; LabL-Ω; I0; Lab→Ctbl; Idx-Ctbl; ctbl-hd; Goodᴸ; forceᴸ; toL₊)
open import OCF.Align.LadderLabZOmegaExpBase using (OccΣ; repW; snoc)
open import OCF.Align.LadderLabZOmegaExp using (ψΩ₀; tΩ1; tΩ1-NF)
open import OCF.Align.LadderLabZOmegaKBase using (tω; tk; tω-NF; tk-NF; tΩ2; tΩ2-NF; ΠΩ; ΠΩ-rep)
open import OCF.Align.LadderLabZOmegaSqBase using (Ω₂; Ω₂+1; low-NF)
open import OCF.Align.LadderLabZOmegaSq using (tΩ₂; tΩ₂-NF)
open import OCF.Align.LadderLabZNonTightBase using (I₁; I₂)
open import OCF.Align.LadderLabZUniform3Base
open import OCF.Align.LadderLabZUniform3Depth1
```

## §1 第 2 层指数尾巴: $\psi_\Omega(\Omega_2)$ 与 $\psi_\Omega(\Omega_2+1)$

Uniform3Base §11 的深度 1 定理只收地板平凡 (第 0、1 层) 的尾巴. 第 2 层的尾巴地板是 `fk 1`, 非平凡: 后继行的副本以它为地板 (需要见证), 互模拟要层对齐. 对 $\Omega_2$ 与 $\Omega_2+1$ 两者都直接成立: $\Omega_2$ 的分支一律是 `up zero x` ($x$ 在第 1 层, 地板回到平凡), 自互模拟 `Ωˢ-refl two` 的层对齐由 `lowA` 在分支处给出 (`alΩ₂`); $\Omega_2+1$ 的后继步两侧地板都是 `fk 1`, 见证是下标 $2$ 在帧标签 $\psi_\Omega(\zeta+\Omega_2)$ 里的出现. 这是 NonTightBase 的 `WE₂`/`ZE₂`/`GoodE₂`/`repGood₂`/`ZE₂₊` 在统一形上的对应, 证明只用 Uniform3Base 的行引理与 `Depth1` 的副本引理.

```agda
LW≡π : ∀ {φ} (R : Run φ) π {u v} → u ≡ v → LW R (π ++ u) → LW R (π ++ v)
LW≡π R π refl h = h

TL0 : TrivLeaf (fk zero)
TL0 = inj₂ (zero , refl , z≅)

fl₂ : FlrLab (fk (suc zero)) Ω₂
fl₂ ink = inj₂ (natT 2 , I₂ , inj₁ (via (≅ᴵ-refl _) zero) , oh)

alΩ₂ : AlignD (fk (suc zero)) (fk (suc zero)) (Ωˢ-refl two)
alΩ₂ x y r = lowA (inj₂ refl) (inj₂ refl) TL0 TL0 r

module Lv2 {flE} {E : A 1 flE} {ζ : T} (GE : GA1 E ζ) where
  open Depth1 GE

  FrΩ₂ : A 1 (flE ⊔ fk (suc zero))
  FrΩ₂ = fold 1 (fk (suc zero)) (cvFlo two) E (Ωˢ two)

  wΩ₂ : GW1 FrΩ₂ (ζ ++ Ω₂)
  wΩ₂ {fl} {P} {π} F hP =
    limᵢW {φ = fl ⊔ (flE ⊔ fk (suc zero))} {ps = π} {y = ψᵗ Ωᵗ (ζ ++ Ω₂)} {ys = []} {ac = λ ev → proj₂ (proj₂ ev) zero}
          {H = λ x → fold 1 (fk (suc zero)) (cvFlo two) E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P}
          (cΩΩ ζ refl I₁) I₁ (≅ᴵ-refl _)
          (λ η x l → subst (λ u → LW _ (π ++ u)) (sym (penΩ ζ refl I₁ η))
                           (wkLW {φ = fl ⊔ (flE ⊔ fk zero)} (λ {L} (ev : Ev L (fl ⊔ (flE ⊔ fk (suc zero)))) → proj₁ ev , (proj₁ (proj₂ ev) , toFlo (suc zero) (λ q → proj₂ (proj₂ ev) (suc q))))
                                 (W1₁ {φ = fk zero} {cv = cvFlo (suc zero)} TrivF-z l F hP)))

  leΩ₂ : ∀ {fl L} → Ev L (fl ⊔ (flE ⊔ fk (suc zero))) → Ev L (fl ⊔ (flE ⊔ fk zero))
  leΩ₂ ev = proj₁ ev , (proj₁ (proj₂ ev) , toFlo (suc zero) (λ q → proj₂ (proj₂ ev) (suc q)))

  oΩ₂ : ∀ {fl} {P : Run fl} {π} → GA0 P π → L0 (FrΩ₂ P) (π ++ ψΩᵗ (ζ ++ Ω₂))
  oΩ₂ {fl} {P} {π} GP =
    limᵢ0 {φ = fl ⊔ (flE ⊔ fk (suc zero))} {ps = π} {y = ψᵗ Ωᵗ (ζ ++ Ω₂)} {ys = []} {ac = λ ev → proj₂ (proj₂ ev) zero}
          {H = λ x → fold 1 (fk (suc zero)) (cvFlo two) E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P}
          (cΩΩ ζ refl I₁) I₁ (≅ᴵ-refl _)
          (λ η x l → subst (λ u → LW _ (π ++ u)) (sym (penΩ ζ refl I₁ η))
                           (wkLW {φ = fl ⊔ (flE ⊔ fk zero)} leΩ₂ (W1₁ {φ = fk zero} {cv = cvFlo (suc zero)} TrivF-z l (proj₁ GP) (gW (proj₂ GP)))))
          (λ η x l xx → L0≡π (fold 1 (fk (suc zero)) (cvFlo two) E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P) π (sym (penΩ ζ refl I₁ η))
                          (wkL0 {φ = fl ⊔ (flE ⊔ fk zero)} {R = fold 1 (fk zero) (cvFlo (suc zero)) E (intoˢ (<→◃ zero) x) P} leΩ₂ (O1₁ {φ = fk zero} {cv = cvFlo (suc zero)} TL0 l xx GP)) ,
                        wkR leΩ₂ leΩ₂ (fold-≅1 {φ = fk zero} {φ′ = fk zero} {cv = cvFlo (suc zero)} {cv′ = cvFlo (suc zero)}
                                               (∼ᶠ-refl flE) (gr1 GE) xx (lowA (inj₂ refl) (inj₂ refl) TL0 TL0 xx)
                                               (∼ᶠ-refl fl) (gR (proj₂ GP))))

  FullΩ₂ : GA1 FrΩ₂ (ζ ++ Ω₂)
  FullΩ₂ = ga1 (FlrLab-⊔ (fl1 GE) fl₂) wΩ₂
               (λ {fl} GP → gr (wΩ₂ (proj₁ GP) (gW (proj₂ GP))) (oΩ₂ GP)
                               (fold-≅1 (∼ᶠ-refl flE) (gr1 GE) (Ωˢ-refl two) alΩ₂ (∼ᶠ-refl fl) (gR (proj₂ GP))))
               (fold-≅1 (∼ᶠ-refl flE) (gr1 GE) (Ωˢ-refl two) alΩ₂)
```

**$\psi_\Omega(\Omega_2+1)$.** 后继行: 第 $m$ 份副本是 `repA 0 P FrΩ₂ m`, 第 $m\ge2$ 份的底的地板 `fk 1` 由下标 $2$ 在 $\psi_\Omega(\zeta+\Omega_2)$ 里的出现见证 (`FL₂`); 互模拟的后继步两侧地板相同 (`fk∼`).

```agda
  FL₂ : ∀ m → FlrLab (flE ⊔ fk (suc zero)) (replicate (suc m) (ψᵗ Ωᵗ (ζ ++ Ω₂)))
  FL₂ m (inl k) = FlrLab-mono (λ o → od (OccPre Ω₂ o)) (fl1 GE) k
  FL₂ m (inr ink) = inj₂ (natT 2 , I₂ , inj₁ (via (≅ᴵ-refl _) zero) , od (OccΣ ζ oh))

  FrΩ₂₊ : A 1 (flE ⊔ fk (suc zero))
  FrΩ₂₊ = fold 1 (fk (suc zero)) (cvFlo two) E (Ord₊ˢ.suc (Ωˢ two))

  FullΩ₂₊ : GA1 FrΩ₂₊ (ζ ++ Ω₂+1)
  FullΩ₂₊ =
    ga1 (FlrLab-⊔ (fl1 GE) (λ { ink → inj₂ (natT 2 , I₂ , inj₁ (via (≅ᴵ-refl _) zero) , oh) }))
        (λ {fl} {P} {π} F hP →
           limW {ps = π} {y = ψᵗ Ωᵗ (ζ ++ Ω₂+1)} {ys = []} {F = λ m → repA 0 P FrΩ₂ m} (c1Ω ζ refl)
                (λ m → LW≡π (repA 0 P FrΩ₂ m) π (sym (repW Ωᵗ ζ (ψᵗ (natT 2) []) (𝟏 ∷ []) refl m))
                             (copyW F FL₂ hP (gw1 FullΩ₂) m)))
        (λ {fl} {P} {π} GP →
           gr (limW {ps = π} {y = ψᵗ Ωᵗ (ζ ++ Ω₂+1)} {ys = []} {F = λ m → repA 0 P FrΩ₂ m} (c1Ω ζ refl)
                    (λ m → LW≡π (repA 0 P FrΩ₂ m) π (sym (repW Ωᵗ ζ (ψᵗ (natT 2) []) (𝟏 ∷ []) refl m))
                                 (copyW (proj₁ GP) FL₂ (gW (proj₂ GP)) (gw1 FullΩ₂) m)))
              (lim0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ Ω₂+1)} {ys = []} {F = λ m → repA 0 P FrΩ₂ m} (c1Ω ζ refl)
                    (λ m → L0≡π (repA 0 P FrΩ₂ m) π (sym (repW Ωᵗ ζ (ψᵗ (natT 2) []) (𝟏 ∷ []) refl m))
                                (g0 (copyGR GP FL₂ (gv1 FullΩ₂) m))))
              (fold-≅1 (∼ᶠ-refl flE) (gr1 GE) (s≅ (Ωˢ-refl two)) (fk∼ (≅ᴵ-refl _) , alΩ₂) (∼ᶠ-refl fl) (gR (proj₂ GP))))
        (fold-≅1 (∼ᶠ-refl flE) (gr1 GE) (s≅ (Ωˢ-refl two)) (fk∼ (≅ᴵ-refl _) , alΩ₂))
```

**读法.** 与 NonTightBase 相比, 不需要 `raise`、把手 `Hd`、`FWR`、W 版的单独移植: 第 2 层尾巴的地板 `fk 1` 只在两处出现, 静态标签 (`fl₂`, `FL₂`: 下标 $2$ 出现在 $\Omega_2$ 里) 与互模拟的后继步 (`fk∼`). 分支一律回到第 1 层, 由 Uniform3Base 的 `W1₁`/`O1₁` 处理.

## §2 符号项层面的好性 (深度 0 与 1)

`GS0 X x`: 深度 0 上把好前缀 $(P,\pi)$ 变成好前缀 $(X\,0\,P,\ \pi+x)$; `GS1 X x`: 深度 1 上把好的指数前缀 $(E,\zeta)$ 变成 $(X\,1\,E,\ \zeta+x)$. TopDown 的 `GoodSym` 是对一切深度的合取; 这里只到深度 1 (理由见 §7). 弱化 (`wk`) 只重排证据, 好性随之搬运; 地板标签沿 `InF` 的重排搬运.

```agda
GS0 : ∀ {φ} → Sym φ → T → Set
GS0 X x = ∀ {fl} {P : Run fl} {π} → GA0 P π → GA0 (X 0 P) (π ++ x)

GS1 : ∀ {φ} → Sym φ → T → Set
GS1 X x = ∀ {fl} {E : A 1 fl} {ζ} → GA1 E ζ → GA1 (X 1 E) (ζ ++ x)

FlrLab-re : ∀ {φ φ′ ps} → (∀ {K} → InF K φ′ → InF K φ) → FlrLab φ ps → FlrLab φ′ ps
FlrLab-re f F k = F (f k)

wkGA1 : ∀ {φ ψ} {E : A 1 φ} {ζ} (le : ∀ {L} → Ev L ψ → Ev L φ) → (∀ {K} → InF K ψ → InF K φ) →
        GA1 E ζ → GA1 (wk 1 le E) ζ
wkGA1 {φ} {ψ} {E} le f G =
  ga1 (FlrLab-re f (fl1 G))
      (λ {fl} F hP → wkLW {φ = fl ⊔ φ} {ψ = fl ⊔ ψ} (λ ev → proj₁ ev , le (proj₂ ev)) (gw1 G F hP))
      (λ {fl} GP → wkGR {φ = fl ⊔ φ} {ψ = fl ⊔ ψ} (λ ev → proj₁ ev , le (proj₂ ev)) (gv1 G GP))
      (λ s H → wkR (λ ev → proj₁ ev , le (proj₂ ev)) (λ ev → proj₁ ev , le (proj₂ ev)) (gr1 G s H))

GA1≡ : ∀ {φ} {E : A 1 φ} {ζ ζ′} → ζ ≡ ζ′ → GA1 E ζ → GA1 E ζ′
GA1≡ refl G = G

GA0≡ : ∀ {φ} {P : Run φ} {π π′} → π ≡ π′ → GA0 P π → GA0 P π′
GA0≡ refl G = G

good∅ᴿ : GA0 ∅ᴿ []
good∅ᴿ = FlrLab-fz ,
         gr (λ { ev p (Y , hY , lY , nY) ei ki → toL₊ ki (LabL-Ω Y hY lY nY ei) })
            (λ ev p nf → gs gz , l1 refl (s≅ z≅) (l0 refl z≅))
            (λ ev p ev′ p′ ei → Ωˢ-≅ ei)

good∅0 : GS0 ∅ᵀ []
good∅0 {fl} {P} {π} (F , GP) =
  FlrLab-⊔ F FlrLab-fz , wkGR {φ = fl} {ψ = fl ⊔ fz} proj₁ (subst (GR P) (sym (++-identityʳ π)) GP)

good∅1 : GS1 ∅ᵀ []
good∅1 {fl} {E} {ζ} G = GA1≡ (sym (++-identityʳ ζ)) (wkGA1 proj₁ (λ { (inl k) → k ; (inr ()) }) G)

reassoc : ∀ {a b c K} → InF K (a ⊔ (b ⊔ c)) → InF K ((a ⊔ b) ⊔ c)
reassoc (inl k)       = inl (inl k)
reassoc (inr (inl k)) = inl (inr k)
reassoc (inr (inr k)) = inr k

reassoc′ : ∀ {a b c K} → InF K ((a ⊔ b) ⊔ c) → InF K (a ⊔ (b ⊔ c))
reassoc′ (inl (inl k)) = inl k
reassoc′ (inl (inr k)) = inr (inl k)
reassoc′ (inr k)       = inr (inr k)

good⊕0 : ∀ {φ ψ} {X : Sym φ} {Y : Sym ψ} {x y} → GS0 X x → GS0 Y y → GS0 (X ⊕ Y) (x ++ y)
good⊕0 {φ} {ψ} {X} {Y} {x} {y} GX GY {fl} {P} {π} GP with GY (GX GP)
... | F , G = GA0≡ (++-assoc π x y)
               (FlrLab-re reassoc F , wkGR {φ = (fl ⊔ φ) ⊔ ψ} {ψ = fl ⊔ (φ ⊔ ψ)} (λ { (u , (v , w)) → (u , v) , w }) G)

good⊕1 : ∀ {φ ψ} {X : Sym φ} {Y : Sym ψ} {x y} → GS1 X x → GS1 Y y → GS1 (X ⊕ Y) (x ++ y)
good⊕1 {x = x} {y = y} GX GY {ζ = ζ} G =
  GA1≡ (++-assoc ζ x y) (wkGA1 (λ { (u , (v , w)) → (u , v) , w }) reassoc (GY (GX G)))

goodΨ0 : ∀ {φ} {Y : Sym φ} {y} → GS1 Y y → GS0 (Ψ Y) (ψΩᵗ y)
goodΨ0 {Y = Y} GY {fl} {P} {π} (F , GP) =
  FlrLab-⊔ F (FlrLab-mono (λ o → od o) (fl1 G)) , gv1 G (F , GP)
  where G = GY goodΩ̂₀
```

**尾巴.** 深度 0 上一切带标签的尾巴都好 (`tlGR`), 只要地板的静态标签 (它成为后续弹栈的底时才用). 深度 1 上, 本文证得的尾巴是 `TlOK`: 第 0、1 层 (地板平凡, Uniform3Base §11) 与第 2 层的 $\Omega_2$、$\Omega_2+1$ (§1).

```agda
data TlOK : ∀ {k} → Ordˢ k → T → Set where
  tlow0 : ∀ {t : Ordˢ zero} {y} → LabL t y → TlOK t y
  tlow1 : ∀ {t : Ordˢ (suc zero)} {y} → LabL₊ (suc zero) Ll t y → t ≅ˢ t → TlOK t y
  tOΩ₂  : TlOK (Ωˢ two) Ω₂
  tOΩ₂₊ : TlOK (Ord₊ˢ.suc (Ωˢ two)) Ω₂+1

goodTl0 : ∀ {k} {t : Ordˢ k} {y} → LabL t y → t ≅ˢ t → FlrLab (flo k) y → GS0 (tlᵀ (flo k) (cvFlo k) t) y
goodTl0 l ex Fl (F , GP) = FlrLab-⊔ F Fl , tlGR GP l ex

goodTl1 : ∀ {k} {t : Ordˢ k} {y} → TlOK t y → GS1 (tlᵀ (flo k) (cvFlo k) t) y
goodTl1 (tlow0 l)     G = Depth1.FullA G (inj₁ refl) (atomL l) (proj₁ l)
goodTl1 (tlow1 l ex)  G = Depth1.Full₁ G TL0 l ex
goodTl1 tOΩ₂          G = Lv2.FullΩ₂ G
goodTl1 tOΩ₂₊         G = Lv2.FullΩ₂₊ G
```

**读法.** `goodTl1` 的 `TlOK` 前提就是 TopDown `goodTl` 在深度 1 缺的那部分: 地板非平凡的一般尾巴要 §6 的 (a′)(b′).

## §3 表示、主标签定理与调整后的期望记录

`Rep`: Ψ 嵌套至多一层的符号项 (外层可有任意尾巴, Ψ 的指数是 `RepΨ`: 零、和、深度 1 上已证的尾巴). 主定理 `label` 与 TopDown `Derived.label` 同形: 计值树 `ψᵀ X ev z` 在一切环境与地板证据下带证书与标签 $\psi_0(x)$ (`NF₁` 下).

```agda
data RepΨ : ∀ {φ} → Sym φ → T → Set where
  e∅  : RepΨ ∅ᵀ []
  e⊕  : ∀ {φ ψ} {X : Sym φ} {Y : Sym ψ} {x y} → RepΨ X x → RepΨ Y y → RepΨ (X ⊕ Y) (x ++ y)
  etl : ∀ {k} {t : Ordˢ k} {y} → TlOK t y → RepΨ (tlᵀ (flo k) (cvFlo k) t) y

data Rep : ∀ {φ} → Sym φ → T → Set where
  r∅  : Rep ∅ᵀ []
  r⊕  : ∀ {φ ψ} {X : Sym φ} {Y : Sym ψ} {x y} → Rep X x → Rep Y y → Rep (X ⊕ Y) (x ++ y)
  rΨ  : ∀ {φ} {Y : Sym φ} {y} → RepΨ Y y → Rep (Ψ Y) (ψΩᵗ y)
  rtl : ∀ {k} {t : Ordˢ k} {y} → LabL t y → t ≅ˢ t → FlrLab (flo k) y → Rep (tlᵀ (flo k) (cvFlo k) t) y

repΨ→GS1 : ∀ {φ} {X : Sym φ} {x} → RepΨ X x → GS1 X x
repΨ→GS1 e∅         = good∅1
repΨ→GS1 (e⊕ r r′)  = good⊕1 (repΨ→GS1 r) (repΨ→GS1 r′)
repΨ→GS1 (etl o)    = goodTl1 o

rep→GS0 : ∀ {φ} {X : Sym φ} {x} → Rep X x → GS0 X x
rep→GS0 r∅          = good∅0
rep→GS0 (r⊕ r r′)   = good⊕0 (rep→GS0 r) (rep→GS0 r′)
rep→GS0 (rΨ r)      = goodΨ0 (repΨ→GS1 r)
rep→GS0 (rtl l ex F) = goodTl0 l ex F

label : ∀ {φ} {X : Sym φ} {x} → Rep X x → NF₁ (ψ₀ᵗ x) → ∀ {ℓ} (ev : Ev ℓ (fz ⊔ φ)) (z : zero <ᴵ ℓ) →
        Lab₀ (ψᵀ X ev z) (ψ₀ᵗ x)
label r nf ev z = g0 (proj₂ (rep→GS0 r good∅ᴿ)) ev z nf
```

**统一支配引理 `dom′`.** TopDown 的 `dom` 在字面界下的形式: 弹栈的界 `suc (Mx B)` 被目标自己的下标或前缀中出现的某个下标支配. (§7 的闭包行里它以 `pickW`/`domC` 的形式被用到.)

```agda
domSrc : ∀ {φ ps i ℓ w₀} (B : Top i ℓ φ) (I₀ : Idx w₀) → i ≅ᴵ lvI I₀ → FlrLab φ ps →
         Σ T λ w → Σ (Idx w) λ Iw → (Bd B ⊑ᴵ suc (lvI Iw)) × (Occ w ps ⊎ w ≡ w₀)
domSrc {φ = φ} {ps = ps} {w₀ = w₀} B I₀ ei F =
  Pick.pw Pk , Pick.pI Pk , ubd B (≼→≺s (≼-trans (inj₂ ei) (Pick.pc Pk))) (λ k → dem k (pd (Pick.pF Pk k))) , Pick.pP Pk
  where
  wit : ∀ {K} → (K ≅ᴵ zero) ⊎ (Σ T λ w → Σ (Idx w) λ Iw → (K ≼ lvI Iw) × Occ w ps) →
        (K ≅ᴵ zero) ⊎ (Σ T λ w → Σ (Idx w) λ Iw → (K ≼ lvI Iw) × (Occ w ps ⊎ w ≡ w₀))
  wit (inj₁ k0) = inj₁ k0
  wit (inj₂ (w , Iw , kw , o)) = inj₂ (w , Iw , kw , inj₁ o)
  Pk : Pick (λ w → Occ w ps ⊎ w ≡ w₀) φ Tr0 (lvI I₀)
  Pk = pickMax φ Tr0 (λ k → wit (F k)) I₀ (inj₂ refl) (inj₂ (≅ᴵ-refl _))
  pd : ∀ {K} → (K ≅ᴵ zero) ⊎ (K ≼ lvI (Pick.pI Pk)) → (K ≺ᴵ suc (lvI (Pick.pI Pk))) ⊎ (K ≅ᴵ zero)
  pd (inj₁ k0) = inj₂ k0
  pd (inj₂ kw) = inj₁ (≼→≺s kw)

record Expected′ : Set₁ where
  field
    good∅ᴿ′ : GA0 ∅ᴿ []
    good∅′  : GS0 ∅ᵀ [] × GS1 ∅ᵀ []
    good⊕′  : ∀ {φ ψ} {X : Sym φ} {Y : Sym ψ} {x y} →
              (GS0 X x → GS0 Y y → GS0 (X ⊕ Y) (x ++ y)) × (GS1 X x → GS1 Y y → GS1 (X ⊕ Y) (x ++ y))
    goodΩ̂′  : GA1 (Ω̂A 0) []
    goodTl′ : (∀ {k} {t : Ordˢ k} {y} → LabL t y → t ≅ˢ t → FlrLab (flo k) y → GS0 (tlᵀ (flo k) (cvFlo k) t) y) ×
              (∀ {k} {t : Ordˢ k} {y} → TlOK t y → GS1 (tlᵀ (flo k) (cvFlo k) t) y)
    dom′    : ∀ {φ ps i ℓ w₀} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (I₀ : Idx w₀) → i ≅ᴵ lvI I₀ → FlrLab φ ps →
              Σ T λ w → Σ (Idx w) λ Iw → (Bd (bound φ ev p) ⊑ᴵ suc (lvI Iw)) × (Occ w ps ⊎ w ≡ w₀)

expected′ : Expected′
expected′ = record
  { good∅ᴿ′ = good∅ᴿ
  ; good∅′  = good∅0 , good∅1
  ; good⊕′  = good⊕0 , good⊕1
  ; goodΩ̂′  = goodΩ̂₀
  ; goodTl′ = goodTl0 , goodTl1
  ; dom′    = λ ev p I₀ ei F → domSrc (bound _ ev p) I₀ ei F
  }
```

## §4 校准: 自下而上的标签在统一树上重证

每条都是 `label` 对一个 `Rep` 的实例, 对一切环境层号与地板证据成立 (自下而上的定理只在一个固定的环境上). 标准形由已有的 `NF₁` 引理给出 (StandardOmega 的 `t2-NF`、Prefix 的 `X₂-NF`、OmegaKBase 的 `tk-NF`/`tω-NF`、OmegaExp 的 `tΩ1-NF`、OmegaSq 的 `tΩ₂-NF`、OmegaSqBase 的 `low-NF`); 可数指数 $\eta$ 的情形与 OmegaExp 的 `Tη-label` 一样以 `NF₁ (ψΩ₀ η)` 为唯一前提.

```agda
one₀ : Ordˢ zero
one₀ = Ord₊ˢ.suc Ord₊ˢ.zero

lab-one₀ : LabL one₀ (natT 1)
lab-one₀ = s≅ z≅ , gs gz , lab1

LΩ1 : LabL (Ωˢ (suc zero)) (Ωt (natT 1))
LΩ1 = LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _)

LΩ2 : LabL (Ωˢ two) (Ωt (natT 2))
LΩ2 = LabL-Ω (natᶜ 2) (natᶜ-HS 2) lab2 nf2 (≅ᴵ-refl _)

Ω̂ᵀ : Sym (fk zero ⊔ fz)
Ω̂ᵀ = Ψ ∅ᵀ

-- ψ₀(Ω_Ω+1), ψ₀(Ω_Ω+Ω), ψ₀(Ω_Ω+Ω₂)
R-p1 : Rep (Ω̂ᵀ ⊕ tlᵀ (flo zero) (cvFlo zero) one₀) (ΩΩ ∷ 𝟏 ∷ [])
R-p1 = r⊕ (rΨ e∅) (rtl lab-one₀ (s≅ z≅) FlrLab-fz)

R-pΩ : Rep (Ω̂ᵀ ⊕ tlᵀ (flo (suc zero)) (cvFlo (suc zero)) (Ωˢ (suc zero))) (ΩΩ ∷ Ωt (natT 1))
R-pΩ = r⊕ (rΨ e∅) (rtl LΩ1 (Ωˢ-refl _) FlrLab-z)

R-pΩ₂ : Rep (Ω̂ᵀ ⊕ tlᵀ (flo two) (cvFlo two) (Ωˢ two)) (ΩΩ ∷ Ωt (natT 2))
R-pΩ₂ = r⊕ (rΨ e∅) (rtl LΩ2 (Ωˢ-refl _) fl₂)

nf-p1 : NF₁ (ψ₀ᵗ (ΩΩ ∷ 𝟏 ∷ []))
nf-p1 = NF₁-fsn (NF₁-fsn t2-NF refl 0) refl 0

nf-pΩ : NF₁ (ψ₀ᵗ (ΩΩ ∷ Ωt (natT 1)))
nf-pΩ = NF₁-fsn t2-NF refl 0

p1-label : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ω̂ᵀ ⊕ tlᵀ (flo zero) (cvFlo zero) one₀) ev z) (ψ₀ᵗ (ΩΩ ∷ 𝟏 ∷ []))
p1-label = label R-p1 nf-p1

pΩ-label : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ω̂ᵀ ⊕ tlᵀ (flo (suc zero)) (cvFlo (suc zero)) (Ωˢ (suc zero))) ev z) (ψ₀ᵗ (ΩΩ ∷ Ωt (natT 1)))
pΩ-label = label R-pΩ nf-pΩ

pΩ₂-label : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ω̂ᵀ ⊕ tlᵀ (flo two) (cvFlo two) (Ωˢ two)) ev z) X₂ᵗ
pΩ₂-label = label R-pΩ₂ X₂-NF

-- ψ₀(Ω_Ω·k) for all k, ψ₀(Ω_Ω·2)
ΨK : ℕ → Σ Flr Sym
ΨK zero    = fz , ∅ᵀ
ΨK (suc k) = _ , Ω̂ᵀ ⊕ proj₂ (ΨK k)

R-k : ∀ k → Rep (proj₂ (ΨK k)) (ΠΩ k [])
R-k zero    = r∅
R-k (suc k) = r⊕ (rΨ e∅) (R-k k)

Tk-label′ : ∀ k {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (proj₂ (ΨK k)) ev z) (tk k)
Tk-label′ k = label (R-k k) (tk-NF k)

T2-label′ : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ω̂ᵀ ⊕ Ω̂ᵀ) ev z) t2
T2-label′ = label (r⊕ (rΨ e∅) (rΨ e∅)) t2-NF

-- ψ₀(Ω_Ω·ω), ψ₀(Ω_Ω·ω^η) (η 第 0 层), ψ₀(Ω_Ω·Ω), 第 1 层指数
Tω-label′ : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (tlᵀ (flo zero) (cvFlo zero) one₀)) ev z) tω
Tω-label′ = label (rΨ (etl (tlow0 lab-one₀))) tω-NF

Tη-label′ : ∀ {t : Ordˢ zero} {η} → LabL t η → NF₁ (ψΩ₀ η) →
            ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (tlᵀ (flo zero) (cvFlo zero) t)) ev z) (ψΩ₀ η)
Tη-label′ l nf = label (rΨ (etl (tlow0 l))) nf

Tη₁-label : ∀ {t : Ordˢ (suc zero)} {η} → LabL₊ (suc zero) Ll t η → t ≅ˢ t → NF₁ (ψΩ₀ η) →
            ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (tlᵀ (flo (suc zero)) (cvFlo (suc zero)) t)) ev z) (ψΩ₀ η)
Tη₁-label l ex nf = label (rΨ (etl (tlow1 l ex))) nf

TΩ1-label : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (tlᵀ (flo (suc zero)) (cvFlo (suc zero)) (Ωˢ (suc zero)))) ev z) tΩ1
TΩ1-label = Tη₁-label LΩ1 (Ωˢ-refl _) tΩ1-NF

-- ψ₀(Ω_Ω·Ω₂), ψ₀(Ω_Ω·Ω₂·ω)
TΩ₂-label′ : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (tlᵀ (flo two) (cvFlo two) (Ωˢ two))) ev z) tΩ₂
TΩ₂-label′ = label (rΨ (etl tOΩ₂)) tΩ₂-NF

TΩ₂₊-label′ : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (tlᵀ (flo two) (cvFlo two) (Ord₊ˢ.suc (Ωˢ two)))) ev z) (ψΩ₀ Ω₂+1)
TΩ₂₊-label′ = label (rΨ (etl tOΩ₂₊)) low-NF
```

**读法.** 九条校准全部经同一个 `label`, 没有逐例的栈或帧; 新树上它们对**一切**环境层号与证据成立. 第 1 层指数 (`Tη₁-label`) 在自下而上里只有链点 $\psi_0(\Omega_\Omega\cdot\Omega)$ 一处 (`TΩ2-0-label`), 这里是一般定理.

## §5 与自下而上的树一致, 决定性检验

**一致 (模 $\cong$).** 同一标签的两棵计值树 $\cong$ (`Lab-uniq`), 所以统一树与自下而上的树在计值后一致: 下面对 GoodL 的 `T2ᴸ`、OmegaK 的 `Tkᴸ`、OmegaSq 的 `TΩ₂ᴸ`、NonTight 的 $\psi_0(\Omega_\Omega\cdot\Omega_2\cdot\omega)$ 树逐一给出. 字面 `refl` 不可能 (TopDown §7 检验 5 的理由: 抽象 $\eta$ 下停在不同的函数上).

```agda
agree-T2 : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → forceᴸ _ (proj₁ (T2-label′ ev z)) ≅ T2ᴸ
agree-T2 ev z = Lab-uniq (proj₂ (T2-label′ ev z)) T2-label

agree-Tk : ∀ k {ℓ} ev (z : zero <ᴵ ℓ) → forceᴸ _ (proj₁ (Tk-label′ k ev z)) ≅ Tkᴸ k
agree-Tk k ev z = Lab-uniq (proj₂ (Tk-label′ k ev z)) (Tk-label k)

agree-TΩ₂ : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → forceᴸ _ (proj₁ (TΩ₂-label′ ev z)) ≅ TΩ₂ᴸ
agree-TΩ₂ ev z = Lab-uniq (proj₂ (TΩ₂-label′ ev z)) TΩ₂-label

agree-TΩ₂₊ : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → forceᴸ _ (proj₁ (TΩ₂₊-label′ ev z)) ≅ forceᴸ _ (proj₁ GLΩ₂₊)
agree-TΩ₂₊ ev z = Lab-uniq (proj₂ (TΩ₂₊-label′ ev z)) TΩ₂₊-label
```

**读法.** 一致都是模 $\cong$ 的 (计值后), 不需要树之间的互模拟.

**决定性检验 (`refl`).** TopDown §7 的检验在调整后的定义上重做. 界现在是 `suc (Mx B)`: 地板全 $\preceq$ 目标时字面是 `suc i` (检验 1 的 `kc one`), `low-pop` 处是 `suc 1 = two` (地板 1 是最大者; TopDown 那里是 `Mlev 1 2`). 低目标点 $[2,0,0]$ 是真极限 (`kl`).

```agda
one : Ordᴵ
one = suc zero

three : Ordᴵ
three = suc two

T2ᵀ : Ordˢ zero
T2ᵀ = ψᵀ (Ω̂ᵀ ⊕ Ω̂ᵀ) {i = zero} {ℓ = one} (tt , (((λ q → q) , tt) , ((λ q → q) , tt))) zero

_ : kind T2ᵀ ≡ kc one
_ = refl
_ : kind (walkˢ T2ᵀ (0 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ T2ᵀ (0 ∷ 0 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ T2ᵀ (0 ∷ 0 ∷ 1 ∷ [])) ≡ kc one
_ = refl

lowᵀ : Ordˢ zero
lowᵀ = ψᵀ (Ψ (tlᵀ (flo two) (cvFlo two) ψ₂1ˢ)) {i = zero} {ℓ = three} (tt , ((λ q → suc (suc q)) , (λ q → suc q))) (suc (suc zero))

low-tree″ : kind (walkˢ lowᵀ (2 ∷ 0 ∷ 0 ∷ [])) ≡ kl
low-tree″ = refl

popᵀ : Ordˢ zero
popᵀ = walkˢ lowᵀ (2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ [])

low-pop-bound : TD.bndOf popᵀ ≡ two
low-pop-bound = refl

_ : kind (walkˢ popᵀ (0 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ popᵀ (0 ∷ 0 ∷ 1 ∷ 0 ∷ [])) ≡ kl
_ = refl
```

**读法.** `low-pop-bound`: 低目标弹栈的界字面是 `two` (TopDown: `Mlev 1 2`, NonTight: `F ≅ 2`), 首点之下第 2 层帧的指数沿第 1 层链折叠 (`kl`), 不需要 `Simᴵ 2 1`.

## §6 $\psi_0(\Omega_\Omega^2)$: 统一形下的归约与精确停点

**归约.** $\psi_0(\Omega_\Omega^2)=\psi_0(\psi_\Omega(\Omega_\Omega))$ 的树是 `ψᵀ (Ψ (Ψ ∅ᵀ))`: 深度 1 上的 $\Omega_\Omega$ 闭包作用于指数前缀 `Ω̂A 0`. 深度 1 的闭包定理 `goodΩ̂₁` 在统一形下**一次写出, 对一切好指数前缀**: 第 0 点是第 1 层尾巴 $\Omega_1$ 的深度 1 折叠 (Uniform3Base `Full₁`), 地板见证由前缀与指数前缀的静态标签 (`fwΩ`), 界与支配由 Uniform3Base §7 的 `cloW`/`clo0`/`cloR`. 剩下的只有分支: 每个带标签的 $\theta$ 处的帧 $\psi_\Omega(\zeta+\Omega_\theta)$ (尾巴 $\Omega_\eta$, $\eta=\mathtt{lvl}\,Y$, 地板 `fk η`) 的好性与分支间的互模拟, 打包成 `BranchΩ`. 这就是 OmegaSq/NonTight 的 `BranchΩ`/`BranchΩᶠ` 在统一形上的样子, 但现在它是**唯一**的缺口: 闭包、界、支配、第 0 点都已是定理.

```agda
record BranchΩ {flE} (E : A 1 flE) (ζ : T) : Set where
  field
    bW : ∀ θ Y (hY : HS Y) → Lab Y θ → NF₁ θ →
         GW1 (fold 1 (fk (toLevel Y hY)) (λ e q → e (suc q)) E (Ωˢ (toLevel Y hY))) (ζ ++ Ωt θ)
    bV : ∀ θ Y (hY : HS Y) → Lab Y θ → NF₁ θ →
         GV1 (fold 1 (fk (toLevel Y hY)) (λ e q → e (suc q)) E (Ωˢ (toLevel Y hY))) (ζ ++ Ωt θ)
    bR : ∀ η η′ → η ≅ᴵ η′ → fold 1 (fk η) (λ e q → e (suc q)) E (Ωˢ η) ≈₁ fold 1 (fk η′) (λ e q → e (suc q)) E (Ωˢ η′)
open BranchΩ public

module DepthOneΩ {flE} {E : A 1 flE} {ζ : T} (GE : GA1 E ζ) (Br : BranchΩ E ζ) where
  T₁ : A 1 (flE ⊔ fk zero)
  T₁ = fold 1 (fk zero) (λ e → e) E (Ωˢ (suc zero))
  Gη : (η : Ordᴵ) → A 1 (flE ⊔ fk η)
  Gη η = fold 1 (fk η) (λ e q → e (suc q)) E (Ωˢ η)
  F1 : GA1 T₁ (ζ ++ Ωt (natT 1))
  F1 = Depth1.Full₁ GE TL0 LΩ1 (Ωˢ-refl _)

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
  fwΩ {π = π} F (inl (inr k)) with fl1 GE k
  ... | inj₁ e = inj₁ e
  ... | inj₂ (w , Iw , kw , o) =
    inj₂ (w , Iw , kw , λ θ → subst (λ u → Occ w (π ++ u)) (sym (pen θ)) (OccΣ π (od (OccPre (Ωt θ) o))))

  inner : ∀ {fl} → Run fl → Run ((fl ⊔ flE) ⊔ fk zero)
  inner P = cloA 0 (wk 0 r (T₁ P)) (λ η → wk 0 rη (Gη η P))

  wΩ : GW1 (Ω̂A 1 E) (ζ ++ ΩΩ ∷ [])
  wΩ {fl} {P} {π} F hP =
    wkLW r′ (cloW {φ = fl ⊔ flE} {ps = π} {y = y₀} {ys = []} {t = wk 0 r (T₁ P)} {g = λ η → wk 0 rη (Gη η P)} (fwΩ F) cs
                  (LW≡π (wk 0 r (T₁ P)) π (sym (pen (natT 1))) (wkLW r (gw1 F1 F hP)))
                  (λ θ Y hY lY nθ lt → LW≡π (wk 0 rη (Gη (toLevel Y hY) P)) π (sym (pen θ)) (wkLW rη (bW Br θ Y hY lY nθ F hP))))

  vΩ : GV1 (Ω̂A 1 E) (ζ ++ ΩΩ ∷ [])
  vΩ {fl} {P} {π} GP =
    wkGR r′ (gr (cloW {φ = fl ⊔ flE} {ps = π} {y = y₀} {ys = []} {t = wk 0 r (T₁ P)} {g = λ η → wk 0 rη (Gη η P)} (fwΩ (proj₁ GP)) cs
                      (LW≡π (wk 0 r (T₁ P)) π (sym (pen (natT 1))) (wkLW r (gW (gv1 F1 GP))))
                      (λ θ Y hY lY nθ lt → LW≡π (wk 0 rη (Gη (toLevel Y hY) P)) π (sym (pen θ)) (wkLW rη (gW (bV Br θ Y hY lY nθ GP)))))
                (clo0 {φ = fl ⊔ flE} {ps = π} {y = y₀} {ys = []} {t = wk 0 r (T₁ P)} {g = λ η → wk 0 rη (Gη η P)} (fwΩ (proj₁ GP)) cs
                      (L0≡π′ (wk 0 r (T₁ P)) π (sym (pen (natT 1))) (wkL0 r (g0 (gv1 F1 GP))))
                      (λ θ Y hY lY nθ lt → L0≡π′ (wk 0 rη (Gη (toLevel Y hY) P)) π (sym (pen θ)) (wkL0 rη (g0 (bV Br θ Y hY lY nθ GP)))))
                (cloR {t = wk 0 r (T₁ P)} {g = λ η → wk 0 rη (Gη η P)} {t′ = wk 0 r (T₁ P)} {g′ = λ η → wk 0 rη (Gη η P)}
                      (∼ᶠ-refl _) (wkR r r (gR (gv1 F1 GP)))
                      (λ η η′ eη → wkR rη rη (bR Br η η′ eη (∼ᶠ-refl fl) (gR (proj₂ GP))))))
    where
    L0≡π′ : ∀ {φ} (R : Run φ) π′ {u v} → u ≡ v → L0 R (π′ ++ u) → L0 R (π′ ++ v)
    L0≡π′ R π′ refl h = h

  goodΩ̂₁ : GA1 (Ω̂A 1 E) (ζ ++ ΩΩ ∷ [])
  goodΩ̂₁ = ga1 (FlrLab-⊔ (fl1 GE) FlrLab-z) wΩ vΩ
               (λ {fl} {fl′} {P} {P′} s H →
                  wkR r′ r′ (cloR {t = wk 0 r (T₁ P)} {g = λ η → wk 0 rη (Gη η P)}
                                  {t′ = wk 0 r (T₁ P′)} {g′ = λ η → wk 0 rη (Gη η P′)}
                                  (⊔∼ s (∼ᶠ-refl flE)) (wkR r r (gr1 F1 s H)) (λ η η′ eη → wkR rη rη (bR Br η η′ eη s H))))
```

**条件定理.** 由 `BranchΩ` 在指数前缀 $\Omega_\Omega$ 处成立, $\psi_0(\Omega_\Omega^2)$ 的树带证书与标签 (对一切环境与证据).

```agda
TΩ2-cond : BranchΩ (Ω̂A 0) [] → ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (Ψ ∅ᵀ)) ev z) tΩ2
TΩ2-cond Br ev z = g0 (gv1 GΨ good∅ᴿ) ev z tΩ2-NF
  where
  GΨ : GA1 (Ψ ∅ᵀ 1 (Ω̂A 0)) (ψΩᵗ [])
  GΨ = wkGA1 {φ = fk zero ⊔ fk zero} {ψ = fk zero ⊔ (fk zero ⊔ fz)} (λ { (u , v) → u , proj₁ v }) (λ { (inl k) → inl k ; (inr (inl k)) → inr k ; (inr (inr ())) })
             (DepthOneΩ.goodΩ̂₁ goodΩ̂₀ Br)
```

**读法.** `TΩ2-cond` 的证明三行: 深度 1 的闭包定理作用于好指数前缀 `Ω̂A 0` (`goodΩ̂₀`), 再在深度 0 取空前缀的目标 0 标签.

**精确停点.** `BranchΩ` 要的是第 $\eta$ 层尾巴 $\Omega_\eta$ 的深度 1 折叠定理, $\eta$ 取一切带标签的层号 (闭包证书的链点层号是巨大的序数, `gŝ` 行对一切 $\theta>1$ 量化). 本文的深度 1 定理覆盖 $\eta\le2$: $\eta\le1$ 由 Uniform3Base `Full₁`/`FullA` (地板平凡), $\eta=2$ 的同类论证是 §1 (`alΩ₂`). 第一个失败点是 $\eta=3$, 即分支 $\psi_0(\psi_\Omega(\Omega_3))$: $\Omega_3$ 的分支是 `up zero x` ($x$ 在第 2 层, 地板 `flo 2 = fk 1`), 而 `gi` 行对**一切**相关的输入对 $x\cong^\mathsf s y$ 量化. 取 $x=1$ (第 2 层自带的后继) 与 $y=$ `up zero (up zero 1)`, 两者 $\cong^\mathsf s$, 但折叠后的后继步一侧地板 `fk 1` (非平凡)、另一侧 `fz`, 层对齐不成立 (编译):

```agda
noFkz : fk (suc zero) ∼ᶠ fz → ⊥
noFkz (kz∼ ())

x₃ y₃ : Ordˢ two
x₃ = Ord₊ˢ.suc Ord₊ˢ.zero
y₃ = Ord₊ˢ.up zero (Ord₊ˢ.up zero one₀)

r₃ : x₃ ≅ˢ y₃
r₃ = upʳ (upʳ (s≅ z≅))

¬AlignΩ₃ : AlignD (fk two) (fk two) (Ωˢ-refl three) → ⊥
¬AlignΩ₃ al = noFkz (proj₁ (al x₃ y₃ r₃))
```



**读法.** 这不是证明技巧的问题而是陈述的问题: 在目标 $0$ 处这两棵分支树确实不互模拟 (左侧的副本以 `fk 1` 为底的地板, 弹栈界为 $2$; 右侧为 $1$). 但 $\Omega_3$ 的折叠在目标 $0$ 处沿第 2 层的链走, 只在**链点**处计值分支; 在目标 $\ge3$ 处穿透, 分支的地板 $\le1$ 低于目标, 界都是紧的 $i+1$. 所以真正成立的是**依目标的**互模拟与依目标的地板见证: 计值在目标 $i$ 处时, 一切弹栈的目标都 $\succeq i$ (派发只升目标: 穿透保持 $i$, 折叠的链点在节点层 $\succeq i$), 于是 $\preceq i$ 的地板项永不被读到. 缺的两条引理因此是:

- (a′) 依目标的地板见证: `GA` 的静态 `FlrLab` 换成 "在目标 $i$ 处, 地板中 $\succ i$ 的项被见证"; 后继行的副本的见证在 $\eta\ge4$ 处才真正需要 (第 3 层输入的地板 `fk 2`; 帧标签 $\psi_\Omega(\ldots)$ 里的 $\Omega=\Omega_1$ 本身含下标 $1$, 只见证 $\le1$).
- (b′) 依目标的层对齐互模拟: `≈ᴿ` 只在 "目标 $\succ$ 输入层" (穿透) 或 "输入是链点" (折叠) 的情形下要求分支相关. `limᵢR` 的前提要相应地分两半, 与 `limᵢ0` 的前提已分成 `LW`/`H0` 两半同理.

两条都只改证明里的量化范围, 不改树. 在它们之下 `BranchΩ` 对一切 $\eta$ 由 Uniform3Base §11 的同一递归给出, `TΩ2-cond` 成为无条件定理. 本文没有写它们.

## §7 对比表: 自下而上与统一形

| 内容 | 自下而上 (文件: 名字) | 统一形 (本文与 Uniform3Base) |
|---|---|---|
| 栈 | `Stk`/`Stkᶠ φ` (OmegaExpBase, NonTightBase) | `A d φ` 前缀塔, `Run φ = A 0 φ` |
| 帧 | `▹Ω̂`, `▹ω X`, `▹[ s ∣ hp ] X`, `▹⟨ρ∣s∣hp⟩`, `▹Ω̂²ᶠ` | 一个 `Ψ` |
| 指数折叠 | `ψᵉ`/`ψᵉ′`/`ψᵉᶠ` + `rep`/`repᶠ`/`repᴿ`, 把手 `Hd`, `raise` | `fold (suc d)` + `repA` (第一份在旧地板上) |
| 地板 | 记录 `Flr` (B/F), 推帧时 `raise` 比较 | 语法和 `Flr`, 弹栈时 `bound` 比较 |
| 非紧弹栈 | `popI`/`popF`/`popΩ` (两种界) | `cloA` 一种: 界 `suc (Mx B)`, 环境 `Mlev (Fc B) (suc η)` |
| 带前缀标签 | `PreW`/`Pre0` (每个栈类型一份: OmegaExpBase, NonTightBase §5) | 行引理 `…W`/`…0`/`…R` 一次 (Uniform3Base §7), 尾巴递归 `TlW`/`Tl0` |
| $\Omega_\Omega$ 闭包 | `GoodΩ`, `GoodΩᶠ` + `FW` + `domP` | `goodΩ̂0` (深度 0), `goodΩ̂₁` (深度 1, 以 `BranchΩ` 为前提) |
| 指数尾巴 | `GoodE`/`repGood`, `WE₀`/`ZE₀`/`WE₁`/`ZE₁`/`GoodE₀`/`GoodE₁`, `WE₂`/`ZE₂`/`GoodE₂`/`repGood₂`/`ZE₂₊` | `FullA`/`Full₁` (一个互递归), `FullΩ₂`/`FullΩ₂₊` |
| 互模拟 | `ψˢ-≅`, `ψᵉ0-≅`/`rep-≈`, `ψᵉᶠ-≅` (只到第 1 层) | `fold-≅0` (一切层), `fold-≅1` + `AlignD` (层对齐的前提显式化) |
| 支配 | `domᴸ`, `domS`, `domP` | `domP` (出现在 `ps ++ fsT …` 任意处), `domC`, `dom′` |

**行数** (只数 ```agda 块内非空行; 用户的四层口径, 只给 "布劳威尔树 EBO 第一阶段" 一列中与本次相关的格; 证书与标签在 `Goodᴸ` 体制下由同一递归造出, 层 3、4 合并为一格):

| 层 | 自下而上 (到 $\psi_0(\Omega_\Omega\cdot\Omega_2\cdot\omega)$ 实际在用的一叠) | 统一形 (本次) |
|---|---|---|
| 共享底座 (不变) | Prefix §2 约 65 + GoodLBase §1–§9 约 550 (含 §3 记号侧 75) | 同左, 原样导入 |
| 1 定义增量 | NonTightBase §1 36 (+ OmegaExpBase 的 `Stk` 与帧) | Uniform3Base §2/§3/§5: 127 (塔、构造器、字面界、符号项) |
| 2 + 折叠 | NonTightBase §2 116 (另有 OmegaExpBase §2 49、OmegaSqBase §2 29 两代已被取代的折叠) | Uniform3Base §4: 33 |
| 3–4 证书与标签 | GoodLBase §10–§12 401 + OmegaExpBase §1 63 + OmegaSqBase §4–§7 326 + NonTightBase §4–§9 974 + 定理文件 (GoodL 107, OmegaExp 167, OmegaSq 129, NonTight 126) 529 ≈ 2290 (历次移植合计: 再加 OmegaKBase 575、OmegaK 135、OmegaExpBase §3–§6 560 ≈ 3500) | Uniform3Base §6–§11 788 + Uniform2 §1–§3 166 + 校准 §4 54 ≈ 1010 |

不计: Uniform3Base §1 的否定 (23)、Uniform2 §5 的一致与 `refl` 检验 (34)、§6 的条件定理与反例 (78).

## §8 结论与边界

**校准 (任务 3, 决定性).** 下列标签在统一树上是**无条件定理**, 每条都是 `label` 对一个 `Rep` 的实例, 且对一切环境层号与地板证据成立:

| 序数 | 定理 | 自下而上的对应 |
|---|---|---|
| $\psi_0(\Omega_\Omega+1)$ | `p1-label` | GoodL/Stage2 的 `χ1`、`ts` 一族 |
| $\psi_0(\Omega_\Omega+\Omega)$ | `pΩ-label` | 同上 |
| $\psi_0(\Omega_\Omega+\Omega_2)$ | `pΩ₂-label` | Decouple `X₂-label` |
| $\psi_0(\Omega_\Omega\cdot2)$ | `T2-label′` | GoodL `T2-label` (`agree-T2`) |
| $\psi_0(\Omega_\Omega\cdot k)$, 一切 $k$ | `Tk-label′` | OmegaK `Tk-label` (`agree-Tk`) |
| $\psi_0(\Omega_\Omega\cdot\omega)$ | `Tω-label′` | OmegaK `Tω-label` |
| $\psi_0(\Omega_\Omega\cdot\omega^\eta)$, 一切带标签的第 0 层 $\eta$ | `Tη-label′` (前提 `NF₁ (ψΩ₀ η)`, 与 OmegaExp `Tη-label` 同) | OmegaExp `Tη-label` |
| $\psi_0(\Omega_\Omega\cdot\omega^\eta)$, 第 1 层 $\eta$ (新) | `Tη₁-label`; 实例 $\psi_0(\Omega_\Omega\cdot\Omega)$: `TΩ1-label` | OmegaExp 只有 `TΩ2-0-label` 这一点 |
| $\psi_0(\Omega_\Omega\cdot\Omega_2)$ | `TΩ₂-label′` | OmegaSq `TΩ₂-label` (`agree-TΩ₂`) |
| $\psi_0(\Omega_\Omega\cdot\Omega_2\cdot\omega)$ | `TΩ₂₊-label′` | NonTight `TΩ₂₊-label` (`agree-TΩ₂₊`) |

**$\psi_0(\Omega_\Omega^2)$ (任务 4).** 未得. 状态: `TΩ2-cond : BranchΩ (Ω̂A 0) [] → …` 是定理, 深度 1 的闭包 (`goodΩ̂₁`) 对一切好指数前缀已证, 唯一前提是分支帧 $\psi_\Omega(\Omega_\theta)$ 的好性与分支互模拟. 精确停点: 深度 1, 尾巴 $\Omega_\eta$ ($\eta=\mathtt{lvl}\,Y$, 地板 `fk η`), 第一个失败层号 $\eta=3$, 即分支 $\psi_0(\psi_\Omega(\Omega_3))$; `gi` 行 (节点层 2) 的路径 `up zero x` 上, 相关输入对 $x=1$ (第 2 层自带后继) 与 $y=$ `up zero (up zero 1)` 的层对齐前提 `AlignD (fk 2) (fk 2) (Ωˢ-refl three)` 为假 (`¬AlignΩ₃`, 编译). 缺的两条引理 (§6): (a′) 依目标的地板见证 ($\eta\ge4$ 起真正需要: 第 3 层输入的地板 `fk 2`), (b′) 依目标的层对齐互模拟 ($\eta\ge3$). 在统一形上它们都是 "量化范围" 的修改: 地板与帧都已统一, 派发只升目标, 所以 $\preceq$ 目标的地板项与穿透分支里的伪输入永不被读到.

**边界.** 字面 `refl` 只有树种类与界的检验; 标签都模 $\cong$. `label` 只收 Ψ 嵌套至多一层的 `Rep` (嵌套两层就是 `TΩ2-cond`). 不改 `src/`、`archive/` 与任何已有文件; README 未更新 (按指示不改已有文件).
