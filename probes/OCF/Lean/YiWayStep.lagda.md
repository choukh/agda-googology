# 产出端折叠: ψ₀(Ω_Ω·2) ≼ `T⁺ʷᵖ` 归约到一条单步比较 (条件)

验收文件. 编译定理 `irr₀` (目标层 0 上折叠的值不依赖 `S`, 派发与外层标注, 只依赖树与 `Pv`), `χ₁-topᵖ`, `χ₁-d1ᵖ`; 条件定理 `T2≼ᴳᵖ : Stepᵖ → GL.T2ᴸ ≼ NA.read T⁺ʷᵖ`, [YiDlVStep](YiDlVStep.lagda.md) 搬到 [YiProdFold](YiProdFold.lagda.md). `Stepᵖ` 未证, 也未否定 (未走通).
外层观察 `Fo` 与内层折叠 `gk₁ᵖ` 在燃料搜索的折叠上定义性相同, 这里只到 `≅` (`Fo≅gk`), 由 `irr₀` 给出. 只是下界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWayStep where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Maybe.Base using (nothing)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (R; lev; succ; psum; chain)
open import OCF.Lean.YiLamFold using (Lw; w0; ws; wl; wΩ; Pk)
open import OCF.Lean.YiZipWay using (Way′; keep′; fold′; Ψn′; ΨN′; ΩT′)
open import OCF.Lean.YiZipFold using (rootZ)
open import OCF.Lean.YiCtxAnn using (noM; noP; sucM; sucP; mS; mL; mE; mB; pS; pL; pM; pB; CpA; cmpe₀)
open import OCF.Lean.YiProdArith using (NE-plus; plusA-weak; plusA-cp)
open import OCF.Lean.YiProdFold using (sub₂; Xm; Ψs; Ψᵖ; ptsΩ; Φ; NE-Φ; chT; chP; T⁺ʷᵖ)
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiWayOne using
  ( V2; Sp; p₀; S₀; x₀; πT; gK′; πc; Fo; gk₁ᵖ; dᵖ; X₀; gm₀′; G₀; GK₃; eᵖ; topΦ; cpInd; up≼; btbo-gen
  ; module Ctx )
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; ≼l; l≼)
open import OCF.Align.Correspond using (Lab)
import OCF.Align.Stage2 as S2
import OCF.Align.GoodL as GL
open Pk
```

## 1 目标层 0 上的折叠只依赖树与 `Pv`

`E₀`: 第 0 层的两棵树逐构造子相同 (极限处逐项). 目标层 0 没有位置, 派发结果都是 `fold′`.

```agda
data E₀ : R → R → Set where
  ez : E₀ G.zero G.zero
  es : ∀ {a b} → E₀ a b → E₀ (G.suc a) (G.suc b)
  el : ∀ {f g} → (∀ n → E₀ (f n) (g n)) → E₀ (G.lim f) (G.lim g)
  et : E₀ G.top G.top

read₀≅ : ∀ {a b} → E₀ a b → NA.read a L.≅ NA.read b
read₀≅ ez = L.z≅
read₀≅ (es e) = L.s≅ (read₀≅ e)
read₀≅ (el e) = L.l≅ (λ n → read₀≅ (e n))
read₀≅ et = L.s≅ L.z≅

plusE : ∀ {x x′ a a′} → E₀ x x′ → E₀ a a′ → E₀ (plus zero x a) (plus zero x′ a′)
plusE xe ez = xe
plusE xe (es e) = es (plusE xe e)
plusE xe (el e) = el (λ n → plusE xe (e n))
plusE xe et = es xe

psumE : ∀ {h h′} → (∀ n → E₀ (h n) (h′ n)) → ∀ n → E₀ (psum zero h n) (psum zero h′ n)
psumE e zero = e zero
psumE e (suc n) = plusE (psumE e n) (e (suc n))

sacE : ∀ {y y′} → E₀ y y′ → ∀ n → E₀ (acc (λ _ z → plus zero y z) y n) (acc (λ _ z → plus zero y′ z) y′ n)
sacE e zero = e
sacE e (suc n) = plusE e (sacE e n)

succE : ∀ {y y′} → E₀ y y′ → E₀ (succ zero y) (succ zero y′)
succE e = el (sacE e)

ΨnE : ∀ j (w w′ : Way′ zero j) gm gm′ gk → (∀ ζ → E₀ (gm ζ) (gm′ ζ)) → E₀ (Ψn′ zero j w gm gk) (Ψn′ zero j w′ gm′ gk)
ΨnE j (keep′ () t) w′ gm gm′ gk h
ΨnE j fold′ (keep′ () t) gm gm′ gk h
ΨnE j fold′ fold′ gm gm′ gk h = el (λ n → h (chain j gk n))

ΨNE : ∀ k r (w w′ : Way′ zero (lev k r)) gm gm′ gk → (∀ ζ → E₀ (gm ζ) (gm′ ζ)) →
  E₀ (ΨN′ zero k r w gm gk) (ΨN′ zero k r w′ gm′ gk)
ΨNE zero ()
ΨNE (suc k) (inj₁ _) = ΨnE k
ΨNE (suc k) (inj₂ r) = ΨNE k r
ΨNE (lim f) (n , r) = ΨNE (f n) r
ΨNE (lc j g) (η , _ , r) = ΨNE (g η) r

ΨsE : ∀ j (w w′ : Way′ zero j) gm gm′ c cp → (∀ η ρ → E₀ (gm η ρ) (gm′ η ρ)) →
  E₀ (Ψs zero j w gm c cp) (Ψs zero j w′ gm′ c cp)
ΨsE j (keep′ () t) w′ gm gm′ c cp h
ΨsE j fold′ (keep′ () t) gm gm′ c cp h
ΨsE j fold′ fold′ gm gm′ c cp h = el (λ n → h (c n) (cp n))

ΩTE : ∀ j (u u′ : Way′ zero j) K K′ o o′ → (∀ n → E₀ (o n) (o′ n)) → E₀ (ΩT′ zero j u K o) (ΩT′ zero j u′ K′ o′)
ΩTE j (keep′ () t) u′ K K′ o o′ h
ΩTE j fold′ (keep′ () t) K K′ o o′ h
ΩTE j fold′ fold′ K K′ o o′ h = el h

irr₀ : ∀ {k} (V : Lw k) S S′ (x : Xm zero k S) (x′ : Xm zero k S′) t μ μ′ π →
  E₀ (Ψᵖ zero V S x t μ π) (Ψᵖ zero V S′ x′ t μ′ π)
irr₀ V S S′ x x′ G.zero μ μ′ π = et
irr₀ V S S′ x x′ (G.suc a) μ μ′ π = succE (irr₀ V S S′ x x′ a (mS μ) (mS μ′) (pS π))
irr₀ V S S′ x x′ (G.lim f) μ μ′ π = el (λ n → irr₀ V S S′ x x′ (f n) (mL μ n) (mL μ′ n) (pL π n))
irr₀ {k} V S S′ x x′ (G.lc r g) μ μ′ π =
  ΨNE k r (x r (mE μ)) (x′ r (mE μ′)) _ _ _ (λ ζ → irr₀ V S S′ x x′ (g ζ) (mB μ ζ) (mB μ′ ζ) (pB π ζ))
irr₀ w0 S S′ x x′ (G.em () a) μ μ′ π
irr₀ (ws V) S S′ x x′ (G.em _ a) μ μ′ π =
  irr₀ V (λ r → S (inj₂ r)) (λ r → S′ (inj₂ r)) (λ r → x (inj₂ r)) (λ r → x′ (inj₂ r)) a noM noM noP
irr₀ (wl V st) S S′ x x′ (G.em n a) μ μ′ π =
  irr₀ (V n) (λ r → S (n , r)) (λ r → S′ (n , r)) (λ r → x (n , r)) (λ r → x′ (n , r)) a noM noM noP
irr₀ (wΩ V w) S S′ x x′ (G.em (η , l) a) μ μ′ π =
  irr₀ (V η l) (λ r → S (η , l , r)) (λ r → S′ (η , l , r)) (λ r → x (η , l , r)) (λ r → x′ (η , l , r)) a noM noM noP
irr₀ w0 S S′ x x′ G.top μ μ′ π = succE et
irr₀ {suc k} (ws V) S S′ x x′ G.top μ μ′ π =
  ΨsE k (x (inj₁ tt) nothing) (x′ (inj₁ tt) nothing) _ _ (chT k V) (chP k V)
    (λ η ρ → irr₀ V (λ r → S (inj₂ r)) (λ r → S′ (inj₂ r)) (λ r → x (inj₂ r)) (λ r → x′ (inj₂ r)) η noM noM ρ)
irr₀ (wl V st) S S′ x x′ G.top μ μ′ π =
  el (psumE (λ n → irr₀ (V n) (λ r → S (n , r)) (λ r → S′ (n , r)) (λ r → x (n , r)) (λ r → x′ (n , r)) G.top noM noM noP))
irr₀ (wΩ {k} {g} V w) S S′ x x′ G.top μ μ′ π =
  ΩTE k (rootZ zero k g w (λ r → x r nothing)) (rootZ zero k g w (λ r → x′ r nothing)) _ _ _ _
    (psumE (λ n → irr₀ (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n)))
      (λ r → S (co (ptsΩ k g V n) , lw (ptsΩ k g V n) , r)) (λ r → S′ (co (ptsΩ k g V n) , lw (ptsΩ k g V n) , r))
      (λ r → x (co (ptsΩ k g V n) , lw (ptsΩ k g V n) , r)) (λ r → x′ (co (ptsΩ k g V n) , lw (ptsΩ k g V n) , r))
      G.top noM noM noP))

Fo≅gk : ∀ ζ → NA.read (Fo ζ) L.≅ NA.read (gk₁ᵖ ζ)
Fo≅gk ζ = read₀≅ (irr₀ V2 S₀ Sp x₀ (cmpe₀ p₀) (gK′ ζ) noM (pM πc ζ) (pB πc ζ))
```

## 2 第 0 支: 根结点 `gK′ top` 的内层链

```agda
hz₀ : ∀ ζ → CpA Sp (G.top , noM , noP) (G₀ ζ) (pM (pB πc G.top) ζ) (pB (pB πc G.top) ζ)
hz₀ ζ = plusA-weak noM noP (gm₀′ ζ) (pM (πT G.top) ζ) (pB (πT G.top) ζ) (NE-Φ w0 (sub₂ X₀) ζ)

hs₀ : ∀ a → CpA Sp (G.suc (G₀ a) , sucM (pM (pB πc G.top) a) , sucP (pB (pB πc G.top) a))
  (G₀ (G.suc a)) (pM (pB πc G.top) (G.suc a)) (pB (pB πc G.top) (G.suc a))
hs₀ a = inj₂ (1 , plusA-cp noM noP (plus (tw 2) (gm₀′ a) (gm₀′ a)) _ _
  (NE-plus (gm₀′ a) (NE-Φ w0 (sub₂ X₀) a) (NE-Φ w0 (sub₂ X₀) a))
  (plusA-cp (pM (πT G.top) a) (pB (πT G.top) a) (gm₀′ a) _ _ (NE-Φ w0 (sub₂ X₀) a)
    (proj₂ (proj₂ (cpInd (topΦ (tw 2) w0 (sub₂ X₀) a) _ _)))))

ht₀ : CpA Sp (G.suc (G₀ G.zero) , sucM (pM (pB πc G.top) G.zero) , sucP (pB (pB πc G.top) G.zero))
  (G₀ G.top) (pM (pB πc G.top) G.top) (pB (pB πc G.top) G.top)
ht₀ = inj₂ (1 , inj₁ refl)

module Ci₀ = Ctx GK₃ (Ψᵖ zero V2 Sp (cmpe₀ p₀) G.top noM noP) (btbo-gen Sp (cmpe₀ p₀))
  (λ ζ → up≼ (cmpe₀ p₀) (hz₀ ζ)) (λ a → up≼ (cmpe₀ p₀) (hs₀ a)) (up≼ (cmpe₀ p₀) ht₀) (λ f n q → ≼l n q)

ch≼₀ᵖ : ∀ m → S2.ch m ≼ NA.read (eᵖ m)
ch≼₀ᵖ zero = ≼-refl _
ch≼₀ᵖ (suc m) = ≼-trans
  (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.lim 0 L.zero} {σ = λ r → r}
    (L.add-≅ {σ = S2.σ₁} {σ′ = S2.σ₁} (L.Ω-refl S2.ℓ₀) (L.≅-refl⁰ (S2.ch m))))))
  (NA.plus≽ (eᵖ m) (GK₃ (eᵖ m)) (Ci₀.ctx (ch≼₀ᵖ m) (eᵖ m) refl))
```

外层与内层的根结点 `top` 支的值都经 `irr₀` 换到 `GK₃` 的形状.

```agda
χ₁-topᵖ : S2.χ 1 ≼ NA.read (Fo G.top)
χ₁-topᵖ = l≼ (λ m → ≼l m (≼-trans (Ci₀.ctx (ch≼₀ᵖ m) (eᵖ m) refl)
  (≅→≼ (read₀≅ (irr₀ V2 Sp S₀ (cmpe₀ p₀) x₀ (G₀ (eᵖ m)) (pM (pB πc G.top) (eᵖ m)) noM (pB (pB πc G.top) (eᵖ m)))))))

χ₁-topᵢ : S2.χ 1 ≼ NA.read (gk₁ᵖ G.top)
χ₁-topᵢ = l≼ (λ m → ≼l m (≼-trans (Ci₀.ctx (ch≼₀ᵖ m) (eᵖ m) refl)
  (≅→≼ (read₀≅ (irr₀ V2 Sp Sp (cmpe₀ p₀) (cmpe₀ p₀) (G₀ (eᵖ m)) (pM (pB πc G.top) (eᵖ m))
    (mB (pM πc G.top) (eᵖ m)) (pB (pB πc G.top) (eᵖ m)))))))

χ₁-d1ᵖ : S2.χ 1 ≼ NA.read (dᵖ 1)
χ₁-d1ᵖ = NA.plus≽ G.top (gk₁ᵖ G.top) χ₁-topᵢ
```

## 3 条件定理

```agda
module FromStepᵖ (f : ℕ → L.Ordᶜ L.zero) (lf : Lab (L.lim f) S2.t2)
  (step : ∀ k m → f k ≼ NA.read (dᵖ m) → f (suc k) ≼ NA.read (Fo (dᵖ (suc m)))) where

  f0≅ : f 0 L.≅ S2.χ 1
  f0≅ = S2.Lab-uniq (subst (Lab (f 0)) (S2.diag2-fs 0) (S2.sqLab lf refl 0)) S2.χ1-label

  stp : ∀ k → Σ ℕ (λ m → f k ≼ NA.read (dᵖ m))
  stp zero = 1 , ≼-trans (≅→≼ f0≅) χ₁-d1ᵖ
  stp (suc k) = suc (suc (proj₁ (stp k))) ,
    NA.plus≽ (dᵖ (suc (proj₁ (stp k)))) (gk₁ᵖ (dᵖ (suc (proj₁ (stp k)))))
      (≼-trans (step k (proj₁ (stp k)) (proj₂ (stp k))) (≅→≼ (Fo≅gk (dᵖ (suc (proj₁ (stp k)))))))

  term : ∀ k → f k ≼ NA.read (Ψᵖ zero V2 S₀ x₀ (chT (tw 2) V2 1) noM (chP (tw 2) V2 1))
  term zero = ≼-trans (≅→≼ f0≅) (≼l 0 χ₁-topᵖ)
  term (suc k) = ≼l (suc (proj₁ (stp k))) (step k (proj₁ (stp k)) (proj₂ (stp k)))

  T2≼ : L.lim f ≼ NA.read T⁺ʷᵖ
  T2≼ = ≼l 1 (l≼ term)

Stepᵖ : Set
Stepᵖ = ∀ k m → GL.χ k ≼ NA.read (dᵖ m) → GL.χ (suc k) ≼ NA.read (Fo (dᵖ (suc m)))

T2≼ᴳᵖ : Stepᵖ → GL.T2ᴸ ≼ NA.read T⁺ʷᵖ
T2≼ᴳᵖ s = FromStepᵖ.T2≼ GL.χ GL.T2-label s
```
