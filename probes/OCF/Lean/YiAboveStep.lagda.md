# ψ₀(Ω_Ω·2) ≼ `T⁺` 归约到一条单步比较 (条件)

验收文件. 编译定理 `χ₁-top : S2.χ 1 ≼ NA.read (Ψ₀ (gK G.top))` (根链第 1 点的第 0 支已不低于 ψ₀(Ω_Ω+Ω₁)), `χ₁-d1` (于是结点链的第 1 点也是).
条件定理 `FromStep.T2≼ : L.lim f ≼ NA.read NT.T⁺`, 前提 `lf : Lab (L.lim f) S2.t2` 与单步比较 `step`; §3 用 `GoodL` 的 `χ`, `T2-label` 填上 `lf`, 得 `T2≼ᴳ : Stepᴳ → GL.T2ᴸ ≼ NA.read NT.T⁺`.
`Stepᴳ` 未证, 也未否定: 它要层号 ≥ 1 的链上的值 (`Ω_{γ′_k}` 的折叠), 正是保守派发 (`cmp V₂ = fold`) 起作用的地方; 它成立与否是判断. 只是下界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAboveStep where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
open import OCF.Lean.YiNextFold
import OCF.Lean.YiNextTop as NT
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiAboveOne using (bt₃)
open import OCF.Lean.YiAboveCtx using (Ψ₀; topᶜ; up≼; gK; gm₀; gk₃; gk₁; d)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
open import OCF.Align.Correspond using (Lab)
import OCF.Align.Stage2 as S2
import OCF.Align.GoodL as GL
```

## 1 第 0 支: `top + gm₀ ζ` 上的上下文引理

与 [YiAboveCtx](YiAboveCtx.lagda.md) 的 `ctx` 同形; `gm₀` 是 `Tt top` 的分支, 后继一步就是 ω 倍.

```agda
ctx₀ : ∀ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ ζ → b ≡ NA.read ζ →
  L.ψ⁰ (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ≼ NA.read (Ψ₀ (plus (tw 2) G.top (gm₀ ζ)))
ctx₀ z≼ ζ q = ≼-trans bt₃ (up≼ (plus-weak (tw 2) G.top (gm₀ ζ)))
ctx₀ (s≼s p) (G.suc a) refl = ≼-trans (NA.suc-lower (Ψ₀ (plus (tw 2) G.top (gm₀ a))) (ctx₀ p a refl))
  (up≼ (inj₂ (1 , add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc (gm₀ a)
    (topᶜ (tw 2) v0 (λ r → keep (G.top , tt , inj₂ r) refl) a)))))
ctx₀ (s≼s p) G.top refl = ≼-trans (NA.suc-lower (Ψ₀ (plus (tw 2) G.top (gm₀ G.zero))) (ctx₀ p G.zero refl))
  (up≼ (inj₂ (1 , inj₁ refl)))
ctx₀ (≼l n p) (G.lim f) refl = ≼l n (ctx₀ p (f n) refl)
ctx₀ (l≼ h) ζ q = l≼ (λ n → ctx₀ (h n) ζ q)
ctx₀ (≼i {p = ()} x ex p) ζ q
ctx₀ (i≼ {p = ()} h) ζ q
ctx₀ (≼u {r = ()} p) ζ q
ctx₀ (u≼ {r = ()} p) ζ q

e : ℕ → R
e = chain zero gk₃

ch≼₀ : ∀ m → S2.ch m ≼ NA.read (e m)
ch≼₀ zero = ≼-refl _
ch≼₀ (suc m) = ≼-trans
  (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.lim 0 L.zero} {σ = λ r → r}
    (L.add-≅ {σ = S2.σ₁} {σ′ = S2.σ₁} (L.Ω-refl S2.ℓ₀) (L.≅-refl⁰ (S2.ch m))))))
  (NA.plus≽ (e m) (gk₃ (e m)) (ctx₀ (ch≼₀ m) (e m) refl))

χ₁-top : S2.χ 1 ≼ NA.read (Ψ₀ (gK G.top))
χ₁-top = l≼ (λ m → ≼l m (ctx₀ (ch≼₀ m) (e m) refl))

χ₁-d1 : S2.χ 1 ≼ NA.read (d 1)
χ₁-d1 = NA.plus≽ G.top (gk₁ G.top) χ₁-top
```

## 2 条件定理

```agda
module FromStep (f : ℕ → L.Ordᶜ L.zero) (lf : Lab (L.lim f) S2.t2)
  (step : ∀ k m → f k ≼ NA.read (d m) → f (suc k) ≼ NA.read (Ψ₀ (gK (d (suc m))))) where

  f0≅ : f 0 L.≅ S2.χ 1
  f0≅ = S2.Lab-uniq (subst (Lab (f 0)) (S2.diag2-fs 0) (S2.sqLab lf refl 0)) S2.χ1-label

  stp : ∀ k → Σ ℕ (λ m → f k ≼ NA.read (d m))
  stp zero = 1 , ≼-trans (≅→≼ f0≅) χ₁-d1
  stp (suc k) = suc (suc (proj₁ (stp k))) ,
    NA.plus≽ (d (suc (proj₁ (stp k)))) (gk₁ (d (suc (proj₁ (stp k))))) (step k (proj₁ (stp k)) (proj₂ (stp k)))

  term : ∀ k → f k ≼ NA.read (Ψ₀ (G.lc p₀ gK))
  term zero = ≼-trans (≅→≼ f0≅) (≼l 0 χ₁-top)
  term (suc k) = ≼l (suc (proj₁ (stp k))) (step k (proj₁ (stp k)) (proj₂ (stp k)))

  T2≼ : L.lim f ≼ NA.read NT.T⁺
  T2≼ = ≼l 1 (l≼ term)
```

## 3 参照取 `GoodL` 的 ψ₀(Ω_Ω·2) (`GL.T2-label`, 无条件)

```agda
_ : GL.T2ᴸ ≡ L.lim GL.χ
_ = refl

Stepᴳ : Set
Stepᴳ = ∀ k m → GL.χ k ≼ NA.read (d m) → GL.χ (suc k) ≼ NA.read (Ψ₀ (gK (d (suc m))))

T2≼ᴳ : Stepᴳ → GL.T2ᴸ ≼ NA.read NT.T⁺
T2≼ᴳ s = FromStep.T2≼ GL.χ GL.T2-label s
```
