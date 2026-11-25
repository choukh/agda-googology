# `T⁺` 不低于 ψ₀(Ω_Ω+Ω₁) (无前提)

验收文件. 编译定理 `χ₁≼ : S2.χ 1 ≼ NA.read NT.T⁺`; 参照 `S2.χ 1 = ψ⁰ K₀` 由 `S2.χ1-label` 验收为 ψ₀(Ω_Ω+Ω₁).
办法: `T⁺` 根链第 1 点是 `p₀` 上的结点 (分支 `gK ξ = top + Kf Tt ξ`); 上下文引理 `ctx`: 可数的 `y ≼ read ξ` 推出 `ψ⁰ (Ω_{ℓ₀} ⊕ y) ≼ read (Ψ₀ (gK ξ))`, 对 `≼` 的推导归纳, 每步只用第一位置 (`topᶜ`, `add-cp`, `Ψ-cp`) 与 `suc-lower`; 再让参照的链 `S2.ch` 与结点的链 `d` 同步.
只是下界, 不涉及上界与同值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAboveCtx where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
open import OCF.Lean.YiNextFold
import OCF.Lean.YiNextTop as NT
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiNextValFin using (cp⊑ⁿ)
open import OCF.Lean.YiAboveOne using (bt₃)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ⊑→≼)
import OCF.Align.Stage2 as S2

Ψ₀ : Raw (tw 2) → R
Ψ₀ = Ψ zero NT.V₂ (λ _ → fold)
```

## 1 `top` 是一切折叠值的第一位置

```agda
ΩT-top : ∀ m j (w : Way m j) K o → Cp m G.top (K G.top) → Cp m G.top (o 0) → Cp m G.top (ΩT m j w K o)
ΩT-top m .(lev m p) (keep p refl) K o hK ho = inj₂ (nodeAt-dn m p G.lc dnLc K hK)
ΩT-top m j fold K o hK ho = inj₂ (0 , ho)

topᶜ : ∀ m {k} (V : Lv k) x ξ → Cp m G.top (Ψ m V x ξ)
topᶜ m V x G.zero = inj₁ refl
topᶜ m V x (G.suc a) = inj₂ (0 , topᶜ m V x a)
topᶜ m V x (G.lim f) = inj₂ (0 , topᶜ m V x (f 0))
topᶜ m {k} V x (G.lc r g) = inj₂ (ΨN-dn m k r (x r) (λ η → Ψ m V x (g η)) (λ η → Ψ (lev k r) V (cmp V r) (g η))
  (topᶜ m V x (g (Lay.tp (Lo k r)))))
topᶜ m v0 x (G.em () a)
topᶜ m (vs V) x (G.em _ a) = topᶜ m V (λ r → x (inj₂ r)) a
topᶜ m (vl V st) x (G.em n a) = topᶜ m (V n) (λ r → x (n , r)) a
topᶜ m (vΩ V u) x (G.em (η , l) a) = topᶜ m (V η l) (λ r → x (η , l , r)) a
topᶜ m v0 x G.top = inj₂ (0 , inj₁ refl)
topᶜ m {suc k} (vs V) x G.top = inj₂ (Ψn-dn m k (x (inj₁ tt)) (λ η → Ψ m V (λ r → x (inj₂ r)) η) (λ η → Ψ k V (self k) η)
  (topᶜ m V (λ r → x (inj₂ r)) G.top))
topᶜ m (vl V st) x G.top = inj₂ (0 , topᶜ m (V 0) (λ r → x (0 , r)) G.top)
topᶜ m (vΩ V u) x G.top = ΩT-top m zero (x p₀) _ _
  (topᶜ m (V G.top tt) (λ r → x (G.top , tt , r)) G.top) (topᶜ m (V G.top tt) (λ _ → fold) G.top)

cp≼ : ∀ {a b} → Cp zero a b → NA.read a ≼ NA.read b
cp≼ {a} {b} c = ⊑→≼ (NA.read a) (cp⊑ⁿ a b c)

up≼ : ∀ {A B} → Cp (tw 2) A B → NA.read (Ψ₀ A) ≼ NA.read (Ψ₀ B)
up≼ c = cp≼ (Ψ-cp zero NT.V₂ (λ _ → fold) c)
```

## 2 根链第 1 点的结点

`Tt η` 是第 `η` 支 `top` 的保留像 (`Ω-keep` 的分支族), `gK` 是根链第 1 点 (`top + Φ₂ top`) 的分支.

```agda
Tt : R → Raw (tw 2)
Tt η = Ψ (tw 2) (NT.lv (nrm η) (nrm-lgl η)) (λ r → keep (nrm η , nrm-lgl η , r) refl) G.top

gK : R → Raw (tw 2)
gK ξ = plus (tw 2) G.top (Kf (tw 2) Tt ξ)

term₁ : chain (tw 2) NT.Φ₂ 1 ≡ G.lc p₀ gK
term₁ = refl

sucK : ∀ a → Cp (tw 2) (G.suc (gK a)) (gK (G.suc a))
sucK a = inj₂ (1 , add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc (Kf (tw 2) Tt a)
  (topᶜ (tw 2) (NT.lv (nrm (G.suc a)) (nrm-lgl (G.suc a))) (λ r → keep (nrm (G.suc a) , nrm-lgl (G.suc a) , r) refl) G.top)))
```

坐标 `top` (读成 1): `Tt top` 是 `p₀` 上的结点, 它自己的链第 1 点已过 `suc top`, 于是值上乘了 ω.

```agda
gm₀ : R → Raw (tw 2)
gm₀ ζ = Ψ (tw 2) v0 (λ r → keep (G.top , tt , inj₂ r) refl) ζ

Tt-top : Tt G.top ≡ G.lc p₀ gm₀
Tt-top = refl

gk₃ : R → R
gk₃ ζ = Ψ zero NT.V₂ (cmp NT.V₂ p₀) (plus (tw 2) G.top (gm₀ ζ))

e₁ : R
e₁ = chain zero gk₃ 1

c₃a : Cp zero (G.suc G.top) e₁
c₃a = add-cp zero G.lc dnLc G.top (topᶜ zero NT.V₂ (cmp NT.V₂ p₀) (plus (tw 2) G.top (gm₀ G.top)))

c₃c : Cp (tw 2) (plus (tw 2) G.top (gm₀ (G.suc G.top))) (plus (tw 2) G.top (gm₀ e₁))
c₃c = add-cp (tw 2) G.lc dnLc G.top (Ψ-cp (tw 2) v0 (λ r → keep (G.top , tt , inj₂ r) refl) c₃a)

c₃d : Cp (tw 2) (G.suc (gK G.zero)) (plus (tw 2) G.top (gm₀ (G.suc G.top)))
c₃d = inj₂ (1 , add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc (gm₀ G.top)
  (topᶜ (tw 2) v0 (λ r → keep (G.top , tt , inj₂ r) refl) G.top)))

topStep : NA.read (Ψ₀ (G.suc (gK G.zero))) ≼ NA.read (Ψ₀ (gK G.top))
topStep = ≼-trans (up≼ c₃d) (≼-trans (up≼ c₃c) (≼l 1 (≼-refl _)))
```

## 3 上下文引理与链

```agda
ctx : ∀ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ ξ → b ≡ NA.read ξ →
  L.ψ⁰ (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ≼ NA.read (Ψ₀ (gK ξ))
ctx z≼ ξ q = ≼-trans bt₃ (up≼ (plus-weak (tw 2) G.top (Kf (tw 2) Tt ξ)))
ctx (s≼s p) (G.suc a) refl = ≼-trans (NA.suc-lower (Ψ₀ (gK a)) (ctx p a refl)) (up≼ (sucK a))
ctx (s≼s p) G.top refl = ≼-trans (NA.suc-lower (Ψ₀ (gK G.zero)) (ctx p G.zero refl)) topStep
ctx (≼l n p) (G.lim f) refl = ≼l n (ctx p (f n) refl)
ctx (l≼ h) ξ q = l≼ (λ n → ctx (h n) ξ q)
ctx (≼i {p = ()} x ex p) ξ q
ctx (i≼ {p = ()} h) ξ q
ctx (≼u {r = ()} p) ξ q
ctx (u≼ {r = ()} p) ξ q

gk₁ : R → R
gk₁ ζ = Ψ zero NT.V₂ (cmp NT.V₂ p₀) (gK ζ)

d : ℕ → R
d = chain zero gk₁

ch≼ : ∀ m → S2.ch m ≼ NA.read (d m)
ch≼ zero = ≼-refl _
ch≼ (suc m) = ≼-trans
  (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.lim 0 L.zero} {σ = λ r → r}
    (L.add-≅ {σ = S2.σ₁} {σ′ = S2.σ₁} (L.Ω-refl S2.ℓ₀) (L.≅-refl⁰ (S2.ch m))))))
  (NA.plus≽ (d m) (gk₁ (d m)) (ctx (ch≼ m) (d m) refl))

χ₁≼ : S2.χ 1 ≼ NA.read NT.T⁺
χ₁≼ = ≼l 1 (l≼ (λ m → ≼l m (ctx (ch≼ m) (d m) refl)))
```
