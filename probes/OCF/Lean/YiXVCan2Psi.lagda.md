# YiXV YiXVCan2Psi
> 验收文件。编译定理：二层自身层折叠保持好树与带证据比较，且输出不低于 Ω₂。
> 按 YiOverOps/YiXVRef2Add 的证明扩展，仅二层参照域；源树γ₂与整链上界仍未证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Psi where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼-refl; ≼-trans)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVRefVar as V
open import OCF.Lean.YiXVCan2Core
import OCF.Lean.YiXVCan2Add as A
import OCF.Lean.YiXVCanTau as T

Ψ : F.T₂ → F.T₂
Ψ = L.ψ L.zero (λ q → L.suc q)
B : R.T₁ → F.T₂
B = L.ψ L.zero (λ q → L.suc (L.suc q))
D : R.T₀ → F.T₂
D = L.ψ L.zero (λ q → L.suc (L.suc (L.suc q)))

good-iter : ∀ {X} → Gd X → ∀ n → Gd (iter (X L.+_) L.zero n)
good-iter g zero = gz
good-iter g (suc n) = A.good g (good-iter g n)
iter-le : ∀ {X Y} → Le X Y → ∀ n → Le (iter (X L.+_) L.zero n) (iter (Y L.+_) L.zero n)
iter-le p zero = refl gz
iter-le p (suc n) = A.plus p (iter-le p n)

pos-Ω : Le one F.Ω₂
pos-Ω = pack (gs gz) Gd-Ω₂ (aa₁ (λ z hz → trans one-up-Ω
  (u≤ O.Gd-Ω (T.start-good hz) (T.start-floor hz))))

baseD : ∀ y → Gd (D y) → Le F.Ω₂ (D y)
baseD L.zero g = Ω₂-refl
baseD (L.suc y) (gl g) = pack Gd-Ω₂ (gl g) (lr 1 (baseD y (g 1)))
baseD (L.lim f) (gl g) = pack Gd-Ω₂ (gl g) (lr 0 (baseD (f 0) (g 0)))
baseD (L.limᵢ () f) g
baseD (L.up () y) g

baseB : ∀ Y → Gd (B Y) → Le F.Ω₂ (B Y)
baseB L.zero g = Ω₂-refl
baseB (L.suc Y) (gl g) = pack Gd-Ω₂ (gl g) (lr 1 (baseB Y (g 1)))
baseB (L.lim f) (gl g) = pack Gd-Ω₂ (gl g) (lr 0 (baseB (f 0) (g 0)))
baseB (L.limᵢ L.zero f) (gn₀ law g) = pack Gd-Ω₂ (gn₀ law g) (aa₀ (baseB (f R.𝟙) (g R.𝟙 (≼-refl _))))
baseB (L.limᵢ (L.suc ()) f) g
baseB (L.up L.zero y) g = baseD y g

base : ∀ X → Gd (Ψ X) → Le F.Ω₂ (Ψ X)
base L.zero g = Ω₂-refl
base (L.suc X) (gl g) = pack Gd-Ω₂ (gl g) (lr 1 (base X (g 1)))
base (L.lim f) (gl g) = pack Gd-Ω₂ (gl g) (lr 0 (base (f 0) (g 0)))
base (L.limᵢ L.zero f) (gn₁ law g) = pack Gd-Ω₂ (gn₁ law g)
  (aa₁ (λ z hz → base (f (T.τ z)) (g z (T.start-good hz) (T.start-floor hz))))
base (L.limᵢ (L.suc L.zero) f) (gn₀ law g) = pack Gd-Ω₂ (gn₀ law g) (aa₀ (base (f R.𝟙) (g R.𝟙 (≼-refl _))))
base (L.up L.zero Y) g = baseB Y g

strict : ∀ {X} → Gd X → Le one X → Le (L.suc X) (L.lim (iter (X L.+_) L.zero))
strict g p = pack (gs g) (gl (good-iter g)) (lr 2 (A.plus (refl g) p))

mutual
  monoD : ∀ {x y : R.T₀} → Gd (D x) → Gd (D y) → x ≼ y → Le (D x) (D y)
  monoD gx gy z≼ = baseD _ gy
  monoD (gl gx) (gl gy) (s≼s p) = pack (gl gx) (gl gy)
    (ll (λ n → pack (gx n) (gl gy) (lr n (iter-le (monoD (gx 1) (gy 1) p) n))))
  monoD gx (gl gy) (≼l n p) = pack gx (gl gy) (lr n (monoD gx (gy n) p))
  monoD (gl gx) gy (l≼ h) = pack (gl gx) gy (ll (λ n → monoD (gx n) gy (h n)))
  monoD gx gy (≼i {p = ()} x ex p)
  monoD gx gy (i≼ {p = ()} h)
  monoD gx gy (≼u {r = ()} p)
  monoD gx gy (u≼ {r = ()} p)

  flat : ∀ {X} {y : R.T₀} → Gd (B X) → Gd (D y) → R.Flat X → X ≼ y → Le (B X) (D y)
  flat gx gy fx z≼ = baseD _ gy
  flat (gl gx) (gl gy) (R.fs fx) (s≼s p) = pack (gl gx) (gl gy)
    (ll (λ n → pack (gx n) (gl gy) (lr n (iter-le (flat (gx 1) (gy 1) fx p) n))))
  flat gx (gl gy) fx (≼l n p) = pack gx (gl gy) (lr n (flat gx (gy n) fx p))
  flat (gl gx) gy (R.fl fx) (l≼ h) = pack (gl gx) gy (ll (λ n → flat (gx n) gy (fx n) (h n)))
  flat gx gy fx (≼i {p = ()} x ex p)
  flat gx gy () (i≼ h)
  flat gx gy fx (≼u {r = ()} p)
  flat gx gy R.fu (u≼ p) = monoD gx gy p

  monoB : ∀ {X Y} → Gd (B X) → Gd (B Y) → X R.≤ₚ Y → Le (B X) (B Y)
  monoB gx gy R.zz = Ω₂-refl
  monoB (gl gx) (gl gy) (R.ss p) = pack (gl gx) (gl gy)
    (ll (λ n → pack (gx n) (gl gy) (lr n (iter-le (monoB (gx 1) (gy 1) p) n))))
  monoB gx (gl gy) (R.ws p) = pack gx (gl gy) (lr 1 (monoB gx (gy 1) p))
  monoB gx (gl gy) (R.≤l n p) = pack gx (gl gy) (lr n (monoB gx (gy n) p))
  monoB (gl gx) gy (R.l≤ h) = pack (gl gx) gy (ll (λ n → monoB (gx n) gy (h n)))
  monoB (gn₀ lx gx) (gn₀ ly gy) (R.ii h) = pack (gn₀ lx gx) (gn₀ ly gy)
    (nn₀ (λ x y o p → monoB (gx x o) (gy y (≼-trans o p)) (h (V.τ x) (V.τ y) (V.posτ o) (V.monoτ p))))
  monoB gx (gn₀ ly gy) (R.i1 p) = pack gx (gn₀ ly gy) (aa₀ (monoB gx (gy R.𝟙 (≼-refl _)) p))
  monoB gx gy (R.fu fx p) = flat gx gy fx p

goodD : ∀ y → Gd (D y)
goodD L.zero = Gd-Ω₂
goodD (L.suc y) = gl (good-iter (goodD y))
goodD (L.lim f) = gl (λ n → goodD (f n))
goodD (L.limᵢ () f)
goodD (L.up () y)

goodB : ∀ {X} → O.Gd X → Gd (B X)
goodB O.gz = Gd-Ω₂
goodB (O.gs g) = gl (good-iter (goodB g))
goodB (O.gl g) = gl (λ n → goodB (g n))
goodB (O.gi {f = f} law gb) = gn₀ (sc₀
  (λ x y o p → monoB (goodB (gb (V.τ x) (V.posτ o))) (goodB (gb (V.τ y) (≼-trans (V.posτ o) (V.monoτ p))))
    (O.SC.mo law (V.τ x) (V.τ y) (V.posτ o) (V.monoτ p)))
  (λ x o → trans (strict (goodB (gb (V.τ x) (V.posτ o)))
      (trans pos-Ω (baseB (f (V.τ x)) (goodB (gb (V.τ x) (V.posτ o))))))
    (monoB (gl (good-iter (goodB (gb (V.τ x) (V.posτ o))))) (goodB (gb (L.suc (V.τ x)) (s≼s z≼)))
      (O.SC.db law (V.τ x) (V.posτ o))))
  (trans pos-Ω (baseB (f R.𝟙) (goodB (gb R.𝟙 (≼-refl _))))))
  (λ x o → goodB (gb (V.τ x) (V.posτ o)))
goodB O.gu = goodD _

mutual
  good : ∀ {X} → Gd X → Gd (Ψ X)
  good gz = Gd-Ω₂
  good (gs g) = gl (good-iter (good g))
  good (gl g) = gl (λ n → good (g n))
  good (gn₀ {f = f} (sc₀ mo db po) gb) = gn₀ (sc₀
    (λ x y o p → monoE (good (gb (V.τ x) (V.posτ o))) (good (gb (V.τ y) (≼-trans (V.posτ o) (V.monoτ p))))
      (mo (V.τ x) (V.τ y) (V.posτ o) (V.monoτ p)))
    (λ x o → trans (strict (good (gb (V.τ x) (V.posτ o)))
        (trans pos-Ω (base (f (V.τ x)) (good (gb (V.τ x) (V.posτ o))))))
      (monoE (gl (good-iter (good (gb (V.τ x) (V.posτ o))))) (good (gb (L.suc (V.τ x)) (s≼s z≼)))
        (db (V.τ x) (V.posτ o))))
    (trans pos-Ω (base (f R.𝟙) (good (gb R.𝟙 (≼-refl _))))))
    (λ x o → good (gb (V.τ x) (V.posτ o)))
  good (gn₁ {f = f} (sc₁ mo db po) gb) = gn₁ (sc₁
    (λ x y hx hy o p → monoE (good (gb (T.τ x) (T.good hx) (T.floor o)))
      (good (gb (T.τ y) (T.good hy) (T.floor (R.trans o p))))
      (mo (T.τ x) (T.τ y) (T.good hx) (T.good hy) (T.floor o) (T.mono p)))
    (λ x hx o → trans (strict (good (gb (T.τ x) (T.good hx) (T.floor o)))
        (trans pos-Ω (base (f (T.τ x)) (good (gb (T.τ x) (T.good hx) (T.floor o))))))
      (monoE (gl (good-iter (good (gb (T.τ x) (T.good hx) (T.floor o)))))
        (good (gb (L.suc (T.τ x)) (O.gs (T.good hx)) (R.ws (T.floor o))))
        (db (T.τ x) (T.good hx) (T.floor o))))
    (trans pos-Ω (base (f (T.τ O.Ω₁)) (good (gb (T.τ O.Ω₁) (T.good O.Gd-Ω) T.Ωτ)))))
    (λ x hx o → good (gb (T.τ x) (T.good hx) (T.floor o)))
  good (gu g) = goodB g

  monoE : ∀ {X Y} → Gd (Ψ X) → Gd (Ψ Y) → Le X Y → Le (Ψ X) (Ψ Y)
  monoE gx gy (pack gX gY rr) = refl gx
  monoE gx gy (pack gX gY zz) = base _ gy
  monoE (gl gx) (gl gy) (pack gX gY (ss p)) = pack (gl gx) (gl gy)
    (ll (λ n → pack (gx n) (gl gy) (lr n (iter-le (monoE (gx 1) (gy 1) p) n))))
  monoE gx (gl gy) (pack gX gY (ws p)) = pack gx (gl gy) (lr 1 (monoE gx (gy 1) p))
  monoE (gl gx) gy (pack gX gY (ll h)) = pack (gl gx) gy (ll (λ n → monoE (gx n) gy (h n)))
  monoE gx (gl gy) (pack gX gY (lr n p)) = pack gx (gl gy) (lr n (monoE gx (gy n) p))
  monoE (gn₀ lx gx) (gn₀ ly gy) (pack gX gY (nn₀ h)) = pack (gn₀ lx gx) (gn₀ ly gy)
    (nn₀ (λ x y o p → monoE (gx x o) (gy y (≼-trans o p)) (h (V.τ x) (V.τ y) (V.posτ o) (V.monoτ p))))
  monoE (gn₁ lx gx) (gn₁ ly gy) (pack gX gY (nn₁ h)) = pack (gn₁ lx gx) (gn₁ ly gy)
    (nn₁ (λ x y hx hy o p → monoE (gx x hx o) (gy y hy (R.trans o p))
      (h (T.τ x) (T.τ y) (T.good hx) (T.good hy) (T.floor o) (T.mono p))))
  monoE gx (gn₀ ly gy) (pack gX gY (aa₀ p)) = pack gx (gn₀ ly gy) (aa₀ (monoE gx (gy R.𝟙 (≼-refl _)) p))
  monoE gx (gn₁ ly gy) (pack gX gY (aa₁ h)) = pack gx (gn₁ ly gy)
    (aa₁ (λ z hz → monoE gx (gy z (T.start-good hz) (T.start-floor hz)) (h (T.τ z) (T.shift hz))))
  monoE gx gy (pack gX gY (uu p)) = monoB gx gy p
  monoE gx gy (pack gX gY (uS g)) = refl gx
  monoE gx gy (pack gX gY (uS⁻ g)) = refl gx
  monoE gx gy (pack gX gY uZ) = refl gx
  monoE gx gy (pack gX gY uZ⁻) = refl gx
  monoE gx gy (pack gX gY (uL g)) = refl gx
  monoE gx gy (pack gX gY (uL⁻ g)) = refl gx
  monoE gx gy (pack gX gY (uN g)) = refl gx
  monoE gx gy (pack gX gY (uN⁻ g)) = refl gx
  monoE gx gy (pack gX gY (tr (pack ga gm p) q)) = trans
    (monoE gx (good gm) (pack ga gm p)) (monoE (good gm) gy q)

mono : ∀ {X Y} → Le X Y → Le (Ψ X) (Ψ Y)
mono p = monoE (good (left p)) (good (right p)) p

sample : Gd (Ψ F.Ω₂)
sample = good Gd-Ω₂
sample-le : Le (Ψ F.Ω₂) (Ψ F.Ω₂)
sample-le = mono Ω₂-refl
```
