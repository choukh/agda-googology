# YiXV YiXVCan2One
> 验收文件。编译定理：二层带证据比较保持目标层 1 的折叠，并给出输出好树。
> 按 YiOverOps/YiXVRef2Add 的证明扩展，仅二层参照域；源树γ₂与整链上界仍未证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2One where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVRefVar as V
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVCanTau as T

module It (f : R.T₁ → F.T₂)
  (b : ∀ x → O.Gd x → O.Ω₁ R.≤ₚ x → O.Gd (F.ψ₁ (f x))) where
  c : ℕ → R.T₁
  c = iter (λ x → F.ψ₁ (f x)) O.Ω₁
  floor : ∀ n → O.Ω₁ R.≤ₚ c n
  floor zero = O.Ω≤Ω
  floor (suc n) = F.base (f (c n))
  good : ∀ n → O.Gd (c n)
  good zero = O.Gd-Ω
  good (suc n) = b (c n) (good n) (floor n)

module IterCmp (f g : R.T₁ → F.T₂)
  (bf : ∀ x → O.Gd x → O.Ω₁ R.≤ₚ x → O.Gd (F.ψ₁ (f x)))
  (bg : ∀ x → O.Gd x → O.Ω₁ R.≤ₚ x → O.Gd (F.ψ₁ (g x)))
  (h : ∀ x y → O.Gd x → O.Gd y → O.Ω₁ R.≤ₚ x → x R.≤ₚ y → F.ψ₁ (f x) R.≤ₚ F.ψ₁ (g y)) where
  module A = It f bf
  module B = It g bg
  bound : ∀ n → A.c n R.≤ₚ B.c n
  bound zero = O.Ω≤Ω
  bound (suc n) = h (A.c n) (B.c n) (A.good n) (B.good n) (A.floor n) (bound n)

succ-step : ∀ {X : R.T₁} → O.Gd X → O.𝟙₁ R.≤ₚ X →
  L.suc X R.≤ₚ L.lim (iter (X L.+_) L.zero)
succ-step g p = R.≤l 2 (O.+ₚ (O.reflₚ g) p)

mutual
  good₁ : ∀ {X} → C.Gd X → O.Gd (F.ψ₁ X)
  good₁ C.gz = O.Gd-Ω
  good₁ (C.gs g) = O.gl (O.Gd-iter (good₁ g))
  good₁ (C.gl g) = O.gl (λ n → good₁ (g n))
  good₁ (C.gn₀ {f = f} law gb) = O.gi
    (O.sc (λ x y o q → mono₁ (C.SC₀.mo₀ law (V.τ x) (V.τ y) (V.posτ o) (V.monoτ q)))
      (λ y o → R.trans (succ-step (good₁ (gb (V.τ y) (V.posτ o)))
        (R.trans O.pos-Ω (F.base (f (V.τ y))))) (mono₁ (C.SC₀.db₀ law (V.τ y) (V.posτ o))))
      (R.trans O.pos-Ω (F.base (f R.𝟙))))
    (λ y o → good₁ (gb (V.τ y) (V.posτ o)))
  good₁ (C.gn₁ {f = f} law gb) = O.gl (λ n →
    good₁ (gb (It.c f (λ x gx o → good₁ (gb x gx o)) n)
      (It.good f (λ x gx o → good₁ (gb x gx o)) n)
      (It.floor f (λ x gx o → good₁ (gb x gx o)) n)))
  good₁ (C.gu g) = O.Gd-ψ₁ g

  mono₁ : ∀ {X Y} → C.Le X Y → F.ψ₁ X R.≤ₚ F.ψ₁ Y
  mono₁ (C.pack gx gy C.rr) = O.reflₚ (good₁ gx)
  mono₁ (C.pack gx gy C.zz) = F.base _
  mono₁ (C.pack gx gy (C.ss p)) = R.l≤ (λ n → R.≤l n (O.iterₚ (mono₁ p) n))
  mono₁ (C.pack gx gy (C.ws p)) = R.≤l 1 (mono₁ p)
  mono₁ (C.pack gx gy (C.ll h)) = R.l≤ (λ n → mono₁ (h n))
  mono₁ (C.pack gx gy (C.lr n p)) = R.≤l n (mono₁ p)
  mono₁ (C.pack gx gy (C.nn₀ h)) = R.ii (λ x y o q → mono₁ (h (V.τ x) (V.τ y) (V.posτ o) (V.monoτ q)))
  mono₁ (C.pack (C.gn₁ {f = f} law bf) (C.gn₁ {f = g} law′ bg) (C.nn₁ h)) =
    R.l≤ (λ n → R.≤l n (mono₁ (h
      (It.c f (λ x gx o → good₁ (bf x gx o)) n)
      (It.c g (λ y gy o → good₁ (bg y gy o)) n)
      (It.good f (λ x gx o → good₁ (bf x gx o)) n)
      (It.good g (λ y gy o → good₁ (bg y gy o)) n)
      (It.floor f (λ x gx o → good₁ (bf x gx o)) n)
      (IterCmp.bound f g (λ x gx o → good₁ (bf x gx o)) (λ y gy o → good₁ (bg y gy o))
        (λ x y gx gy o q → mono₁ (h x y gx gy o q)) n))))
  mono₁ (C.pack gx gy (C.aa₀ p)) = R.i1 (mono₁ p)
  mono₁ (C.pack gx gy (C.aa₁ h)) = R.≤l 0 (mono₁ (h O.Ω₁ T.start))
  mono₁ (C.pack gx gy (C.uu p)) = O.ψ₁-mono p
  mono₁ (C.pack gx gy (C.uS g)) = O.reflₚ (good₁ gx)
  mono₁ (C.pack gx gy (C.uS⁻ g)) = O.reflₚ (good₁ gx)
  mono₁ (C.pack gx gy C.uZ) = O.reflₚ (good₁ gx)
  mono₁ (C.pack gx gy C.uZ⁻) = O.reflₚ (good₁ gx)
  mono₁ (C.pack gx gy (C.uL g)) = O.reflₚ (good₁ gx)
  mono₁ (C.pack gx gy (C.uL⁻ g)) = O.reflₚ (good₁ gx)
  mono₁ (C.pack gx gy (C.uN g)) = O.reflₚ (good₁ gx)
  mono₁ (C.pack gx gy (C.uN⁻ g)) = O.reflₚ (good₁ gx)
  mono₁ (C.pack gx gy (C.tr p q)) = R.trans (mono₁ p) (mono₁ q)

sample : O.Gd (F.ψ₁ F.Ω₂)
sample = good₁ C.Gd-Ω₂
sample-le : F.ψ₁ F.Ω₂ R.≤ₚ F.ψ₁ F.Ω₂
sample-le = mono₁ C.Ω₂-refl
```
