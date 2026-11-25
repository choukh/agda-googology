# YiXV YiXVCan2Zero
> 验收文件。编译定理：二层带证据比较保持目标层 0 的值序。
> 按 YiOverOps/YiXVRef2Add 的证明扩展，仅二层参照域；源树γ₂与整链上界仍未证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Zero where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼; iter-≼; 1≼ψ⁰)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVCan2One as I
import OCF.Lean.YiXVCanTau as T

module Chains (f : R.T₀ → R.T₁) (law : O.SC f) where
  P Q : R.T₀ → R.T₀
  P y = R.ψ₀ (f y)
  Q y = L.ψ (L.suc L.zero) (λ r → r) (L.up L.zero (f y))
  d e : ℕ → R.T₀
  d = iter P R.𝟙
  e = iter Q R.𝟙
  posP : ∀ n → R.𝟙 ≼ d n
  posP zero = ≼-refl _
  posP (suc n) = ≼-trans (1≼ψ⁰ (f (d n))) (proj₂ (R.ψ₀≈ (f (d n))))
  posQ : ∀ n → R.𝟙 ≼ e n
  posQ zero = ≼-refl _
  posQ (suc n) = ≼-trans (1≼ψ⁰ (f (e n))) (proj₂ (F.ψu≈ (f (e n))))
  p≤q : ∀ n → d n ≼ e n
  p≤q zero = ≼-refl _
  p≤q (suc n) = ≼-trans (proj₁ (R.ψ₀≈ (f (d n))))
    (≼-trans (R.mono⁰ (O.SC.mo law (d n) (e n) (posP n) (p≤q n))) (proj₂ (F.ψu≈ (f (e n)))))
  q≤p : ∀ n → e n ≼ d n
  q≤p zero = ≼-refl _
  q≤p (suc n) = ≼-trans (proj₁ (F.ψu≈ (f (e n))))
    (≼-trans (R.mono⁰ (O.SC.mo law (e n) (d n) (posQ n) (q≤p n))) (proj₂ (R.ψ₀≈ (f (d n)))))
  fwd : L.ψ⁰ (L.up L.zero (L.limᵢ L.zero f)) ≼
    L.ψ⁰ (L.limᵢ (L.suc L.zero) (λ x → L.up L.zero (f x)))
  fwd = l≼ (λ n → ≼l n (R.mono⁰ (O.SC.mo law (d n) (e n) (posP n) (p≤q n))))
  rev : L.ψ⁰ (L.limᵢ (L.suc L.zero) (λ x → L.up L.zero (f x))) ≼
    L.ψ⁰ (L.up L.zero (L.limᵢ L.zero f))
  rev = l≼ (λ n → ≼l n (R.mono⁰ (O.SC.mo law (e n) (d n) (posQ n) (q≤p n))))

mono₀ : ∀ {X Y} → C.Le X Y → L.ψ⁰ X ≼ L.ψ⁰ Y
mono₀ (C.pack gx gy C.rr) = ≼-refl _
mono₀ (C.pack gx gy C.zz) = 1≼ψ⁰ _
mono₀ (C.pack gx gy (C.ss p)) = l≼ (λ n → ≼l n (iter-≼ (mono₀ p) n))
mono₀ (C.pack gx gy (C.ws p)) = ≼l 1 (mono₀ p)
mono₀ (C.pack gx gy (C.ll h)) = l≼ (λ n → mono₀ (h n))
mono₀ (C.pack gx gy (C.lr n p)) = ≼l n (mono₀ p)
mono₀ (C.pack gx gy (C.nn₀ {f} {g} h)) = l≼ (λ n → ≼l n (mono₀ (h (F.c₀ f n) (F.c₀ g n)
  (F.Chain₀.floor f g (λ x y o q → mono₀ (h x y o q)) f n)
  (F.Chain₀.bound f g (λ x y o q → mono₀ (h x y o q)) n))))
mono₀ (C.pack (C.gn₁ {f = f} law bf) (C.gn₁ {f = g} law′ bg) (C.nn₁ h)) =
  l≼ (λ n → ≼l n (mono₀ (h
    (I.It.c f (λ x gx o → I.good₁ (bf x gx o)) n)
    (I.It.c g (λ y gy o → I.good₁ (bg y gy o)) n)
    (I.It.good f (λ x gx o → I.good₁ (bf x gx o)) n)
    (I.It.good g (λ y gy o → I.good₁ (bg y gy o)) n)
    (I.It.floor f (λ x gx o → I.good₁ (bf x gx o)) n)
    (I.IterCmp.bound f g (λ x gx o → I.good₁ (bf x gx o)) (λ y gy o → I.good₁ (bg y gy o))
      (λ x y gx gy o q → I.mono₁ (h x y gx gy o q)) n))))
mono₀ (C.pack gx gy (C.aa₀ p)) = ≼l 0 (mono₀ p)
mono₀ (C.pack gx gy (C.aa₁ h)) = ≼l 0 (mono₀ (h O.Ω₁ T.start))
mono₀ (C.pack gx gy (C.uu p)) = R.mono⁰ p
mono₀ (C.pack gx gy (C.uS g)) = ≼-refl _
mono₀ (C.pack gx gy (C.uS⁻ g)) = ≼-refl _
mono₀ (C.pack gx gy C.uZ) = ≼-refl _
mono₀ (C.pack gx gy C.uZ⁻) = ≼-refl _
mono₀ (C.pack gx gy (C.uL g)) = ≼-refl _
mono₀ (C.pack gx gy (C.uL⁻ g)) = ≼-refl _
mono₀ (C.pack gx gy (C.uN (O.gi {f = f} law gb))) = Chains.fwd f law
mono₀ (C.pack gx gy (C.uN⁻ (O.gi {f = f} law gb))) = Chains.rev f law
mono₀ (C.pack gx gy (C.tr p q)) = ≼-trans (mono₀ p) (mono₀ q)

sample : L.ψ⁰ F.Ω₂ ≼ L.ψ⁰ F.Ω₂
sample = mono₀ C.Ω₂-refl
```
