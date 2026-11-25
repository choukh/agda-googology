# 以旧 Ω₃ 的实际前缀检验完整 Ω₂ 查询

第四层。把 ψ₀(Ω₃) 的有限理论标尺与标准底旧折叠的前缀双向换算。旧第 n 个前缀由高度 2n+3 的 ψ₂ 塔盖住，反向可从同值证明抽出一个旧前缀。第 0、1 个旧前缀已落在同一个真实 Ω₂ 查询内。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FirstBranchOldTest where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Lean.YiRVLevel using (LEM)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; s≼s; l≼)
import B12BtboCut as Ref
import Survey.W4PTOFinite as PTO
import Survey.W4FiniteRaiseWindow as W
import Survey.W4FirstBranchLiveTest as Live
import Survey.W4FirstBranchSelf as Self
open import Survey.W4FirstBranchOldScale using (prefix; height; ceiling; early; zero-one; powers-bound; finite-powers; covers; x-base; x-ceiling; x-value; x-cofinal)
open import WVOne using (T₀)
open import OCF.Align.Value using (≼-suc; ≼-refl)

weak : ∀ {x y : T₀} → L.suc x ≼ y → x ≼ y
weak {x} p = ≼-trans {b = L.suc x} (≼-suc (≼-refl x)) p

module Compare (q : ℕ → ℕ → T₀) (full : T₀) where
  queries : T₀ → Set
  queries x = Σ ℕ (λ m → Σ ℕ (λ n → L.suc x ≼ q m n))

  module Paid (base : ∀ m → L.suc (Live.stage 2) ≼ q m 0) where
    one : ∀ m → L.suc (prefix 1) ≼ q m 0
    one m = ≼-trans {b = L.suc (Live.stage 2)} (s≼s early) (base m)
    start : ∀ m → L.suc (prefix 0) ≼ q m 0
    start m = ≼-trans {b = prefix 1} zero-one (weak (one m))
    powers : ∀ m → L.suc powers-bound ≼ q m 0
    powers m = ≼-trans {b = L.suc (Live.stage 2)} (s≼s finite-powers) (base m)

    x-start : ∀ m → L.suc (x-value 0) ≼ q m 0
    x-start m = ≼-trans {b = L.suc (Live.stage 2)} (s≼s x-base) (base m)

  cover : (f : ℕ → T₀) → Ref.finite 3 ≼ L.lim f → (∀ m n → q m n ≼ full) →
    (∀ k → queries (f k)) → Ref.finite 3 ≼ full
  cover f cofinal in-full hits = ≼-trans {b = L.lim f} cofinal (l≼ (λ k → each k (hits k)))
    where
    each : ∀ k → queries (f k) → f k ≼ full
    each k (m , n , p) = ≼-trans {b = q m n} (weak p) (in-full m n)

  pull : ∀ {x y} → x ≼ y → queries y → queries x
  pull {x} {y} le (m , n , p) = m , n , ≼-trans {b = L.suc y} (s≼s le) p

  from-old : (∀ m n → q m n ≼ full) → (∀ k → queries (prefix k)) → Ref.finite 3 ≼ full
  from-old = cover prefix covers

  to-old : (∀ j → queries (Live.stage j)) → ∀ k → queries (prefix k)
  to-old f k = pull (ceiling k) (f (height k))

  to-X : (∀ j → queries (Live.stage j)) → ∀ k → queries (x-value k)
  to-X f k = pull (x-ceiling k) (f (suc (Self.tower-index k)))

module A = Live.Live.A
module C = Compare A.Ω₂ (W.Live.full 2)
module Actual = C.Paid Live.base

sufficient : (∀ k → C.queries (prefix k)) → Ref.finite 3 ≼ W.Live.full 2
sufficient = C.from-old Live.Live.paid

necessary : LEM → Ref.finite 3 ≼ W.Live.full 2 → ∀ k → C.queries (prefix k)
necessary lem p = C.to-old (Live.Live.Row.necessary 2 lem
  (≼-trans {b = Ref.finite 3} (proj₁ (PTO.scale 2)) p))

x-sufficient : (∀ k → C.queries (x-value k)) → Ref.finite 3 ≼ W.Live.full 2
x-sufficient = C.cover x-value x-cofinal Live.Live.paid

x-necessary : LEM → Ref.finite 3 ≼ W.Live.full 2 → ∀ k → C.queries (x-value k)
x-necessary lem p = C.to-X (Live.Live.Row.necessary 2 lem
  (≼-trans {b = Ref.finite 3} (proj₁ (PTO.scale 2)) p))
```
