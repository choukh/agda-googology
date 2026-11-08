# 全原 Q 的实际底观察输出都有 SV

证明针对原 ψ̄ᵠ 的所有构造子、世界和真实底目标，不限制为有限站。
高反馈的每一个被选分支都是原 Q 的递归子项。观察证明不要求 seed
或坐标先有 SV；它们仍原样决定分支。该域比任意 Z 小，但包含原
最高 Ω̇ 端行，不附加成品证书。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueTailHighGenerated (S : HtB) where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ; Ωˢ)
open import OCF.Free.Floor using (Ev; fz; fk; _⊔_; Bd; bound; evF)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.TotalValueBuildStrict using (SV)
open import OCF.Align.TotalValueTailHighRegular S
import OCF.Align.TotalValueNegPositive S as P
import OCF.Free.TotalOrbitRun as R

source : ∀ {m c φ χ w ℓ} (ok : Ok w) (e : Eh h₀ m w χ)
  (x : Q m c φ χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) →
  Regular (ψ̄ᵠ ok e x ev p)
source ok e q0 ev p = rs rz
source ok e (qs a) ev p = repeat-regular (source ok e a ev p) (P.source ok e a ev p)
source ok e (ql f) ev p = rl (λ n → source ok e (f n) ev p)
  (λ n → P.source ok e (f (suc n)) ev p)
source ok e (qi {j = j} ac f) ev p with <ᴵ-dec (ac ev) p
... | injᵃ (via eq ())
... | injᵇ _ = rl
  (λ n → source ok e (f (iter (λ x → ψ̄ᵠ ok e (f x) ev (ac ev)) (Ωˢ j) n)) ev p)
  (λ n → P.source ok e (f (iter (λ x → ψ̄ᵠ ok e (f x) ev (ac ev)) (Ωˢ j) (suc n))) ev p)
... | injᶜ _ = rl
  (λ n → source ok e (f (iter (λ x → ψ̄ᵠ ok e (f x) ev (ac ev)) (Ωˢ j) n)) ev p)
  (λ n → P.source ok e (f (iter (λ x → ψ̄ᵠ ok e (f x) ev (ac ev)) (Ωˢ j) (suc n))) ev p)
source ok e (qŝ c t g) ev p = rsh (source ok e t ev p)
  (λ η d → source ok e (g η d) ev p) (λ η d → P.source ok e (g η d) ev p)
source ok e (qĉ c t g o h) ev p = rc (source ok e o ev p)
  (λ η d → source ok e (h η d) ev p) (λ η d → P.source ok e (h η d) ev p)
source ok e (qclo t g) ev p = rsh (source ok e t ev p)
  (λ η d → source ok e (g η) _ _) (λ η d → P.source ok e (g η) _ _)
source {χ = χ} {w = w} ok e (qcl {n = n} q ψ s t g) ev p =
  rsh (source ok e t ev p)
    (λ η d → source
      (upd-ok n w ok (_ , λ q′ → lim 0 (proj₂ (evF B) q′)))
      (λ i h r → upd-ev n i w χ (evη ψ B η d) (e i h r)) (g η) ev p)
    (λ η d → P.source
      (upd-ok n w ok (_ , λ q′ → lim 0 (proj₂ (evF B) q′)))
      (λ i h r → upd-ev n i w χ (evη ψ B η d) (e i h r)) (g η) ev p)
  where B = bound (ψ ⊔ fk zero) (s (e n (Hi-0 n) q)) (zr ok n)
source ok e (qwk le le′ x) ev p = source ok (λ i h r → le′ i r (e i h r)) x (le ev) p
source ok e (omk r z x) ev p = source ok e x ev p
source {φ = φ} {χ = χ} ok e (qΩ↓ {n = n} {k = k} q fe ac h) ev p =
  rl (λ i → source ok (e⁺ n ok e)
    (h φ (Z* χ) (intoV q (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* n))
      (Ψ q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) (h φ (Z* χ) (intoV q z)))) i)))
    (ev , ev) p)
    (λ i → P.source ok (e⁺ n ok e)
    (h φ (Z* χ) (intoV q (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* n))
      (Ψ q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) (h φ (Z* χ) (intoV q z)))) (suc i))))
    (ev , ev) p)
source {m} {φ = φ} {χ = χ} ok e (qΩ fe r h) ev p =
  rl (λ i → source ok (e⁺ m ok e)
    (h φ (Z* χ) (intoU (<→◃ r) (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* m))
      (ψᵠ r (h φ (Z* χ) (intoU (<→◃ r) z)))) i))) (ev , ev) p)
    (λ i → P.source ok (e⁺ m ok e)
    (h φ (Z* χ) (intoU (<→◃ r) (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* m))
      (ψᵠ r (h φ (Z* χ) (intoU (<→◃ r) z)))) (suc i)))) (ev , ev) p)

output-sv : ∀ {m c φ χ w ℓ} (ok : Ok w) (e : Eh h₀ m w χ)
  (x : Q m c φ χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) →
  SV (R.run (toZ (ψ̄ᵠ ok e x ev p)))
output-sv ok e x ev p = value (source ok e x ev p)
```
