# 原 Q 底观察在新运行器中的统一正性

这是一条配对检查的正面定理。所有原 Q 构造子、合法环境及实际底目标
都覆盖；闭包只取原 observer₀，未要求任意回调单调或与旧值相同。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueNegPositive (𝕊 : HtB) where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ; Ωˢ)
open import OCF.Free.Floor using (Ev)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.ValueJudgeBase
open import OCF.Align.TotalValuePureLower using (part)
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A
import OCF.Align.TotalValueTraceShape as Trace

one : Ordᶜ zero
one = suc zero

-- 只记录一个实际正输出，所有数据均为原 Z 子树。
data Positive : Z → Set where
  ps : ∀ {x} → Positive (Z.suc x)
  pl : ∀ {f} n → Positive (f n) → Positive (Z.lim f)
  pc : ∀ {c t g o h} → Positive o → Positive (Z.ĉᴸ c t g o h)

value : ∀ {x} → Positive x → one ≼ A.read (R.run x)
value ps = s≼s z≼
value (pl {f} n h) = ≼l n (≼-trans (value h) (part (λ k → R.run (f k)) n))
value (pc {c} {t} {g} {o} {h} p) =
  ≼-trans (≼l zero (value p))
    (≅→≼ (A.read-cong (≅ᴵ-sym N.shape)))
  where module N = Trace.Node c t g o h

source : ∀ {m c φ χ w ℓ} (ok : Ok w) (e : Eh h₀ m w χ)
  (x : Q m c φ χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) →
  Positive (toZ (ψ̄ᵠ ok e x ev p))
source ok e q0 ev p = ps
source ok e (qs a) ev p = pl 1 (source ok e a ev p)
source ok e (ql f) ev p = pl 0 (source ok e (f 0) ev p)
source ok e (qi ac f) ev p with <ᴵ-dec (ac ev) p
... | injᵃ (via eq ())
... | injᵇ _ = pl 0 (source ok e (f (Ωˢ _)) ev p)
... | injᶜ _ = pl 0 (source ok e (f (Ωˢ _)) ev p)
source ok e (qŝ c t g) ev p = pc (source ok e t ev p)
source ok e (qĉ c t g o h) ev p = pc (source ok e o ev p)
source ok e (qclo t g) ev p = pc (source ok e t ev p)
source ok e (qcl q ψ s t g) ev p = pc (source ok e t ev p)
source ok e (qwk le le′ x) ev p = source ok (λ i h r → le′ i r (e i h r)) x (le ev) p
source ok e (omk r z x) ev p = source ok e x ev p
source {φ = φ} {χ = χ} ok e (qΩ↓ {n = n} {k = k} q fe ac h) ev p =
  pl 0 (source ok (e⁺ n ok e)
    (h φ (Z* χ) (intoV q (qwk fe fc* (Ω̇ n k)))) (ev , ev) p)
source {m} {φ = φ} {χ = χ} ok e (qΩ {k = k} fe r h) ev p =
  pl 0 (source ok (e⁺ m ok e)
    (h φ (Z* χ) (intoU (<→◃ r) (qwk fe fc* (Ω̇ m k)))) (ev , ev) p)

positive : ∀ {m c φ χ w ℓ} (ok : Ok w) (e : Eh h₀ m w χ)
  (x : Q m c φ χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) →
  one ≼ A.read (R.run (toZ (ψ̄ᵠ ok e x ev p)))
positive ok e x ev p = value (source ok e x ev p)
```

此处没有把旧 force 的严格上升传给新 run；它只提供新实际输出自身的
正性，可与实际部分和首项包含组合。原 q0 即给非空实例。
