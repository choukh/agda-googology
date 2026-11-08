# 全高度原 Ω̇ 1 的完整下降回收

这不是第一支包含：Cross 观察消去同步完整无累加 typed 反馈，
再由新运行器的结构相容性同步其全部累计反馈。
原高行与 cap 环境均保留，参数为非零 1；尚不把它推广至任意 η。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildRecoverActual (𝕊 : HtB) where
open import OCF.Free.Level
open import Data.Product using (proj₂)
open import OCF.Free.Floor using (Ev; flo)
open import OCF.Free.Tree using (Fl)
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Eq using (_≈ᴿ_; _≅ᶻ_; toZ-≅)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.ValLabLadder 𝕊 using (e₀; ev₀)
open import OCF.Align.TotalValueBuildRecoverGenerated 𝕊 using (one-cross)
open import OCF.Align.TotalValueBuildRecoverObserve 𝕊 using (observe)
open import OCF.Align.TotalValueTailCongruence using (run-cong; read-run-cong)
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A

one-observe : ∀ {m m′ b w} (δ : m <ᴸ m′) (ok : Ok w)
  (e : Eh h₀ m′ w (cap (κ Fl) m (flo (suc zero)))) →
  ψ̄ᵠ ok₀ e₀ (Ω̇ m (suc zero)) ≈ᴿ
  ψ̄ᵠ ok e (ι↓ {α = b} δ (Ω̇ m (suc zero)))
one-observe δ ok e = observe (one-cross δ) ok₀ e₀ ok e

one-code : ∀ {m m′ b w ℓ ℓ′} (δ : m <ᴸ m′) (ok : Ok w)
  (e : Eh h₀ m′ w (cap (κ Fl) m (flo (suc zero))))
  (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) (ev′ : Ev ℓ′ Fl) (p′ : zero <ᴵ ℓ′) →
  toZ (ψ̄ᵠ ok₀ e₀ (Ω̇ m (suc zero)) ev p) ≅ᶻ
  toZ (ψ̄ᵠ ok e (ι↓ {α = b} δ (Ω̇ m (suc zero))) ev′ p′)
one-code δ ok e ev p ev′ p′ = toZ-≅ (one-observe δ ok e ev p ev′ p′ (≅ᴵ-refl zero))

one-run : ∀ {m m′ b w ℓ ℓ′} (δ : m <ᴸ m′) (ok : Ok w)
  (e : Eh h₀ m′ w (cap (κ Fl) m (flo (suc zero))))
  (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) (ev′ : Ev ℓ′ Fl) (p′ : zero <ᴵ ℓ′) →
  R.run (toZ (ψ̄ᵠ ok₀ e₀ (Ω̇ m (suc zero)) ev p)) ≅ᴵ
  R.run (toZ (ψ̄ᵠ ok e (ι↓ {α = b} δ (Ω̇ m (suc zero))) ev′ p′))
one-run δ ok e ev p ev′ p′ = run-cong (one-code δ ok e ev p ev′ p′)

one-value : ∀ {m m′ b w ℓ ℓ′} (δ : m <ᴸ m′) (ok : Ok w)
  (e : Eh h₀ m′ w (cap (κ Fl) m (flo (suc zero))))
  (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) (ev′ : Ev ℓ′ Fl) (p′ : zero <ᴵ ℓ′) →
  A.read (R.run (toZ (ψ̄ᵠ ok₀ e₀ (Ω̇ m (suc zero)) ev p))) ≅
  A.read (R.run (toZ (ψ̄ᵠ ok e (ι↓ {α = b} δ (Ω̇ m (suc zero))) ev′ p′)))
one-value δ ok e ev p ev′ p′ = read-run-cong (one-code δ ok e ev p ev′ p′)

-- 所有环境字段在原默认合法世界中实填，不把 cap 可满足性留作条件。
one-default : ∀ {m m′} (δ : m <ᴸ m′) →
  A.read (R.run (toZ (ψ̄ᵠ ok₀ e₀ (Ω̇ m (suc zero)) ev₀ zero))) ≅
  A.read (R.run (toZ (ψ̄ᵠ ok₀
    (λ i h r → κ-cap {x = flo (suc zero)} m (λ v → proj₂ v) i (ok₀ i))
    (ι↓ {α = zero} δ (Ω̇ m (suc zero))) ev₀ zero)))
one-default {m} δ = one-value δ ok₀
  (λ i h r → κ-cap {x = flo (suc zero)} m (λ v → proj₂ v) i (ok₀ i)) ev₀ zero ev₀ zero
```
