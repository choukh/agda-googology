# 高度是树 (四): 闭项

> 不含记号. 入口 [HtFeed](HtFeed.lagda.md). $S=\cdot\omega$ 的实例 (同 `SumOneClosed`, `SumHtClosed`). **一个定义对一切合法高度**: `TΛ Λ lΛ` 是层 $\Lambda$ 自己的 $\Omega_\Lambda$ (`Ωd`) 折叠到第 0 层的输出, 世界从 $1$ 起 (同 `SumOne`). 没有证书参数, 合法性是 `Lg-sum` 的一次调用. 闭项是 [HtFeedHt](HtFeedHt.lagda.md) 里的高度的实例. 读法 $\psi_0(\Omega_\Lambda)$ 是判断.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtFeedClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg; z⊲)
import OCF.Free.Level as FL
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedHt hiding (T)
import OCF.Align.HtFeedFold as Fold

ω⋅ : ∀ {Kd : A → H → Set} {V′ : ∀ {W k} → Kd W k → A → Set} {Z : Set} {W} → D₊ Kd V′ Z W → D₊ Kd V′ Z W
ω⋅ c = nl (λ _ → c)

one : A
one = asuc azero

module At (Λ : H) (lΛ : LgH Λ) where
  open Fold ω⋅ Λ lΛ public

  Act : ∀ {ly W} → Ig ly W
  Act p lW′ _ Y = Step Y

  Y₀ : ∀ {W} → St W
  Y₀ = st zeroD n0

  ΔΩ : Df one
  ΔΩ = Run accᴸ (Ωd Λ {azero}) (z⊲ one) tt hself Act n0 Y₀

  ΨΩ : D₀ one
  ΨΩ = n1 ⨾ yc ΔΩ (τ₀ tt)

  Tψ : A
  Tψ = sum azero ΨΩ

  Lg-Tψ : Lg Tψ
  Lg-Tψ = Lg-sum azero ΨΩ tt

-- ψ₀(Ω_Λ), 一切合法的 Λ
TΛ : ∀ Λ → LgH Λ → A
TΛ Λ lΛ = At.Tψ Λ lΛ

Lg-TΛ : ∀ Λ (lΛ : LgH Λ) → Lg (TΛ Λ lΛ)
Lg-TΛ Λ lΛ = At.Lg-Tψ Λ lΛ
```

## 闭项

```agda
T-Ω T-Ω+1 T-Ω·2 T-Ωω T-ΩΩ T-ΩΩω : A
T-Ω = TΛ h-Ω l-Ω
T-Ω+1 = TΛ h-Ω+1 l-Ω+1
T-Ω·2 = TΛ h-Ω·2 l-Ω·2
T-Ωω = TΛ h-Ωω l-Ωω
T-ΩΩ = TΛ h-ΩΩ l-ΩΩ
T-ΩΩω = TΛ h-ΩΩω l-ΩΩω

T-Ωk T-ΩΩk : ℕ → A
T-Ωk k = TΛ (h-Ωk k) (l-Ωk k)
T-ΩΩk k = TΛ (h-ΩΩk k) (l-ΩΩk k)

ord : A → FL.Ordᶜ FL.zero
ord azero = FL.zero
ord (asuc a) = FL.suc (ord a)
ord (alim f) = FL.lim (λ n → ord (f n))

G : ℕ → A → ℕ
G n azero = 0
G n (asuc a) = suc (G n a)
G n (alim f) = G n (f n)

fgh : ℕ → ℕ
fgh = FL.FGH (ord T-ΩΩω)
```
