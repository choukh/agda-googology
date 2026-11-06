# 两种种类的折叠 (四): 闭项

> 不含记号. 入口 [HtTowerF](HtTowerF.lagda.md). $S=\cdot\omega$ 的实例 (同 `HtFeedClosed`). `TΛ Λ lΛ o`: 层 $\Lambda$ 的 $\Omega_\Lambda$ 折叠到第 0 层的输出, 世界从 $(1, 0)$ 起. 一个定义对一切合法、以第 1 层为第一位置的 $\Lambda$; 合法性是 `Lg-sum` 的一次调用. `top⁺ h = 1 ⊞ h` 给出第一位置 (同 `HtOutFeed`).
>
> 闭项的高度都用到新种类: `Ω₂ᴴ = Ωtop S₀` (新种类上的恒等分支, 与 [HtTowerU](HtTowerU.lagda.md) 的 `θ 1` 同形), 以及它的后继, 两倍, ℕ-倍的极限, 新种类上的 $x\mapsto\Omega_2\cdot x$. 读法 $\psi_0(\Omega_\Lambda)$ 是判断.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerFClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg; z⊲)
import OCF.Free.Level as FL
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop; nbᴮ; nb-contB; cont→Lg)
open import OCF.Align.HtTowerFTree
import OCF.Align.HtTowerFFold as Fold

ω⋅ : ∀ {Kd : Wd₂ → Ht → Set} {V′ : ∀ {W k} → Kd W k → Wd₂ → Set} {Z₀ Z₁ : Set} {W} → D₊ Kd V′ Z₀ Z₁ W → D₊ Kd V′ Z₀ Z₁ W
ω⋅ c = nl (λ _ → c)

one : A
one = asuc azero

W₁ : Wd₂
W₁ = one , hz

module At (Λ : Ht) (lΛ : LgB Λ) (o : ∀ {w} → hs hz ⊲[ w ] Λ) where
  open Fold ω⋅ Λ lΛ o public

  Act : ∀ {ly W} → Ig ly W
  Act p lW′ _ Y = Stp Y

  Y₀ : ∀ {W} → St W
  Y₀ = st zeroD n0 n0

  ΔΩ : Df W₁
  ΔΩ = Run accᴸ (Ωd Λ {azero , hz}) (z⊲ one , hself) (tt , tt) hself Act n0 Y₀

  ΨΩ : D₀ W₁
  ΨΩ = n1 ⨾ yc ΔΩ (τ₀ (tt , tt))

  Tψ : A
  Tψ = sum azero ΨΩ

  Lg-Tψ : Lg Tψ
  Lg-Tψ = Lg-sum azero ΨΩ tt

TΛ : ∀ Λ → LgB Λ → (∀ {w} → hs hz ⊲[ w ] Λ) → A
TΛ Λ lΛ o = At.Tψ Λ lΛ o

Lg-TΛ : ∀ Λ (lΛ : LgB Λ) (o : ∀ {w} → hs hz ⊲[ w ] Λ) → Lg (TΛ Λ lΛ o)
Lg-TΛ Λ lΛ o = At.Lg-Tψ Λ lΛ o

-- 接在第 1 层后面: 第 1 层字面地是第一位置
top⁺ : Ht → Ht
top⁺ h = hs hz ⊞ h

T⁺ : ∀ h → LgB h → A
T⁺ h lh = TΛ (top⁺ h) (Lg-⊞ (hs hz) h tt lh) (⊞-fst (hs hz) h)

Lg-T⁺ : ∀ h (lh : LgB h) → Lg (T⁺ h lh)
Lg-T⁺ h lh = Lg-TΛ (top⁺ h) (Lg-⊞ (hs hz) h tt lh) (⊞-fst (hs hz) h)
```

## 用到新种类的高度与闭项

```agda
Ω₂ᴴ : Ht
Ω₂ᴴ = Ωtop S₀

lΩ₂ : LgB Ω₂ᴴ
lΩ₂ = Lg-Ωtop S₀

-- Ω₂ · n
mul : ℕ → Ht
mul zero = hz
mul (suc n) = mul n ⊞ Ω₂ᴴ

Lg-mul : ∀ n → LgB (mul n)
Lg-mul zero = tt
Lg-mul (suc n) = Lg-⊞ (mul n) Ω₂ᴴ (Lg-mul n) lΩ₂

Ω₂ω : Ht
Ω₂ω = hl mul

Lg-Ω₂ω : LgB Ω₂ω
Lg-Ω₂ω = (λ n → ⊞-fst (mul n) Ω₂ᴴ) , Lg-mul

-- 新种类上 x ↦ Ω₂ · x (对坐标递归, 连续)
Ω₂² : Ht
Ω₂² = hΩ κH (nbᴮ hz (λ x h → h ⊞ Ω₂ᴴ))

Lg-Ω₂² : LgB Ω₂²
Lg-Ω₂² = cont→Lg (nb-contB tt (λ x h → ⊞-fst h Ω₂ᴴ) (λ x h lh → Lg-⊞ h Ω₂ᴴ lh lΩ₂))

T-Ω₂ T-Ω₂+1 T-Ω₂·2 T-Ω₂ω T-Ω₂² : A
T-Ω₂ = T⁺ Ω₂ᴴ lΩ₂
T-Ω₂+1 = T⁺ (hs Ω₂ᴴ) lΩ₂
T-Ω₂·2 = T⁺ (mul 2) (Lg-mul 2)
T-Ω₂ω = T⁺ Ω₂ω Lg-Ω₂ω
T-Ω₂² = T⁺ Ω₂² Lg-Ω₂²

Lg-T-Ω₂² : Lg T-Ω₂²
Lg-T-Ω₂² = Lg-T⁺ Ω₂² Lg-Ω₂²

ord : A → FL.Ordᶜ FL.zero
ord azero = FL.zero
ord (asuc a) = FL.suc (ord a)
ord (alim f) = FL.lim (λ n → ord (f n))

fgh : ℕ → ℕ
fgh = FL.FGH (ord T-Ω₂²)
```
