# 两种种类的折叠 (六): 有限测试

> 不含记号. 入口 [HtTowerF](HtTowerF.lagda.md). **这些是有限测试, 不是证明.** `same d w a b`: 两棵 `A` 树到深度 $d$, 每个极限取前 $w$ 支, 构造子相同. 只说明折叠在用到新种类的层上算得出, 并且不同的层给出不同形状; 不说明值.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerFTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.HtTowerFClosed using (T-Ω₂; T-Ω₂+1; T-Ω₂·2; T-Ω₂ω)
open import OCF.Align.HtOutFeed using (T-fbω)

all< : ℕ → (ℕ → Bool) → Bool
all< zero p = true
all< (suc n) p = all< n p ∧ p n

same : ℕ → ℕ → A → A → Bool
same zero w a b = true
same (suc d) w azero azero = true
same (suc d) w (asuc a) (asuc b) = same d w a b
same (suc d) w (alim f) (alim g) = all< w (λ n → same d w (f n) (g n))
same (suc d) w _ _ = false
```

| 比较 (宽 2) | 结果 |
|---|---|
| `T-Ω₂` 对 `T-Ω₂+1` | 深度 5 同, 深度 6 不同 |
| `T-Ω₂` 对 `T-Ω₂·2` | 深度 9 同, 深度 10 不同 |
| `T-Ω₂·2` 对 `T-Ω₂ω` | 深度 4 同, 深度 5 不同 |
| `T-Ω₂` 对 `HtOut.T-fbω` (读法同为 $\psi_0(\Omega_{\Omega_2})$, 折叠不同) | 深度 4 同, 深度 5 不同 |

```agda
a5 : same 5 2 T-Ω₂ T-Ω₂+1 ≡ true
a5 = refl

a6 : same 6 2 T-Ω₂ T-Ω₂+1 ≡ false
a6 = refl

b9 : same 9 2 T-Ω₂ T-Ω₂·2 ≡ true
b9 = refl

b10 : same 10 2 T-Ω₂ T-Ω₂·2 ≡ false
b10 = refl

c4 : same 4 2 T-Ω₂·2 T-Ω₂ω ≡ true
c4 = refl

c5 : same 5 2 T-Ω₂·2 T-Ω₂ω ≡ false
c5 = refl

d4 : same 4 2 T-Ω₂ T-fbω ≡ true
d4 = refl

d5 : same 5 2 T-Ω₂ T-fbω ≡ false
d5 = refl
```

形状不同只说明折叠在这些层上不塌成同一棵树; 与 `T-fbω` 在深度 5 分开, 说明新折叠在 $\Omega_2$ 这一站与 `HtOut` 的回灌不是同一棵树, 不说明哪个值大.
