# `T-Ω` 的值: 有限测试

> **有限测试, 不是证明.** 不读记号. 入口 [HtVal](HtVal.lagda.md).
>
> 比较器 `agree d w x y` (`Bool`): 两棵第 0 层的树同时往下走, 后继逐个对上 (不算深度), ℕ-极限算一层深度, 只看前 $w$ 支; 深度 $d$ 用完就只比最外的构造子. 盲区: 不读第 $w$ 支以后, 不读深度 $d$ 以下, 不读值.
>
> 问的是: `T-Ω` 与 `SumOne.T₀` 的差别是不是只来自动作里 $\Omega_t$ 的写法. 测试: 参照项 `T-Ω′` (同一个折叠与输入, 动作里的 $\Omega_t$ 照 `SumOne` 写) 在 `EndLowTShape.path` 上与 `T₀` 相同 (`T-Ω` 在那里与 `T₀` 不同, 是定理 `EndLowTShape.T-Ω≇T₀`), 并且宽 3 到深度 `dd` 都相同; 对照: 同一个比较器分得开 `T-Ω` 与 `T₀`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtValTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
open FL using (Ordᶜ)
open import OCF.Align.HtFeedClosed using (ord; T-Ω)
import OCF.Align.SumOneClosed as SO
open import OCF.Align.EndLowTShape using (walk; path)
open import OCF.Align.HtValAct using (T-Ω′)

agree  : ℕ → ℕ → Ordᶜ FL.zero → Ordᶜ FL.zero → Bool
agreeL : ℕ → ℕ → ℕ → (ℕ → Ordᶜ FL.zero) → (ℕ → Ordᶜ FL.zero) → Bool
agree d w FL.zero FL.zero = true
agree d w (FL.suc x) (FL.suc y) = agree d w x y
agree zero w (FL.lim f) (FL.lim g) = true
agree (suc d) w (FL.lim f) (FL.lim g) = agreeL d w w f g
agree d w _ _ = false
agreeL d w zero f g = true
agreeL d w (suc i) f g = agree d w (f i) (g i) ∧ agreeL d w i f g
```

## 测试

```agda
-- 在 T-Ω 与 T₀ 分开的那条路径上, T-Ω′ 与 T₀ 相同
path′ : walk path (ord T-Ω′) ≡ walk path (SO.ord SO.T₀)
path′ = refl
```

```agda
t12 : agree 12 3 (ord T-Ω′) (SO.ord SO.T₀) ≡ true
t12 = refl

c12 : agree 12 3 (ord T-Ω) (SO.ord SO.T₀) ≡ false
c12 = refl
```
