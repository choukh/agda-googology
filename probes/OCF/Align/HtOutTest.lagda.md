# 高度来自折叠的输出: 有限测试

> 入口 [HtOut](HtOut.lagda.md). **有限测试, 不是证明.** 比较器 `same d w` (`CumUpAcceptF`, 同 [HtFeedTest](HtFeedTest.lagda.md)): 深度 $d$, 宽度 $w=2$, 只读形状, 不读值.
>
> | 比较 | 结果 |
> |---|---|
> | `T-fb 1` 对 `T-Ω` ($\psi_0(\Omega_\Omega)$) | 深度 6 同, 深度 7 不同 |
> | `T-fb 1` 对 `T-Ωk 2` (HtFeed 的 $\psi_0(\Omega_{\Omega^2})$) | 深度 10 同, 深度 11 不同 |
> | 对照: `T-Ωk 3` 对 `T-Ωk 2` | 深度 12 同 |
> | `T-fb 2` 对 `T-fb 1` | 深度 12 同 |
>
> 读法: 第 1 行说 `T-fb 1` 不是 $\Omega$ 那一站的形状. 第 2 行与 `T-fb 1` 读 $\psi_0(\Omega_{\Omega^2})$ (判断) 不矛盾, 但对照行说这个比较器在深度 12 分不开 $\Omega^2$ 与 $\Omega^3$ 两站, 所以第 2, 4 行不支持也不否定任何值的说法.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtOutTest where

open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumUpAcceptF using (same)
open import OCF.Align.HtFeedClosed using (ord; T-Ωk; T-Ω)
open import OCF.Align.HtOutFeed using (T-fb)

a6 : same 6 2 (ord (T-fb 1)) (ord T-Ω) ≡ true
a6 = refl
a7 : same 7 2 (ord (T-fb 1)) (ord T-Ω) ≡ false
a7 = refl

b10 : same 10 2 (ord (T-fb 1)) (ord (T-Ωk 2)) ≡ true
b10 = refl
b11 : same 11 2 (ord (T-fb 1)) (ord (T-Ωk 2)) ≡ false
b11 = refl

-- 对照: 比较器分不开 Ω² 与 Ω³ 两站
c12 : same 12 2 (ord (T-Ωk 3)) (ord (T-Ωk 2)) ≡ true
c12 = refl

d12 : same 12 2 (ord (T-fb 2)) (ord (T-fb 1)) ≡ true
d12 = refl
```
