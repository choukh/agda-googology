# 可数层的对角 (五): 现成的一致族上的对角闭项

> 不含记号. 入口 [DiagK](DiagK.lagda.md). 现成的、对 $n$ 一致的闭项族只有回灌族: `HtOutFeed.T-fb n` (一种种类) 与 `HtTowerNFb.T-fb₂ n` (两种种类). 它们的对角已有高度上的写法 (`T-fbω`, `T-fb₂ω`: 先在高度里取 ℕ-极限, 再折叠一次). 这里给**可数层上的**对角 (先折叠, 再在 `A` 里取部分和的极限), 合法由形状给出, 不比较两个实例的值.
>
> | 闭项 | 定义 | 读法 (判断) |
> |---|---|---|
> | `Tdg₁` | `Dg T-fb` | $\sup_n\psi_0(\Omega_{x_n})=\psi_0(\Omega_{\Omega_2})$, 同 `T-fbω` |
> | `Tdg₂` | `Dg T-fb₂` | $\psi_0(\Omega_{\Omega_3})$, 同 `T-fb₂ω` |
>
> 定理: `Lg-Tdg₁`, `Lg-Tdg₂`; 每个 `T-fb₂ n` 在值上 $\le$ `Tdg₂` (`fb₂≤`); 相邻部分和字面是第一位置. 与高度上的对角之间**没有**定理 (那是跨实例比较, `HtCross` 一类的开放问题). 这两个闭项都不是 $\psi_0\Lambda$ 的候选, 只是本路形状在现成族上的实例.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DiagKInst where

open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import OCF.Align.CumReadCF using (A; Lg)
open import OCF.Align.TLRuleSpec using (_≤_; ≤-trans)
import OCF.Free.Level as FL
open import OCF.Align.DiagKSum using (Dg; Lg-Dg; x≤pre; pre≤Dg; ord)
import OCF.Align.HtOutFeed as O1
import OCF.Align.HtFeedClosed as FC
import OCF.Align.HtTowerNFb as O2
import OCF.Align.HtTowerFClosed as TC

Lg-fb : ∀ n → Lg (O1.T-fb n)
Lg-fb n = FC.Lg-TΛ (proj₁ (O1.Λs n)) (proj₂ (O1.Λs n))

Lg-fb₂ : ∀ n → Lg (O2.T-fb₂ n)
Lg-fb₂ n = TC.Lg-T⁺ (proj₁ (O2.Λs₂ n)) (proj₂ (O2.Λs₂ n))

Tdg₁ : A
Tdg₁ = Dg O1.T-fb

Tdg₂ : A
Tdg₂ = Dg O2.T-fb₂

Lg-Tdg₁ : Lg Tdg₁
Lg-Tdg₁ = Lg-Dg O1.T-fb Lg-fb

Lg-Tdg₂ : Lg Tdg₂
Lg-Tdg₂ = Lg-Dg O2.T-fb₂ Lg-fb₂

fb₂≤ : ∀ n → O2.T-fb₂ n ≤ Tdg₂
fb₂≤ n = ≤-trans (x≤pre O2.T-fb₂ n) (pre≤Dg O2.T-fb₂ n)

fgh₁ : ℕ → ℕ
fgh₁ = FL.FGH (ord Tdg₁)

fgh₂ : ℕ → ℕ
fgh₂ = FL.FGH (ord Tdg₂)
```
