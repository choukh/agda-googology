# 差树按层互译 (六): 用在折叠的中间层上

> 不含记号. 入口 [LayerTr](LayerTr.lagda.md). `SumOneClosed` ($S=\cdot\omega$) 的 $\psi_0(\Omega_\Omega)$ 一步 `Δ₀` 在目标第 1 层上的输出 `mid₁ : D one one` 是 `T₀`, `T₁` 的中间层之一 (`T₁` 的状态在第 1 层的差).
>
> - `Lg-mid`: `toB tt mid₁` 是合法的第 1 层布劳威尔树 (`LgB yes`). 这是 `Lg-toB` 的一次调用.
> - `mid-κ`: `mid₁` 里有 `nκ` (回灌闭包在别的层保留成节点), 所以 `difT` 读不回它 (`Ok no` 不成立).
>
> 高层没有 FGH, 也没有原来的值可比: 第 1 层树的 "值" 就是这里的 $\preccurlyeq$, 差树一侧没有独立的值. 第 0 层 (`T₀`, `T₁` 本身) 的翻译与计值在 [BrwMidZero](BrwMidZero.lagda.md) (`sum₀`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LayerTrFold where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D)
open import OCF.Align.SumOneClosed using (Δ₀; yc)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne

mid₁ : D one one
mid₁ = yc Δ₀ (inj₁ C.self) tt

Tmid : B₁ one
Tmid = toB tt mid₁

Lg-mid : LgB yes Tmid
Lg-mid = Lg-toB yes tt mid₁ (ok-yes mid₁)

mid-κ : ¬ Ok no mid₁
mid-κ (_ , (_ , (() , _)))
```
