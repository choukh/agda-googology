# `Tᴰ₊` 的折叠 (二): 无条件的 `Fold₊` 与闭项

> 不含记号. 入口 [TdPlus](TdPlus.lagda.md). [DiagK3One](DiagK3One.lagda.md) 把 `towerL′` 的折叠缺的一块缩成 `Fold₊` (第 $k\ge1$ 级, 种类结构 `L′ (k+2)`), `Tᴰ₊` 条件于它. 这里给出 `Fold₊` 的一个居民:
>
> - **`fold₊`**: 第 $k$ 级把合法高度 $\Lambda$ 经一致世界的投影 ([TdPlusUni](TdPlusUni.lagda.md) 的 `pr`, 种类结构 `uL (k+2)`) 送进两种种类的折叠 `HtTowerFClosed.T⁺`. 合法由形状给出 (`Lg-T⁺`, `Lg-pr`). 回灌只有两种增量: `A` 界一齐升, 高度界一齐接同一个 $H_0$ 高度 (`T⁺` 的世界 $(a,\beta)$ 经 `uW` 就是一致世界; 与 `growL′` 的关系是 [TdPlusGrow](TdPlusGrow.lagda.md) 的定理). 不挑分量, 不判定任何相等.
> - **`Tᴰ₊`**: 无模块参数, 无前提的闭项, $=$ `DiagK3One.Tᴰ₊ fold₊` (定义相等). **`Lg-Tᴰ₊`**: 合法. **`fgh-Tᴰ₊`**: FGH. 值在 `A` (布劳威尔树: $0$, 后继, ℕ-极限) 里, 所以 `ord Tᴰ₊` 直接是 `OCF.Free.Level` 的序数.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TdPlusFold where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Align.CumReadCF using (A; Lg)
open import OCF.Align.HtTowerTy using (HB; LgB)
open import OCF.Align.HtTowerNStage using (L′)
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.HtTowerFClosed using (T⁺; Lg-T⁺)
open import OCF.Align.DiagKSum using (ord)
import OCF.Align.DiagK3One as D3
import OCF.Free.Level as FL
open import OCF.Align.TdPlusUni using (uL; module Pr)
```

## §1 第 $k\ge1$ 级的折叠

```agda
prL : ∀ k → HB (L′ k) → Ht
prL k = Pr.pr (uL k)

Lg-prL : ∀ k (Λ : HB (L′ k)) → LgB Λ → LgB (prL k Λ)
Lg-prL k = Pr.Lg-pr (uL k)

foldK : ∀ k (Λ : HB (L′ (suc (suc k)))) → LgB Λ → A
foldK k Λ lΛ = T⁺ (prL (suc (suc k)) Λ) (Lg-prL (suc (suc k)) Λ lΛ)

Lg-foldK : ∀ k Λ (lΛ : LgB Λ) → Lg (foldK k Λ lΛ)
Lg-foldK k Λ lΛ = Lg-T⁺ (prL (suc (suc k)) Λ) (Lg-prL (suc (suc k)) Λ lΛ)

fold₊ : D3.Fold₊
fold₊ = record { foldₛ = foldK ; lgₛ = Lg-foldK }
```

## §2 无条件的闭项

```agda
Tᴰ₊ : A
Tᴰ₊ = D3.Tᴰ₊ fold₊

Lg-Tᴰ₊ : Lg Tᴰ₊
Lg-Tᴰ₊ = D3.Lg-Tᴰ₊ fold₊

fgh-Tᴰ₊ : ℕ → ℕ
fgh-Tᴰ₊ = FL.FGH (ord Tᴰ₊)
```
