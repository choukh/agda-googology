# 种类塔上的一级折叠 (三): 有限测试 (在 `LvKtTest.B₁` 上)

> 不含记号. 入口 [KcFold](KcFold.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. **本篇全是有限测试** (具体输入上的 `refl`), 不是对一切输入的定理.
>
> 码目标取 `LvKtTest.B₁` (第 0 站用 `foldFinK` 折叠后真回灌一站的层号, 第 2 支里有种类 `(inj₂ 1, inj₂ tt)` 的 $\Omega$-结点, `LvKtTest.t-cells`). `KcFoldTop.foldTop` 在它的顶码上的读回是 `hs (top B₁)`, `B₁` 的头是 ℕ-极限, 所以 `top B₁` 是各支级顶的部分和. 测的是: `B₁` 的第 2 支的头就是那个 $\Omega$-结点 (`t-cell2`); 读回的第 2 个部分和的头是第 2 个分量里的 $\Omega$-结点 (`t-rt-idx`). 因为第 2 支的头是 $\Omega$-极限, `top` 在那里只走底支 (`KcFoldTop` §1 末): **在 `LvKtTest.B₁` 上, 读回只看见 $\Omega$-结点的底坐标那一支** (`code-botK` 的现象). 本路的塔 (`KcFoldTower`) 起点取 $1$, 读回后加 $1$, 层号的头从第 1 站起都是后继, 不经过这一行. 比较器: 头是否 $\Omega$-结点 (`isΩ`), 头的种类的分量下标 (`kidx`). 盲区: 只看头, 不看分支内部.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KcFoldTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.LvKtIf
import OCF.Align.LvKtTest as LT
open import OCF.Align.KcFoldTop

isΩ : ∀ {S : KS} → HB S → ℕ
isΩ (hΩ κ g) = 1
isΩ _ = 0

kidx : ∀ {F : ℕ → KS} → HB (sup ℕ F) → ℕ ⊎ ⊤
kidx (hΩ (n , κ) g) = inj₁ n
kidx _ = inj₂ tt

cellL : ∀ {S : KS} → HB S → ℕ → HB S
cellL (hl f) = f
cellL _ = λ _ → hz

rtB₁ : HB (Lev LT.B₁)
rtB₁ = top LT.B₁

-- 层号 B₁ 的第 2 支的头就是那个 Ω-结点 (种类 (inj₂ 1, …))
t-cell2 : isΩ (cellL LT.B₁ 2) ≡ 1
t-cell2 = refl

-- 读回的第 2 个部分和的头是第 2 个分量里的 Ω-结点
t-rt-idx : kidx (cellL rtB₁ 2) ≡ inj₁ 2
t-rt-idx = refl
```
