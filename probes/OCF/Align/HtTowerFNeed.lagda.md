# 两种种类的折叠 (七): 一切级的折叠缺什么

> 不含记号. 入口 [HtTowerF](HtTowerF.lagda.md). `step S₀` 的折叠 ([HtTowerFFold](HtTowerFFold.lagda.md)) 用到的读回 `rd : D₁ → H₀` 把第 1 层的节点 (过第 0 层) 与旧种类的闭包, 都读成 `H₀` **自己的**种类 `tt` 的 $\Omega$-分支, 坐标原样. 换到 [HtTowerU](HtTowerU.lagda.md) 的塔, 第 $k$ 个新种类 (坐标 `HB (L k)`) 的读回层是 `θ k`. 低于 `θ k` 的层只用分量 $j<k$ 的种类 (`HtTowerStrat.below-θ`), 即 `step (L j)` 的种类. 所以读回要把它们**搬成 `L k` 的种类, 坐标可以来回换**:
>
>     KMatch S S′ = 种类的映射 km : K S → K S′, 坐标 to : E S κ → E S′ (km κ), fr 反过来, fr ∘ to = id (逐点)
>     Need = ∀ k j → j < k → KMatch (step (L j)) (L k)
>
> **`need-1`**: $k=1, j=0$ 时有, 种类映射到 `L 1` 里 $x=0$ 与 $x=1$ 两个分量, 坐标定义相等 (`refl`). **$k\ge2$ 没有构造.** 判断: `L k` 是 `Lev` 对高度的结构递归造出来的, 它的种类与 `U` 的低分量种类只能经 `Lev (ι i h)` 与 `Lev h` 的对应搬过去; 两者不是定义相等的 (`sup` 的族是函数, 相等要函数外延, 同 `HtTowerNeg.no-naive-diag` 的原因), 要改用种类结构之间的同构 (函数, 不要外延) 逐级递归地造. 这是一条未做的构造, 不是否定; 也还缺世界 (界) 的对应 (`Wd U → Wd (L k)` 保 `Bd`), 这里没有写成类型.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerFNeed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerU using (L)

record KMatch (S S′ : KS) : Set where
  field
    km    : K S → K S′
    to    : ∀ κ → E S κ → E S′ (km κ)
    fr    : ∀ κ → E S′ (km κ) → E S κ
    fr-to : ∀ κ c → fr κ (to κ c) ≡ c
open KMatch public

Need : Set
Need = ∀ k j → j <ᴺ k → KMatch (step (L j)) (L k)

-- k = 1: 旧种类到 L 1 的分量 x = 0 (即 S₀), 新种类到分量 x = 1 (即 step S₀) 的新种类
need-1 : KMatch (step (L 0)) (L 1)
need-1 = record { km = km₁ ; to = to₁ ; fr = fr₁ ; fr-to = ft₁ }
  where
  km₁ : K (step S₀) → K (L 1)
  km₁ (inj₁ tt) = hz , tt
  km₁ (inj₂ tt) = hs hz , inj₂ tt
  to₁ : ∀ κ → E (step S₀) κ → E (L 1) (km₁ κ)
  to₁ (inj₁ tt) c = c
  to₁ (inj₂ tt) c = c
  fr₁ : ∀ κ → E (L 1) (km₁ κ) → E (step S₀) κ
  fr₁ (inj₁ tt) c = c
  fr₁ (inj₂ tt) c = c
  ft₁ : ∀ κ c → fr₁ κ (to₁ κ c) ≡ c
  ft₁ (inj₁ tt) c = refl
  ft₁ (inj₂ tt) c = refl
```
