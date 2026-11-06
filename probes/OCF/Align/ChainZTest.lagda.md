# 链从 0 起 (五): 有限测试

> 入口 [ChainZ](ChainZ.lagda.md). **都是有限测试, 不是证明.** 比较器 `HtTowerFTest.same d w` (深度 $d$, 每个极限只看前 $w$ 项), 盲区: 看不见第 $w$ 项以后与深度 $d$ 以下的差别; `dp k` 是只沿前两项的深度. 每条都是 `refl` (编译即检查).
>
> - 种子取输出 (`Zs-…`) 与原折叠 (`HtTowerFClosed.T-…`) 在深度 18 内相同 (`Ω₂`, `Ω₂²`); `Zs` 自己不塌: `Zs-Ω₂` 与 `Zs-Ω₂·2` 深度 9 同、10 不同 (原折叠同为 9/10, `HtTowerFTest.b9`, `b10`).
> - 字面的 $x_0=\mathrm{bot}$ (`Z-…`): 高度 `Ω₂`, `Ω₂·2`, `Ω₂²` 在深度 18、宽度 3 内给出同一棵树, 沿前两项的深度只有 4. 与 `ChainZStall.stall` 一致: 新种类的闭包什么也不输出.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ChainZTest where

open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.HtTowerFTest using (same)
open import OCF.Align.HtTowerFClosed using (T-Ω₂; T-Ω₂²)
open import OCF.Align.ChainZClosed using (Z-Ω₂; Z-Ω₂·2; Z-Ω₂²; Zs-Ω₂; Zs-Ω₂·2; Zs-Ω₂²)

dp : ℕ → A → ℕ
dp zero a = 0
dp (suc k) azero = 0
dp (suc k) (asuc a) = suc (dp k a)
dp (suc k) (alim f) = suc (dp k (f 0) ⊔ dp k (f 1))
```

```agda
-- 种子取输出: 与原折叠相同 (深度 18)
s-Ω₂ : same 18 2 Zs-Ω₂ T-Ω₂ ≡ true
s-Ω₂ = refl

s-Ω₂² : same 18 2 Zs-Ω₂² T-Ω₂² ≡ true
s-Ω₂² = refl

-- 种子取输出: 不塌
s9 : same 9 2 Zs-Ω₂ Zs-Ω₂·2 ≡ true
s9 = refl

s10 : same 10 2 Zs-Ω₂ Zs-Ω₂·2 ≡ false
s10 = refl

-- 字面的 x₀ = bot: 三个高度同一棵树, 很浅
z-·2 : same 18 3 Z-Ω₂ Z-Ω₂·2 ≡ true
z-·2 = refl

z-² : same 18 3 Z-Ω₂ Z-Ω₂² ≡ true
z-² = refl

z-dp : dp 40 Z-Ω₂ ≡ 4
z-dp = refl

-- 两种种子在深度 3 分开
zs2 : same 2 2 Z-Ω₂ Zs-Ω₂ ≡ true
zs2 = refl

zs3 : same 3 2 Z-Ω₂ Zs-Ω₂ ≡ false
zs3 = refl
```
