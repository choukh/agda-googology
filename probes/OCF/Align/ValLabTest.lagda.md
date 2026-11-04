# 值验收: 有限测试

> **验收文件, 有限测试, 不是证明.** 入口 [ValLab](ValLab.lagda.md). 比较器: 树的形状 `sh`, 经类型检查器计算 (`refl`). 盲区: 只看这几个点, 形状相同不说明深处相同.
>
> 这是否定结论的来路: 先看到 $X_1$ 的子树里有 $\mathrm{suc}\,X_0$, 再写成定理 (`no-val-M₂`). 定理不依赖这个测试.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValLabTest where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Free.Force using (forceᴺ)
open import OCF.Align.LadderOrdPos
open import OCF.Align.OrdLabAccept using (module G₂)
open import OCF.Align.OrdLabRead using (ev₀)

data Sh : Set where
  sz ss sl : Sh

sh : Ordᶜ zero → Sh
sh zero    = sz
sh (suc _) = ss
sh (lim _) = sl
sh (limᵢ () f)
sh (up () x)

at : Ordᶜ zero → ℕ → Ordᶜ zero
at (lim f) n = f n
at x n = x

pr : Ordᶜ zero → Ordᶜ zero
pr (suc x) = x
pr x = x

-- 码 ω·ᶜ 1 的顶, 第 1 行
X₁ : Ordᶜ zero
X₁ = forceᴺ _ (G₂.GᴺTᵠ end (suc zero) ev₀ zero)

-- X₁[1] = ψ₀(ψ_u(Ω_u)); [0] = ψ₀(ψ_u(1)); [2] = ψ₀(Ω_u·2); [0] = ψ₀(Ω_u + 1) = X₀·ω
W : Ordᶜ zero
W = at (at (at (at X₁ 1) 0) 2) 0

-- X₀·2 = X₀ + X₀; [0] = X₀ + ω; [1] = X₀ + 1
S : Ordᶜ zero
S = at (at (at W 2) 0) 1

t-suc : sh S ≡ ss
t-suc = refl

-- 它的前驱是 X₀ = [ω, t[0], …]: 第 0 项的第 1 项是后继, 第 1 项的第 1 项是极限
P : Ordᶜ zero
P = pr S

t-lim : sh P ≡ sl
t-lim = refl

t-ω : sh (at (at P 0) 1) ≡ ss
t-ω = refl

t-t₀ : sh (at (at P 1) 1) ≡ sl
t-t₀ = refl
```
