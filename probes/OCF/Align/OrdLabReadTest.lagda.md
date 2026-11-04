# 主线直接标: 读法的有限测试

> **验收文件, 有限测试, 不是证明.** 结论写在 [OrdLab](OrdLab.lagda.md). 比较器: 主线树的形状 `sh` 与 `FGH`, 经类型检查器计算 (`refl`). 盲区: 只看这几个点, 形状相同不说明深处相同; `FGH` 在 $0$ 上看不出差别.
>
> 这是怎么找到读法的: 码 `ω·ᶜ 1` 顶的第 0 项的第 1 项是后继, 而 $t[0]=\psi_0(\Omega_{\psi_1(1)})$ 的第 1 项 $\psi_0(\Omega_\Omega)$ 是极限. 定理形式在 [OrdLabRead](OrdLabRead.lagda.md) 的 `chain-needs-zero`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabReadTest where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Free.Force using (forceᴺ)
open import OCF.Align.LadderInfTop2 using (top)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (ω²ᶜ)
open import OCF.Align.LadderOrdInst using (M₂; e₂)
open import OCF.Align.OrdLabAccept using (module G₂; module G²)
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

TM : Ordᶜ zero
TM = forceᴺ _ (G₂.GᴺTᵠ end zero ev₀ zero)

Tω₀ : Ordᶜ zero
Tω₀ = forceᴺ _ (G₂.GᴺTᵠ (e₂ (top 0)) zero ev₀ zero)

Tpos : Ordᶜ zero
Tpos = forceᴺ _ (G².GᴺTᵠ (low (blk 1 end)) zero ev₀ zero)

-- 顶的第 0 项是 ω: 它的第 1 项是后继
t1 : sh (at (at TM 0) 1) ≡ ss
t1 = refl

-- 记号要的第 0 项 ψ₀(Ω_{ψ₁(1)}) 是树 Tω₀: 它的第 1 项 ψ₀(Ω_Ω) 是极限
t2 : sh (at Tω₀ 1) ≡ sl
t2 = refl

-- ω²ᶜ 的位置 ω·2: 第 0 项同样是 ω
t3 : sh (at (at Tpos 0) 1) ≡ ss
t3 = refl

-- FGH 在 0 上相同, 看不出差别 (盲区)
t4 : FGH TM 0 ≡ FGH Tω₀ 0
t4 = refl

-- 第 1 行也继承: ψ₀(Ω_{X+1}) 的第 0 项是第 0 行, 它的第 0 项还是 ω
T1 : Ordᶜ zero
T1 = forceᴺ _ (G₂.GᴺTᵠ end (suc zero) ev₀ zero)

t5 : sh (at (at (at T1 0) 0) 1) ≡ ss
t5 = refl
```
