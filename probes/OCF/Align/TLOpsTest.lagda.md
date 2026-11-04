# 树的算子语言: 有限测试

> 入口 [TLOps](TLOps.lagda.md). **全部是有限测试 (`refl`), 不是证明.** 比较器 `same d w`: 深度 $d$, 宽度 $w$, 只读形状 (`CumUpAcceptF`). 盲区: 不读第 $w$ 项以后, 不读深度 $d$ 以下, 不读值. 相等只说明顶上几层形状相同; 不相等多半来自世界前缀 (链的下标不同), 不否定序数值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOpsTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
import OCF.Free.Closed as FC
open import OCF.Align.CumUpAcceptF using (same; TF)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; z⊲; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadAccept using (natA; lgn)
open import OCF.Align.NoCumLit using (Ord₀)
open import OCF.Align.TLOpsW using (one; g₀; Gw; gw; pos)
open import OCF.Align.TLOpsPre using (Tᵖ)
open import OCF.Align.TLOpsClo using (module Top; module Feed)
open import OCF.Align.NoCumOmega using (T⁰)
import OCF.Align.NoCumPre as NP
import OCF.Align.NoCumW as NW
import OCF.Align.LadderMonoClosed as LM
import OCF.Align.CrossMClosed as CM

two : A
two = asuc one

gtwo : Gw two
gtwo = gw tt (C.suc C.self)

ωA : A
ωA = alim natA
```

## 与旧世界同形的范围

```agda
lω : Lg ωA
lω = (λ n → C.suc C.self) , lgn

gω : Gw ωA
gω = gw lω (C.lim 1 C.self)

T₀₁ : Ord₀
T₀₁ = Tᵖ azero one one tt g₀ C.self

T₁₀ T₁₁ T₂₀ Tω₀′ : Ord₀
T₁₀ = Tᵖ one azero one tt g₀ (z⊲ one)
T₁₁ = Tᵖ one one one tt g₀ C.self
T₂₀ = Tᵖ two azero one tt g₀ (z⊲ one)
Tω₀′ = Tᵖ ωA azero one lω g₀ (z⊲ one)

-- 与 NoCumPre (高度 ℕ) 的同一个前缀树
a10 : same 6 2 T₁₀ (NP.Tᵖ 1 azero one NW.g₀ (C.z⊲ one)) ≡ true
a10 = refl
a20 : same 6 2 T₂₀ (NP.Tᵖ 2 azero one NW.g₀ (C.z⊲ one)) ≡ true
a20 = refl
-- ψ₀(Ω_Ω): 顶层闭包, 没有前缀, 与不累加的 T⁰ 同形
bΩ : same 6 2 (Top.T azero tt) T⁰ ≡ true
bΩ = refl
-- 与 OCF.Free 的树: 第一次分开的深度记下来
c0 : same 4 2 T₁₀ (TF 0) ≡ true
c0 = refl
c0′ : same 5 2 T₁₀ (TF 0) ≡ false
c0′ = refl
c1 : same 5 2 T₁₁ (TF 1) ≡ true
c1 = refl
c1′ : same 6 2 T₁₁ (TF 1) ≡ false
c1′ = refl
c·2 : same 6 2 T₂₀ FC.TΩ₂ ≡ true
c·2 = refl
c·2′ : same 7 2 T₂₀ FC.TΩ₂ ≡ false
c·2′ = refl
```

## 高度 ω 与回灌作高度

`LM.Tω₀` 是 `LadderMonoClosed` 的 $\psi_0(\Omega_{\Omega\cdot\omega})$, `CM.T⊤` 是 `CrossMClosed` 的闭项. 旧树第 0 行有 "链行第 0 项是 1", 新树的 ℕ-极限没有这一项, 基本列错开一位, 所以下面比的是错开之后的对应项 (`FS`), 再比整棵的深度.

```agda
FS : Ord₀ → ℕ → Ord₀
FS (FL.lim f) n = f n
FS x n = x

d1 : same 3 2 (FS Tω₀′ 1) (FS LM.Tω₀ 2) ≡ true
d1 = refl
```

```agda
d2 : same 2 2 (FS Tω₀′ 1) (FS LM.Tω₀ 2) ≡ true
d2 = refl
-- T⊤ (CrossMClosed) 与 Feed.T: 第 0 项分别读 ψ₀(Ω_{Ω·ω}), ψ₀(Ω_Ω): 起点不同, 所以比错开的项
e0 : same 2 2 Feed.T CM.T⊤ ≡ true
e0 = refl
```

## 前缀的账

$T_{1,0}$ 的闭包在数据树里, 带世界前缀 $1+$; `Top azero` 是顶层闭包, 没有前缀.

```agda
f0 : same 4 2 T₁₀ (Top.T azero tt) ≡ true
f0 = refl
f0′ : same 5 2 T₁₀ (Top.T azero tt) ≡ false
f0′ = refl
-- 控制: 不同的站在这里分得开
g0 : same 4 2 T₁₀ T₁₁ ≡ false
g0 = refl
```
