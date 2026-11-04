# 序数高度的世界: 有限对照

> **验收文件.** 这里读 `OCF.Free` 带标签的树, `CumUp`, `LadderOrd`, `CrossM` 的树. **全部是有限测试** (`refl`), 比较器 `same d w`: 深度 $d$, 宽度 $w$, 只读形状 (`CumUpAcceptF.fpO`). 盲区: 只看前 $w$ 项, 前 $d$ 层; 形状相同不等于树相同, 不是基本列验收, 不是序数值验收. 第一次不等来自链的下标不同, 不否定序数值. **这个文件之外的 `CumHt*` 不读记号**; 下面的比较不进任何定义.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumHtAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
import OCF.Free.Closed as FC
open import OCF.Align.CumReadCF using (A; azero; asuc; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadAccept using (natA; lgn)
open import OCF.Align.CumUpAccept using (T+; gN)
open import OCF.Align.CumUpAcceptF using (TF; T·2; same)
open import OCF.Align.LadderOrdCode using (ωᶜ)
import OCF.Align.LadderOrdClosed as LC
import OCF.Align.CrossMClosed as XM
open import OCF.Align.CumHtBase using (Ord₀; ⟨_,_⟩; one; g₀; Gw; gw; _,ᵈ_; Dz)
open import OCF.Align.CumHt using (module Cum; Tω; Tω²)

two : A
two = asuc one

g₂ : Gw two
g₂ = gw (lgn 2) (C.suc C.self)

-- r = 0, p 是有限的, 与 CumUp 的 p : ℕ 对应
TΩ : Ord₀
TΩ = Cum.Tψ ⟨ 0 , one ⟩ azero one g₀ (C.self ,ᵈ z⊲ one)

TΩ+1 : Ord₀
TΩ+1 = Cum.Tψ ⟨ 0 , one ⟩ one one g₀ (C.self ,ᵈ C.self)

TΩ·2 : Ord₀
TΩ·2 = Cum.Tψ ⟨ 0 , two ⟩ azero two g₂ (C.self ,ᵈ z⊲ two)
```

## §1 $r=0$, $p$ 有限: 对 `CumUp`

**比较器能走到的最深处都相等** (这里只试了下面这些). 这是回归测试: 高度换成 `A` 之后, 这一段形状没有变.

```agda
u₀ : same 7 2 TΩ (T+ 0) ≡ true
u₀ = refl

u₁ : same 7 2 TΩ+1 (T+ 1) ≡ true
u₁ = refl

u₂ : same 7 2 TΩ·2 T·2 ≡ true
u₂ = refl
```

## §2 对 `OCF.Free` 带标签的树

与 `CumUpAcceptF` 同一组: 标签贴在右边, 只有形状的有限测试.

```agda
f₀ : same 4 2 TΩ (TF 0) ≡ true
f₀ = refl

f₁ : same 4 2 TΩ+1 (TF 1) ≡ true
f₁ = refl

f₂ : same 4 2 TΩ·2 FC.TΩ₂ ≡ true
f₂ = refl
```

## §3 对 `LadderOrd`: $p$ 过 $\omega$

`LC.Tᶜ ωᶜ` 由定理 `anchor-ω` 连到带标签的树, 读作 $\psi_0(\Omega_{\Omega\cdot\omega})$ (判断).

```agda
l₀ : same 4 2 Tω (LC.Tᶜ ωᶜ FL.zero) ≡ true
l₀ = refl

l₁ : same 3 2 Tω² LC.Tω² ≡ true
l₁ = refl
```

## §4 对 `CrossM`: $\Omega^2$

**深度 4 上已经不等.** `T⊤` 的高度链是码链, 这里是下标链, 第 1 项开始不同. 两棵树的序数值之间没有定理, 这里不下结论 (`CumVal` 那一路的事).

```agda
x₀ : same 3 2 (Cum.T² 0) XM.T⊤ ≡ true
x₀ = refl

x₁ : same 4 2 (Cum.T² 0) XM.T⊤ ≡ false
x₁ = refl
```
