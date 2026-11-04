# 验收: 高度世界的树对 `OCF.Free` 的树

> **验收文件.** 这里读 `OCF.Free` 的树 (标签贴在它上面). 全部是 **有限测试** (`refl`), 比较器 `fpO d w`: 深度 $d$, 宽度 $w$, 只读形状. 盲区: 只看前 $w$ 项, 只看前 $d$ 层; 不读后面的项; 形状相同不等于树相同. 这不是基本列验收, 不是前驱结构验收, 也不是序数值验收.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumUpAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
open import OCF.Free.Level using (natᴵ; FGH)
open import OCF.Align.CumReadAccept using (Fp; fpO; natA; lgn; gF; fpZ)
open import OCF.Align.CumReadBase using (Ord₀)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; z⊲; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadW using (one; Gw; gw; g₀)
open import OCF.Align.CumReadTop using (Tᶜ)
open import OCF.Align.CumUpW using (Tψ)

gN : ∀ n → Gw (natA (suc n))
gN zero = g₀
gN (suc n) = gw (lgn (suc (suc n))) (C.suc (Gw.pos (gN n)))

T+ : ℕ → Ord₀
T+ zero = Tψ 1 azero one g₀ (z⊲ one)
T+ (suc n) = Tψ 1 (natA (suc n)) (natA (suc n)) (gN n) C.self

T0 : ℕ → Ord₀
T0 zero = Tψ 0 azero one g₀ (z⊲ one)
T0 (suc n) = Tψ 0 (natA (suc n)) (natA (suc n)) (gN n) C.self
```

## §1 $\psi_0(\Omega_n)$

```agda
c0 : fpO 5 2 (T0 0) ≡ fpZ 5 2 (gF 0)
c0 = refl
c1 : fpO 5 2 (T0 1) ≡ fpZ 5 2 (gF 1)
c1 = refl
c2 : fpO 5 2 (T0 2) ≡ fpZ 5 2 (gF 2)
c2 = refl
c3 : fpO 5 2 (T0 3) ≡ fpZ 5 2 (gF 3)
c3 = refl
```

## §2 $\psi_0(\Omega_\Omega)$ 对上一轮的 $T^c$

```agda
tc : fpO 4 2 (T+ 0) ≡ fpO 4 2 Tᶜ
tc = refl
ctl : fpO 4 2 (T+ 0) ≡ fpO 4 2 (T+ 1) → Data.Empty.⊥
ctl ()
```
