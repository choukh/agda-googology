# 验收: 不累加的树, 有限测试

> **验收文件**, 读 `OCF.Free` 带标签的树. **全部是有限测试** (`refl`), 比较器 `same d w`: 深度 $d$, 宽度 $w$, 只读形状. 盲区同 [CumUpAcceptF](CumUpAcceptF.lagda.md). 不是基本列验收, 不是前驱结构验收, 不是序数值验收.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
import OCF.Free.Closed as FC
open import OCF.Align.CumUpAcceptF using (same; TF)
open import OCF.Align.CumReadTop using (Tᶜ)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadAccept using (natA; lgn)
open import OCF.Align.NoCumLit using (Ord₀; rd; El)
open import OCF.Align.NoCumW using (one; g₀; Gw; gw; pos)
open import OCF.Align.NoCumOmega using (T⁰)
open import OCF.Align.NoCumHon using (TΩᴺ)
open import OCF.Align.NoCumPre using (Tᵖ)
open import OCF.Align.NoCumOmega using (cell; η; ys⁰)
open import OCF.Align.CumUpAcceptLedger using (GA; G)

gN : ∀ n → Gw (natA (suc n))
gN zero = g₀
gN (suc n) = gw (lgn (suc (suc n))) (C.suc (pos (gN n)))

P+ : ℕ → Ord₀
P+ zero = Tᵖ 1 azero one g₀ (z⊲ one)
P+ (suc n) = Tᵖ 1 (natA (suc n)) (natA (suc n)) (gN n) C.self

P·2 : Ord₀
P·2 = Tᵖ 2 azero one g₀ (z⊲ one)
```

## 记录

不累加的 `T⁰` 与带标签的 `TF 0` 到深度 6 同形, 累加的树到深度 4 (`CumUpAcceptF.no₀`). 带前缀的 `Tᵖ` 与累加的树第一次不同形的深度相同: 这个比较器在这几层分不开两种前缀.

```agda
okT : same 6 2 T⁰ (TF 0) ≡ true
okT = refl
okᴺ : same 6 2 TΩᴺ T⁰ ≡ true
okᴺ = refl
okᴺ′ : same 5 3 TΩᴺ T⁰ ≡ true
okᴺ′ = refl
p0 : same 4 2 (P+ 0) (TF 0) ≡ true
p0 = refl
n0 : same 5 2 (P+ 0) (TF 0) ≡ false
n0 = refl
p1 : same 5 2 (P+ 1) (TF 1) ≡ true
p1 = refl
n1 : same 6 2 (P+ 1) (TF 1) ≡ false
n1 = refl
p2 : same 6 2 (P+ 2) (TF 2) ≡ true
p2 = refl
p·2 : same 6 2 P·2 FC.TΩ₂ ≡ true
p·2 = refl
n·2 : same 7 2 P·2 FC.TΩ₂ ≡ false
n·2 = refl
```

第一个下标的慢增长值: 不累加 $0, 1, 16$. 同一位置上 `chainᶜ` 是 $2, 9, 206933$ ([CumUpAcceptLedger](CumUpAcceptLedger.lagda.md)).

```agda
_ : GA (η (cell 0)) 0 ≡ 0
_ = refl
_ : GA (η (cell 0)) 1 ≡ 1
_ = refl
_ : GA (η (cell 0)) 2 ≡ 16
_ = refl
```

