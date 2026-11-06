# 跨层值同余 (二): 先试反驳 `MidMono`, 有限测试

> 不含记号. 入口 [KValC](KValC.lagda.md). 按作者 2026-11-05 的决定, 证 `MidMono` 之前先试反驳. `MidMono` 推出 (经 `KValInst.mono-lo`, `Step` 的上下文, 空状态, 底 $0$): 层 $1$ 的分支的值 $\le$ 层 $\lim_n 1$ 的 (两者值相同, 所以两个方向), 也 $\le$ 层 $2$ 的. 本文算这三个值的基本列读数 `G k`. **只是有限测试**: `G k` 对 $\le$ 不单调, 读数的大小不推出 (也不否定) $\le$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KValCTest where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (n0)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValSound using (sd; Ob)
open import OCF.Align.KValInst using (StepA; lim1; lg1; one⊲lim1)
open import OCF.Align.KValCMid using (uMid)

two : A
two = asuc one

Y∅ : ∀ {W} → F.St W
Y∅ = F.st F.zeroD n0

vOne vLim vTwo : A
vOne = Ob (sd one tt C.self StepA) azero (uMid C.self tt) C.self n0 Y∅
vLim = Ob (sd lim1 lg1 one⊲lim1 StepA) azero (uMid one⊲lim1 lg1) C.self n0 Y∅
vTwo = Ob (sd two tt (C.suc C.self) StepA) azero (uMid (C.suc C.self) tt) C.self n0 Y∅

G : ℕ → A → ℕ
G n azero = 0
G n (asuc a) = ℕ.suc (G n a)
G n (C.alim f) = G n (f n)
```

## 测试

`G 0` 三者都是 $0$ (`refl`). `G 1` 在交互求值里三个都在 4G 堆上限内耗尽 (退出码 251), 没有读数. 所以这一轮的测试**没有分辨力**: 既没有反驳 `MidMono`, 也不支持它.

```agda
test-G0 : (G 0 vOne ≡ 0) × ((G 0 vLim ≡ 0) × (G 0 vTwo ≡ 0))
test-G0 = refl , (refl , refl)
```
