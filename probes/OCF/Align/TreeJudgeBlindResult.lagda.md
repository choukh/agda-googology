# 盲测: 结果 (树这一侧, 不读记号)

> **封存之后写的.** 预测在 [TreeJudgeBlind](TreeJudgeBlind.lagda.md), [TreeJudgeBlind2](TreeJudgeBlind2.lagda.md), 这里只计值, 全部是**有限测试 (`refl`)**. 与记号的比较在 [TreeJudgeAccept](TreeJudgeAccept.lagda.md). 结论写在 [TreeJudge](TreeJudge.lagda.md).
>
> **66 条预测 (第一次 44, 第二次 22), 65 条对, 1 条错 (`pB14`).**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudgeBlindResult where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.TreeJudgeObs using (run; nclo; vio)
open import OCF.Align.TreeJudgeBlind
open import OCF.Align.TreeJudgeBlind2
```

## §1 第一次: $A,B,C,D$

```agda
r-A : pA1 ∷ pA2 ∷ pA3 ∷ pA4 ∷ pA5 ∷ pA6 ∷ pA7 ∷ pA8 ∷ pA9 ∷ pA10 ∷ pA11 ∷ []
    ≡ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
r-A = refl

r-B : pB1 ∷ pB2 ∷ pB3 ∷ pB4 ∷ pB5 ∷ pB6 ∷ pB7 ∷ pB8 ∷ pB9 ∷ pB10 ∷ pB11 ∷ pB12 ∷ pB13 ∷ pB15 ∷ pB16 ∷ []
    ≡ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
r-B = refl

r-C : pC1 ∷ pC2 ∷ pC3 ∷ pC4 ∷ pC5 ∷ pC6 ∷ pC7 ∷ pC8 ∷ []
    ≡ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
r-C = refl

r-D : pD1 ∷ pD2 ∷ pD3 ∷ pD4 ∷ pD5 ∷ pD6 ∷ pD7 ∷ []
    ≡ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
r-D = refl

r-R : pR1 ∷ pR2 ∷ [] ≡ true ∷ true ∷ []
r-R = refl
```

**猜错的一条.** `pB14`: 我预测恒等读法在 $a+a$ 上深 9 就违反 `HF`. 没有. 这是**用法的错, 不是判据的错**: 深 9 宽 2 只取样到 26 个闭包 (`n-TB`), 深 11 就违反了 (`post-TBid`, 事后探查, 不算预测). 我把 $\Omega\cdot2$ 上的深度搬过来, 没有算 $a+a$ 要多走几层.

```agda
r-B14 : pB14 ≡ false
r-B14 = refl

post-TBid : run 11 8 2 TBid ≡ just (vio (0 ∷ 1 ∷ []) 1 (1 ∷ 500 ∷ 1 ∷ 1 ∷ 101 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ []) 2)
post-TBid = refl

-- 测试的分母 (深 9 宽 2): C 只有 1 个闭包, E 只有 4 个, 这两个的 `HF` 测试力量很弱
n-TA : nclo 9 2 TA ≡ 16
n-TA = refl
n-TB : nclo 9 2 TB ≡ 26
n-TB = refl
n-TC : nclo 9 2 TC ≡ 1
n-TC = refl
n-TD : nclo 9 2 TD ≡ 59
n-TD = refl
```

## §2 第二次: $E,E^+$

**关键的一条: `pY1`..`pY6`.** 这是 `c-bra*` 在 $\psi_1(\Omega)$ 上的形式: 紧读法界恒为 1 ($\tau=2,3,5$), 恒等读法界是 $\tau$. **对取样的 $\tau$ 与这一条路径, 不是对一切 $\tau$.** `pH2`: 恒等读法在 $E^+$ 上违反 `HF`; `pH1`: 紧读法不违反, 215 个闭包.

```agda
r-E : pE1 ∷ pE2 ∷ pE3 ∷ pE4 ∷ pE5 ∷ pE6 ∷ [] ≡ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
r-E = refl

r-F : pF1 ∷ pF2 ∷ pF3 ∷ pF4 ∷ pF5 ∷ pF6 ∷ pF7 ∷ pF8 ∷ []
    ≡ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
r-F = refl

r-Y : pY1 ∷ pY2 ∷ pY3 ∷ pY4 ∷ pY5 ∷ pY6 ∷ [] ≡ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
r-Y = refl

r-H : pH1 ∷ pH2 ∷ [] ≡ true ∷ true ∷ []
r-H = refl

n-TE : nclo 9 2 TE ≡ 4
n-TE = refl
n-TE⁺ : nclo 9 2 TE⁺ ≡ 72
n-TE⁺ = refl
n-TE⁺₁₁ : nclo 11 2 TE⁺ ≡ 215
n-TE⁺₁₁ = refl
```
