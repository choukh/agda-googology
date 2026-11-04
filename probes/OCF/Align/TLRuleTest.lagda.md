# 折叠是和的作用: 有限测试

> **这些是有限测试, 不是证明.** 比较 FGH 的小值. 盲区: 只看几个小参数; FGH 不随序数值走. 读 `CumReadCFThm` 的 `Y` 作对照.

比较器: 慢增长 `G n` (沿第 $n$ 项走到底计后继数). 盲区: 只走一条路径, 只看小参数; 与序数值没有定理联系. `y` 取 $0,1,2$; 超过 30 秒的没有结果 (ω 在 $y=2$, $G_1$; ·2 在 $y=2$, $G_1$).

| `G n (Ψ y)` | $S=+1$ | $S=\cdot2$ | $S=\cdot\omega$ |
|---|---|---|---|
| $n=1,y=0$ | 2 | 2 | 2 |
| $n=1,y=1$ | 3 | 4 | 4 |
| $n=1,y=2$ | 7 | >30s | >30s |
| $n=2,y=0$ | 2 | 2 | 3 |
| $n=2,y=1$ | 4 | 16 | >30s |
| $n=2,y=2$ | 40 | >30s | >30s |

增长的快慢与判断一致: $+1$ 明显慢. 这不是序数值的证据. 下面只留很快的几条作回归.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLRuleTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.TLRuleSum
open import OCF.Align.TLRuleVar using (module P; module Q; one)
open import OCF.Align.TLRuleDiag using (TopΣ; fghΣ)

G : ℕ → A → ℕ
G n azero = 0
G n (asuc a) = suc (G n a)
G n (alim f) = G n (f n)

two : A
two = asuc one

_ : G 1 (Ψ azero tt) ≡ 2
_ = refl

_ : G 1 (P.Ψ one tt) ≡ 3
_ = refl

_ : G 1 (Q.Ψ one tt) ≡ 4
_ = refl

_ : G 2 (P.Ψ two tt) ≡ 40
_ = refl

_ : fgh 0 ≡ 0
_ = refl

_ : fghΣ 0 ≡ 0
_ = refl
```
