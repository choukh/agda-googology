# `nκ` 的值语义 (七): 最低一站的实例内单调, 先试反驳

> 不含记号. 入口 [KVal](KVal.lagda.md). **共同的目标** (`KVal`, `EndLow.ToLimit.mono`, `HtCross.MonoStep` 都在等它) 的最低一站: $\Lambda=$ `hs hz`, `HtCrossInst.Hs.MonoStep`. 它说: 实例 $\Lambda$ 里, 从空状态、底 $1$ 折叠 $\Omega_\Lambda$, 不超过从多一段的状态 (`Y₀ ⊕ Step Y₀`)、底 $b_0=1+\omega$ 折叠同一棵树.
>
> **先试反驳, 没有反驳出来.**
>
> - 纸面计算 (判断): 两边都是 `n1` 之后接一条链 (`ni` 在第 0 层上升), 链的每一段把上一段当第 0 层输入, 每个 `n1` 走一次 `Step`. 左边 `n1` 给 $\omega$, 链从 $\omega$ 起; 右边 `n1` 给 $\omega\cdot(1+\omega)=\omega^2$, 链从 $\omega+\omega^2$ 起. 两条链的极限都是 $\varepsilon_0$ 这一类的不动点, 右边每一项不低于左边对应项. 没有找到让右边变小的机制: 这一站没有 `nκ`, 没有换世界, 分支是常数 `n1`, 不读坐标.
> - **有限测试** (`refl`, 只是测试): 第 1 项的基本列读数 `G 1` 左边 $4$, 右边 $32$. `G 2` 在交互求值里超时, 没有算出.
> - 证明: 没有做. 要的是 `DValZero.chain` 在 `HtFeedFold` 上的同形物 (两条链起点值可比 ⇒ 链的极限可比), 它要 `DValCanon` 的规范形论证搬到 `HtFeedTree.D hz` 上 (那里的 `Gen` 写死在 `SumOneTree.D azero` 上). 估计 500 行, 判断可行.
>
> 结论档: **未反驳 (测试与纸面), 未证明.**
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KValMonoTest where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A)
open import OCF.Align.HtFeedTree using (sum; hs; hz; H; LgH)
open import OCF.Align.HtFeedClosed using (G; one)
open import OCF.Align.HtCrossInst using (module Hs; b₀)
import OCF.Align.TLRuleSpec
```

## 共同目标的陈述

```agda
-- 一切合法高度上的实例内单调 (HtCross 的 hs-reduce 由它给出 TΛ Λ ≤ TΛ (hs Λ))
MonoTarget : Set
MonoTarget = ∀ (Λ : H) (l : LgH Λ) → Hs.MonoStep Λ l

-- 最低一站
MonoTarget₁ : Set
MonoTarget₁ = Hs.MonoStep (hs hz) tt
```

## 有限测试

```agda
module Q = Hs (hs hz) tt

lhs rhs : A
lhs = sum one (Q.Q.yc Q.Q.ΔΩ (Q.Q.τ₀ tt))
rhs = sum b₀ Q.X′

-- MonoTarget₁ 就是 lhs ≤ rhs
target≡ : MonoTarget₁ ≡ (OCF.Align.TLRuleSpec._≤_ lhs rhs)
target≡ = refl

test-G1-lhs : G 1 lhs ≡ 4
test-G1-lhs = refl

test-G1-rhs : G 1 rhs ≡ 32
test-G1-rhs = refl
```
