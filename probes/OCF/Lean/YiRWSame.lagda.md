# 从头重写: 与 F2 的闭项逐路径相同 (有限测试)

> 有限测试, 不是证明: 沿几条给定的下标路径走第 0 层的树 (`tr`: 记下后继 1, 极限 2, 零 0), 新块的 `twᶜ n`, `EBOᶜ` 与 F2 (`YiLegFold`) 的同名闭项记录相同.
> 两边的类型不同 (层号与树是两个归纳-递归定义), 没有转换, 所以 F2 上的值定理不由此搬来.
> 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRWSame where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import OCF.Lean.YiRWBlock as N
import OCF.Lean.YiRWFold as NF
import OCF.Lean.YiLegBlock as O
import OCF.Lean.YiLegFold as OF
```

```agda
trN : N.Tr N.zero → List ℕ → List ℕ
trN N.zero      _       = 0 ∷ []
trN (N.suc x)   l       = 1 ∷ trN x l
trN (N.lim f _) []      = 2 ∷ []
trN (N.lim f _) (n ∷ l) = 2 ∷ trN (f n) l

trO : O.Tr O.zero → List ℕ → List ℕ
trO O.zero      _       = 0 ∷ []
trO (O.suc x)   l       = 1 ∷ trO x l
trO (O.lim f _) []      = 2 ∷ []
trO (O.lim f _) (n ∷ l) = 2 ∷ trO (f n) l

qa qb qc qd : List ℕ
qa = replicate 40 0
qb = 2 ∷ replicate 40 1
qc = 1 ∷ 2 ∷ 0 ∷ 1 ∷ 2 ∷ 0 ∷ 1 ∷ 2 ∷ 0 ∷ replicate 30 1
qd = 3 ∷ 1 ∷ 2 ∷ replicate 40 0

same1a : trN (NF.twᶜ 1) qa ≡ trO (OF.twᶜ 1) qa
same1a = refl

same1b : trN (NF.twᶜ 1) qb ≡ trO (OF.twᶜ 1) qb
same1b = refl

same1c : trN (NF.twᶜ 1) qc ≡ trO (OF.twᶜ 1) qc
same1c = refl

same1d : trN (NF.twᶜ 1) qd ≡ trO (OF.twᶜ 1) qd
same1d = refl

same2a : trN (NF.twᶜ 2) qa ≡ trO (OF.twᶜ 2) qa
same2a = refl

sameΛa : trN NF.EBOᶜ qa ≡ trO OF.EBOᶜ qa
sameΛa = refl
```
