# Third: 与 RecB 闭项的对照 (有限测试)

> 不含记号. 入口 [Third](Third.lagda.md). 验收文件, 不在 `Third` 的导入闭包里. 全文 `--safe --without-K --lossy-unification`.
>
> 这里是**有限测试**: 有界展开 (深度 5, 每个 ℕ-极限只展开前 5 项) 的结点数, 由 `refl` 检查. 测试不是证明. 结果: `TN (1) 1`, `TN (1) 2` 与 RecB 的 `TN 1 1` 结点数相同 (206): 这个比较器分不开第 $2,3$ 个底, 也分不开它们与 RecB. `TN (1) 0`, `TN (3) 0` 都是 201 (第 $0$ 层的界换成 $3$ 看不出差别). 这些测试不支持也不否定任何读法.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdCmp where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdTm using (module Cn)
import OCF.Lean.RecB as R

sz : ℕ → Cd → ℕ
szs : ℕ → ℕ → (ℕ → Cd) → ℕ
sz zero x = 0
sz (suc k) hz = 1
sz (suc k) (hs x) = suc (sz (suc k) x)
sz (suc k) (hl f) = suc (szs k (suc k) f)
sz (suc k) (hΩ () g)
szs k zero f = 0
szs k (suc i) f = sz k (f i) + szs k i f

c₁ k₃ : Cd
c₁ = hs hz
k₃ = hs (hs (hs hz))

t0 : sz 5 (Cn.TN c₁ tt 0) ≡ 201
t0 = refl

t1 : sz 5 (Cn.TN k₃ tt 0) ≡ 201
t1 = refl

t2 : sz 5 (Cn.TN c₁ tt 1) ≡ sz 5 (R.TN 1 c₁ tt)
t2 = refl

t3 : sz 5 (Cn.TN c₁ tt 2) ≡ sz 5 (Cn.TN c₁ tt 1)
t3 = refl
```
