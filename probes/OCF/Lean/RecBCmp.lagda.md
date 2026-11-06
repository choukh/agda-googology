# RecB: 与 CRw 闭项的对照 (有限测试)

> 不含记号. 入口 [RecB](RecB.lagda.md). 验收文件, 不在 `RecB` 的导入闭包里. 全文 `--safe --without-K --lossy-unification`.
>
> 两边的闭项都是 `OCF.Lean.CRwBase.Cd`. 这里是**有限测试**: 有界展开 (深度 4, 每个 ℕ-极限只展开前 4 项) 的结点数, 由 `refl` 检查. 测试不是证明. 结果: `TN 0 1`, `TD 0` 与 CRw 的 `TU1`, `TU2` 相同 (深度 4); `TD 1` 与 `TD 0` 在深度 4 (都是 32) 与深度 5 都相同, 这个测试分不开它们.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RecBCmp where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
import OCF.Lean.CRw as C
open import OCF.Lean.RecB using (TN; TD)

sz : ℕ → Cd → ℕ
szs : ℕ → ℕ → (ℕ → Cd) → ℕ
sz zero x = 0
sz (suc k) hz = 1
sz (suc k) (hs x) = suc (sz (suc k) x)
sz (suc k) (hl f) = suc (szs k (suc k) f)
sz (suc k) (hΩ () g)
szs k zero f = 0
szs k (suc i) f = sz k (f i) + szs k i f

t1 : sz 4 (TN 0 (hs hz) tt) ≡ sz 4 C.TU1
t1 = refl

t2 : sz 4 (TD 0) ≡ sz 4 C.TU2
t2 = refl

t3 : sz 4 (TD 1) ≡ 32
t3 = refl

t4 : sz 5 (TD 1) ≡ sz 5 (TD 0)
t4 = refl

```

路径指纹 (沿第 2 项走 30 步, 比较 `TD 1` 与 `TD 0`) 在 6G 内超过 10 分钟未完成, 已停, 没有结果.
