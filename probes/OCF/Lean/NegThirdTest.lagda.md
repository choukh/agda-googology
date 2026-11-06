# 第三种组织, 否定一路: 有限测试

> 不含记号. 入口 [NegThird](NegThird.lagda.md). 验收文件, 不在入口的导入闭包里. 全文 `--safe --without-K --lossy-unification`. **这里是有限测试, 不是证明**: `fp w d x` 是 $x$ 的结构指纹 (深度 $d$, 每个 ℕ-极限只看前 $w$ 项, 模 $1000003$ 的哈希), 由 `refl` 检查.
>
> **结果.** 第 $0$ 层的界取 $1$. `TN 1 2`, `TN 1 3` 与 RecB 的 `TN 1 1` 在 (宽 3, 深 6) 指纹相同; `TN 1 0`, `TN 1 1` 与它们不同. 宽 4 深 7, 宽 2 深 9 各在 5 分钟内没有算完 (未完成, 不是结论). 盲区: 指纹只看前几项与有限深度; 相同不说明两棵树相同, 也不说明读法相同.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegThirdTest where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdTm using (module Cn)
import OCF.Lean.RecB as R

fp : ℕ → ℕ → Cd → ℕ
fps : ℕ → ℕ → ℕ → (ℕ → Cd) → ℕ
fp w zero x = 7
fp w (suc k) hz = 1
fp w (suc k) (hs x) = 3 * fp w (suc k) x + 2
fp w (suc k) (hl f) = 5 * fps w k w f + 3
fp w (suc k) (hΩ () g)
fps w k zero f = 0
fps w k (suc i) f = (fp w k (f i) + 11 * fps w k i f) % 1000003

c₁ : Cd
c₁ = hs hz

t23 : fp 3 6 (Cn.TN c₁ tt 2) ≡ fp 3 6 (Cn.TN c₁ tt 3)
t23 = refl

t2R : fp 3 6 (Cn.TN c₁ tt 2) ≡ fp 3 6 (R.TN 1 c₁ tt)
t2R = refl

v0 : fp 3 6 (Cn.TN c₁ tt 0) ≡ 3144918
v0 = refl

v1 : fp 3 6 (Cn.TN c₁ tt 1) ≡ 4431413
v1 = refl

v2 : fp 3 6 (Cn.TN c₁ tt 2) ≡ 3802983
v2 = refl
```
