# 世界索引不能自动消去证据依赖

配合 `WorldAlgebra` 检查同一个玩具定义。组合律不意味着搬运只依赖
起点和终点：这里给出同一公共上界内的两条路径，使搬运后的树
不逐支互模拟。此结论只否定无条件的证据无关性，不否定世界索引路线，
也不是序数值不等定理。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.WorldEvidence where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import OCF.Lean.Fab6Base using (Cd; hz; hs; hl; _⊲_; hself; hsuc; hlim)
open import OCF.Lean.NegFab6Idx
open import OCF.Lean.WorldCompose

tag : ∀ {a b : Cd} → a ⊲ b → ℕ
tag hself = zero
tag (hsuc p) = tag p
tag (hlim n p) = n

num : ∀ {B} → ℕ → W B
num zero = wz
num (suc n) = ws (num n)

reader : W hz
reader = wn (λ e p → num (tag p))

bound : Cd
bound = hl (λ _ → hz)

left right : hz ⊲ bound
left = hlim zero hself
right = hlim (suc zero) hself

no-evidence-independence : lift left reader ≈ lift right reader → ⊥
no-evidence-independence (n≈ f) with f bound hself
... | ()
```

前提可满足：两条路径均显式给出，且有同一个字面上界 `bound`；
没有裸下标的比较。反例利用原定义允许分支读路径中的自然数。
后续若要求证据无关，应给出稳定分支的可满足接口及闭包证明，
不能把它当成索引类型自动保证的事实。
