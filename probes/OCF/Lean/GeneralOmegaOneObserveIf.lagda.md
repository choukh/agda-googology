# 单个旧Ω种类的可数观察

本路以已编译的Seeded完整合法轨道为输入，直接研究保留一个Ω种类
的树如何生成可数树。全部分支值与反馈都来自当前源节点的子树；
反馈从1开始，无额外累加，后继列从0份开始。规则受旧typed折叠
启发，属于新实验选择，不宣称由树唯一逼出或已经树自足。

这里只使用普通HB、一个step种类和树侧Seeded，不导入记号。与原
ψ的比较另在验收模块证明；不改既有全Ω运行器，也不将其值关系
穿过这个新观察器。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaOneObserveIf where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.GeneralOmegaSeededIf using (module Prototype)
import OCF.Lean.Fold1 as F

U : KS
U = step S⊥
floor : HB U
floor = hΩ (inj₂ tt) up
module P = Prototype U floor

iterate : ∀ {A : Set} → (A → A) → A → ℕ → A
iterate f a zero = a
iterate f a (suc n) = f (iterate f a n)
leftMul : Cd → ℕ → Cd
leftMul a zero = hz
leftMul a (suc n) = a ⊞ leftMul a n

observe : HB U → Cd
observe hz = hs hz
observe (hs a) = hl (leftMul (observe a))
observe (hl f) = hl (λ n → observe (f n))
observe (hΩ (inj₁ ()) f)
observe (hΩ (inj₂ _) f) = hl (λ n → observe
  (f (iterate (λ c → observe (f c)) (hs hz) n)))

raw : Cd
raw = observe P.whole
tree : Cd
tree = leg raw
legal : LgB tree
legal = Lg-leg raw
raw-lower : raw ≤ᵛ tree
raw-lower = inflation raw
fgh : ℕ → ℕ
fgh = F.FGH tree
```

这是一个实际合法闭项及树上FGH。raw的合法性、完成保值和具名
序数界都未在本篇断言；尤其不能只由Typed的高层单调性推导观察器
单调。此候选与已有C、D和全Ω候选的相互比较均须另证。
