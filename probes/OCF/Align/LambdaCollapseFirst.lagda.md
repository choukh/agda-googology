# 新一步折叠的首个值下界：严格超过 ω

直接验收 `TowerCollapseClosed.T`，不是重述接口。
下界树 `ω²` 定义为 ω 的有限正倍数的上确界。
证得 ω² ≤ T，因而 T 不≤ω。ε₀ 读法尚未证明，且这里没有上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LambdaCollapseFirst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Lean.CRwBase using (Cd; hz; hs; hl; S⊥; _⊞_; up)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.TowerCollapseRun using (module Run)
open import OCF.Lean.TowerCollapseClosed using (T; legal-T)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
import OCF.Align.TLRuleSpec as V
open Ops S⊥
open Run S⊥

read : Cd → A
read hz = azero
read (hs a) = asuc (read a)
read (hl f) = alim (λ n → read (f n))

add-read : ∀ a b → (read a V.⊞ read b) V.≤ read (a ⊞ b)
add-read a hz = V.≤-refl _
add-read a (hs b) = V.s≤ (add-read a b)
add-read a (hl f) = V.l≤ (λ n → V.≤l n (add-read a (f n)))

right-add : ∀ a b → read b V.≤ read (a ⊞ b)
right-add a hz = V.z≤
right-add a (hs b) = V.s≤ (right-add a b)
right-add a (hl f) = V.l≤ (λ n → V.≤l n (right-add a (f n)))

ω : Cd
ω = repeat (hs hz)

ω² : Cd
ω² = repeat ω

power : Cd → Cd
power a = fold (up a)

ω²≤second : read ω² V.≤ read (power (orbit power 1))
ω²≤second = V.≤l 0 (V.≤-refl _)

ω²≤T : read ω² V.≤ read T
ω²≤T = V.≤l 1 (V.≤-trans ω²≤second
  (right-add (power (orbit power 0)) (power (orbit power 1))))

one≤ω : asuc azero V.≤ read ω
one≤ω = V.≤l 0 (V.s≤ V.z≤)

ω+1≤ω² : asuc (read ω) V.≤ read ω²
ω+1≤ω² = V.≤l 1 (V.≤-trans
  (V.⊞-mono (V.≤-refl (read ω)) one≤ω) (add-read ω ω))

ω+1≤T : asuc (read ω) V.≤ read T
ω+1≤T = V.≤-trans ω+1≤ω² ω²≤T

not-T≤ω : read T V.≤ read ω → ⊥
not-T≤ω p = V.irr (read ω) (V.≤-trans ω+1≤T p)
```

下界来自回灌轨道第 1 项的第 0 分支，其输入正是 2；没有用全局
折叠单调，也不需要按值判定坐标。读树仅用构造子，不读记号。
下一步若证明 ε₀ 完整值，至少需要一个对迭代统一的指数下界，以及
对累加和回灌封闭的上界不变量；本文件尚未给出它们。
