# 由实际回灌构成全部底的合法世界族

参数 `c` 是上次完整下降得到的可数树，进入第一个底的指标界；
参数 `rounds` 控制每个底执行多少次真实全槽回灌。其余界由运行输出生成，
不以预给地板充作更新结果。全部底按自然数递归，逐层保留低世界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.OutputDrivenFamily where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdTw using (Sb)
import OCF.Lean.OutputDrivenWorld as World

module Family (rounds : ℕ) (c : Cd) (lc : LgB c) where
  start : ∀ n u lu → World.Driven.State n u lu
  start zero u lu = record
    { index = c ; index-legal = lc ; bounds = λ _ → hz ; bounds-legal = λ _ → tt }
  start (suc n) u lu = World.Driven.initial (suc n) u lu

  iterate : ∀ n u lu → ℕ → World.Driven.State n u lu → World.Driven.State n u lu
  iterate n u lu zero s = s
  iterate n u lu (suc r) s = iterate n u lu r (World.Driven.next n u lu s)

  worlds : ∀ n → Wd (Sb n)
  legal : ∀ n → LgW (Sb n) (worlds n)
  worlds zero = tt
  worlds (suc n) = World.Driven.world n (worlds n) (legal n)
    (iterate n (worlds n) (legal n) rounds (start n (worlds n) (legal n)))
  legal zero = tt
  legal (suc n) = World.Driven.legal n (worlds n) (legal n)
    (iterate n (worlds n) (legal n) rounds (start n (worlds n) (legal n)))
```

此定义没有要求两个不同底的下标比较。每次原折叠内部仍携自身合法的字面
公共界；不同底之间通过原 `Sb` 的类型结构和完整下降相连。
