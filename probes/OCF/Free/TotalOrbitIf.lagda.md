# 不再生产 Goodᴺ：累积解释的接口

作者允许改变序数值后，本实验删除原轨道证书的生产要求。反馈坐标用
`c + η` 保证可调用分支，输出以部分和完成；不假设新旧轨道相同。
本接口定稿后只增不改。它没有要求任意两个裸层号可比较。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.TotalOrbitIf where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z)

record TotalInterpreter : Set where
  field
    run : Z → Ordᴵ
    read : Ordᴵ → Ordᶜ zero
    lawful : ∀ a → HS (read a)

  tree : Z → Ordᶜ zero
  tree x = read (run x)

  legal : ∀ x → HS (tree x)
  legal x = lawful (run x)

  fgh : Z → ℕ → ℕ
  fgh x = FGH (tree x)
```

这里的无参数合法性是交付的一半；另一半是对具体闭项另证值界。
`TotalInterpreter` 本身没有承诺保旧值、保持任意输入的值序或已达 EBO。
