# 原有限下降在有证采样关系上的目标

输入自证不是子树递归证书；本接口把期待的运行保持单独写出，不能
从记录定义推定实现存在。每次原下降带实际合法公共界及源目标位置。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseLayerNativeIf where
open import OCF.Lean.CRwBase
open import OCF.Lean.RebaseLayerIf
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunIf using (at)

record NativeComparison : Set₁ where
  field
    self : ∀ n m {B} (lB : LgB B) (pc : num n ⊲ B) (pt : num m ⊲ B)
      {a} → Value (num n) a a → Value (num m) (at n m lB pc pt a) (at n m lB pc pt a)
    compare : ∀ n m {B B′} (lB : LgB B) (lB′ : LgB B′)
      (pc : num n ⊲ B) (pc′ : num n ⊲ B′)
      (pt : num m ⊲ B) (pt′ : num m ⊲ B′)
      {a b} → Value (num n) a a → Value (num n) b b → Value (num n) a b →
      Value (num m) (at n m lB pc pt a) (at n m lB′ pc′ pt′ b)
```

前提非空：任意有限原floor均有RebaseLayerActual.floor-self，取公共
界num n及源目标hself即可。接口本身还不是该floor运行自证定理。
