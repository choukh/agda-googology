# 前缀进入未来世界分支

对任意签名的一条构造。只用 `NextUp`，不需要坐标反向映射。
这不是升世界保值定理。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TowerWorldPrefix where
open import OCF.Lean.TowerWorldIf

module _ (S : Signature) (N : NextUp S) where
  open Signature S
  open Trees S
  open NextUp N
  _+_ : ∀ {w} → Tree w → Tree w → Tree w
  a + zero = a
  a + suc b = suc (a + b)
  a + lim f = lim (λ n → a + f n)
  a + node k g = node k (λ v p c e → lift (transw p (up v k c e)) a + g v p c e)
```
