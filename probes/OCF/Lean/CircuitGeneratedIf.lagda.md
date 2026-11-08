# 原折叠输出的全分支位置：共享接口

不要求原输入或地板满足此强域。只问实际 Φ 输出是否具有它：每个 Ω
根的种类在原世界有位置，且全部裸分支递归具有同一性质。若能实填，
未来世界的新 AdT 输入不会再激活未覆盖的输出枝。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CircuitGeneratedIf where

open import Data.Unit using (⊤)
open import Data.Product using (_×_; proj₁)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw; Pos)
import OCF.Lean.ThirdFold as TF

module At (U : KS) (w : Wd U) (lw : LgW U w) where
  module Old = TF U w lw

  Full : ∀ m → HB (Tw U m) → Set
  Full m hz = ⊤
  Full m (hs h) = Full m h
  Full m (hl f) = ∀ n → Full m (f n)
  Full m (hΩ κ g) = Pos U w m κ × (∀ e → Full m (g e))

  record OutputClosure (Sn : Old.San) : Set where
    field
      outputs : ∀ m a lm t pt b h nd →
        Full t (proj₁ (Old.F.Φ Sn m a lm t pt b h nd))
```

输入与目标的比较仍由原 Φ 的合法公共高度及字面路径给出。接口不要求
输入 Full，不假定原 Gd 可迁移，也不要求种子在未来世界有证书。
它不是终点值覆盖定理；尤其不能由 Full 推出折叠没有洗掉 Ω 信息。
