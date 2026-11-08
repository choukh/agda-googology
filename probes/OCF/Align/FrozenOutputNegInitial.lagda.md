# 输出接口的首生成元校准

这是配对审计的局部正面定理，不是否定。对任意零点树 A 与任意同一初界 b，
两个模型在实际首生成元 top 1 上逐构造子双模拟，因此序数值双向比较。
这不证明 Generated 的闭包步保持比较，也未提供模型到实际 OT/NT 的桥。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenOutputNegInitial where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (top; _≤ᵛ_)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; same-value; same-sym)
open import OCF.Align.FrozenInnerOuter using (same-refl; same-add; same-mul)
open import OCF.Align.FrozenOutputIf
import OCF.Lean.Fold1Fold as F

module Initial (A b : Cd) where
  open Model A

  pure : ∀ m n w v {c d : Cd} → Same c d →
    Same (run m w (up c)) (run n v (up d))
  pure m n w v zz = same-refl A
  pure m n w v (ss p) = ll (same-mul (pure m n w v p))
  pure m n w v (ll p) = ll (λ k → pure m n w v (p k))

  module Old = F.Col _⊞_ _⊞_ b b (update changing)
    (λ w e → run changing w (up e)) (λ w e → run changing w (up e))
  module New = F.Col _⊞_ _⊞_ b b (update frozen)
    (λ w e → run frozen w (up e)) (λ w e → run frozen w (up e))

  coordinates : ∀ k → Same (Old.ce k) (New.ce k)
  coordinates zero = same-refl b
  coordinates (suc k) = same-add (coordinates k)
    (pure changing frozen (Old.cw k) (New.cw k) (coordinates k))

  outputs : ∀ k → Same (Old.oo k) (New.oo k)
  outputs k = pure changing frozen (Old.cw k) (New.cw k) (coordinates k)

  sums : ∀ k → Same (Old.oO k) (New.oO k)
  sums zero = outputs zero
  sums (suc k) = same-add (sums k) (outputs (suc k))

  initial-same : Same (run changing b (top (hs hz))) (run frozen b (top (hs hz)))
  initial-same = ll sums

  initial-forward : run changing b (top (hs hz)) ≤ᵛ run frozen b (top (hs hz))
  initial-forward = same-value initial-same

  initial-back : run frozen b (top (hs hz)) ≤ᵛ run changing b (top (hs hz))
  initial-back = same-value (same-sym initial-same)
```

前提可满足：A、b 是任意可数树，可取 1 与 0；首生成元的 Generated 证据是 initial。
证明不要求合法性，因为这里比较的全部分支来自 up c，按可数树结构递归即可。
任意 Ω 分支函数不具备本证明所用的 pure 律，故本证明不能充当一般 Same 输入的折叠同余。
最后一句是证明范围说明，并不是该一般命题的否定。

翻译账：复用现有树值关系与结构双模拟，没有新树、记号规则、合法性脚手架或闭项证书。
