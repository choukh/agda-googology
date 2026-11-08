# 实际底族上的合法证书接线：共享检验合同

本轮只检验旧 Gd 反例未覆盖的合法输入域。不改原树、折叠或合法化。
以下是候选充分合同，不是纲领必要条件；失败只否定精确合同。
限定原 Sb n 底族，不要求任意额外种类结构都满足。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CircuitLegalIf where

open import Data.Nat using (ℕ)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (Sb)
import OCF.Lean.ThirdFold as F
import OCF.Lean.ThirdRichLegBuild as Rich

-- 本合同没有比较裸下标；m 自身合法，可取 hs m 为公共上界。
LegalTransport : Set
LegalTransport = ∀ n (w v : Wd (Sb n))
  (lw : LgW (Sb n) w) (lv : LgW (Sb n) v) →
  _≤w_ (Sb n) w v → ∀ m → LgB m →
  ∀ (h : HB (Tw (Sb n) m)) → LgB h →
  F.Gd (Sb n) w lw m h → F.Gd (Sb n) v lv m h

-- 接原实际输出前，先核实富合法化能否保住所需的当前证书。
NormalGd : Set
NormalGd = ∀ n (w : Wd (Sb n)) (lw : LgW (Sb n) w)
  m → LgB m → ∀ (h : HB (Tw (Sb n) m)) →
  F.Gd (Sb n) w lw m h →
  F.Gd (Sb n) w lw m (Rich.legT n m h)
```

LegalTransport 即使成立，也仍欠 NormalGd、实际输出的生成闭包与最终
Cd 值覆盖；NormalGd 即使成立，也不从 Gd 推出新世界证书。本接口不
把两者打包成空记录，更不将条件陈述当作实填结果。
