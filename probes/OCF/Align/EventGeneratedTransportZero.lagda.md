# 实际异层转换的零层值验收

对原零层全部数据和任意 base，不限编码子语言。
只在零层将逐形关系送入原序数值序；不据此声称高层往返保值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventGeneratedTransportZero where
open import Data.Empty using (⊥-elim)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EventReturnCodeIf using (sz)
open import OCF.Align.EventReturnCoordIf
open import OCF.Align.EventReturnCoordBuild using (sum-related)
import OCF.Align.EventReturnValueZero as V
import OCF.Align.CumReadBase as O
open import OCF.Align.EventGeneratedTransport

zero-related : ∀ {W} (ac ac′ : AccY hz) (x : D₀ W) → E₀ x (retype ac ac′ sz x)
zero-related (acc f) (acc f′) x = go x
  where
  go : ∀ {W} (x : D₀ W) → E₀ x (retype (acc f) (acc f′) sz x)
  go n0 = ez
  go n1 = eo
  go (x ⨾ y) = ea (go x) (go y)
  go (nl d) = el (λ n → go (d n))
  go (ni () u)
  go (nκ () u)
  go (nε κ z u) = ⊥-elim (ze0 κ z)
  go (nw p x) = ewL p (ewR p (go x))

back-related : ∀ {W} (ac ac′ : AccY hz) (x : D₀ W) → E₀ x (untype ac ac′ sz x)
back-related (acc f) (acc f′) x = go x
  where
  go : ∀ {W} (x : D₀ W) → E₀ x (untype (acc f) (acc f′) sz x)
  go n0 = ez
  go n1 = eo
  go (x ⨾ y) = ea (go x) (go y)
  go (nl d) = el (λ n → go (d n))
  go (ni () u)
  go (nκ () u)
  go (nε κ z u) = ⊥-elim (ze0 κ z)
  go (nw p x) = ewL p (ewR p (go x))

sum-shape : ∀ {W} (ac ac′ : AccY hz) b (x : D₀ W) →
  V.Same (sum b x) (sum b (retype ac ac′ sz x))
sum-shape ac ac′ b x = sum-related (zero-related ac ac′ x) (V.self b)

lower : ∀ {W} (ac ac′ : AccY hz) b (x : D₀ W) →
  O.toO (sum b x) O.≼ O.toO (sum b (retype ac ac′ sz x))
lower ac ac′ b x = V.sound (sum-shape ac ac′ b x)

upper : ∀ {W} (ac ac′ : AccY hz) b (x : D₀ W) →
  O.toO (sum b (retype ac ac′ sz x)) O.≼ O.toO (sum b x)
upper ac ac′ b x = V.sound (V.reverse (sum-shape ac ac′ b x))

back-sum-shape : ∀ {W} (ac ac′ : AccY hz) b (x : D₀ W) →
  V.Same (sum b x) (sum b (untype ac ac′ sz x))
back-sum-shape ac ac′ b x = sum-related (back-related ac ac′ x) (V.self b)
```
