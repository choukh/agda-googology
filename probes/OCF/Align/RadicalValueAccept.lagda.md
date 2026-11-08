# 算子闭包实验的已验 BTBO 下界

第 4 层验收。这里只接已有 BTBO 双向值定理，不把闭包层数解释为 Ω 塔。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RadicalValueAccept where
open import Data.Product using (proj₂)
import OCF.Lean.RadicalValueOrbit as R
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.LambdaOrderBridge as O
import OCF.Align.Level as L
import OCF.Align.Value as V
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOFull using (BTBO≈)
open import OCF.Align.NoCumsum using (BTBOᴵ)

shape : ∀ a → tr₀ a L.≅ B.read (R.read a)
shape R.S.zero = L.z≅
shape (R.S.suc a) = L.s≅ (shape a)
shape (R.S.lim f) = L.l≅ (λ n → shape (f n))
shape (R.S.limᵢ () f)

named-lower : BTBOᴵ V.≼ B.read R.tree
named-lower = V.≼-trans (proj₂ BTBO≈)
  (V.≼-trans (V.≅→≼ (shape R.S.BTBO))
    (O.forward (B.read-mono R.btbo-lower)))
```

下界为 ψ₀(Ω_Ω)，并未继承 EmbVV 的 ψ₀(Ω_{Ω·ω²})。
没有估值定理支持把后续算子层当成 EBO 新站。
