# 零层值的验收桥
验收文件；readV-mono 与 read-val 按零、后继、ℕ 极限递归，不读记号项或基本列。
导入旧值序与 K.readRW，故不把本文件列为干净的树侧模块。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTVRead where
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiKVRel as K
import OCF.Align.Level as L
import OCF.Align.Value as W
readV : V.V B.zero → L.Ordᶜ L.zero
readV V.zero = L.zero
readV (V.suc x) = L.suc (readV x)
readV (V.lim f) = L.lim (λ n → readV (f n))
readV (V.Ω () g)

readV-mono : ∀ {x y : V.V B.zero} → x V.≼ y → readV x W.≼ readV y
readV-mono V.z≼ = W.z≼
readV-mono (V.s≼s d) = W.s≼s (readV-mono d)
readV-mono (V.≼l n d) = W.≼l n (readV-mono d)
readV-mono (V.l≼ h) = W.l≼ (λ n → readV-mono (h n))
readV-mono (V.≼Ω {p = ()} z d)
readV-mono (V.Ω≼ {p = ()} h)

read-val : (x : B.Tr B.zero) → readV (V.val B.zero x) L.≅ K.readRW x
read-val B.zero = L.z≅
read-val (B.suc x) = L.s≅ (read-val x)
read-val (B.lim f a) = L.l≅ (λ n → read-val (f n))

```
