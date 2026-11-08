# 可数闭项与终点验收树的值序连接

验收专用。当前冻结路线的闭项为 CRwBase.Cd，而终点接口以
Level.Ordᶜ zero 为对象。本篇逐构造子转换并证明两个值序相互反映，
不把同名关系混用，也不改变候选、合法性或折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LambdaCountableBridge where

open import OCF.Lean.CRwBase using (Cd; hz; hs; hl; hΩ)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
import OCF.Align.Level as L
import OCF.Align.OCFSpecBase as V

read : Cd → L.Ordᶜ L.zero
read hz = L.zero
read (hs a) = L.suc (read a)
read (hl f) = L.lim (λ n → read (f n))
read (hΩ () _)

forget : L.Ordᶜ L.zero → Cd
forget L.zero = hz
forget (L.suc a) = hs (forget a)
forget (L.lim f) = hl (λ n → forget (f n))
forget (L.limᵢ () f)
forget (L.up () x)

read-mono : ∀ {a b} → a ≤ᵛ b → read a V.≼ read b
read-mono z≤ = V.z≼
read-mono (s≤s p) = V.s≼s (read-mono p)
read-mono (≤s p) = V.≼-suc (read-mono p)
read-mono (l≤ p) = V.l≼ (λ n → read-mono (p n))
read-mono (≤l n p) = V.≼l n (read-mono p)

forget-mono : ∀ {a b : L.Ordᶜ L.zero} → a V.≼ b → forget a ≤ᵛ forget b
forget-mono V.z≼ = z≤
forget-mono (V.s≼s p) = s≤s (forget-mono p)
forget-mono (V.l≼ p) = l≤ (λ n → forget-mono (p n))
forget-mono (V.≼l n p) = ≤l n (forget-mono p)
forget-mono (V.≼i {p = ()} x e p)
forget-mono (V.i≼ {p = ()} p)
forget-mono (V.≼u {r = ()} p)
forget-mono (V.u≼ {r = ()} p)

roundtrip≤ : ∀ a → forget (read a) ≤ᵛ a
roundtrip≤ hz = z≤
roundtrip≤ (hs a) = s≤s (roundtrip≤ a)
roundtrip≤ (hl f) = l≤ (λ n → ≤l n (roundtrip≤ (f n)))
roundtrip≤ (hΩ () _)

roundtrip≥ : ∀ a → a ≤ᵛ forget (read a)
roundtrip≥ hz = z≤
roundtrip≥ (hs a) = s≤s (roundtrip≥ a)
roundtrip≥ (hl f) = l≤ (λ n → ≤l n (roundtrip≥ (f n)))
roundtrip≥ (hΩ () _)

read-reflect : ∀ {a b} → read a V.≼ read b → a ≤ᵛ b
read-reflect {a} {b} p = ≤-trans (roundtrip≥ a)
  (≤-trans (forget-mono p) (roundtrip≤ b))

reference-roundtrip : ∀ a → read (forget a) L.≅ a
reference-roundtrip L.zero = L.z≅
reference-roundtrip (L.suc a) = L.s≅ (reference-roundtrip a)
reference-roundtrip (L.lim f) = L.l≅ (λ n → reference-roundtrip (f n))
reference-roundtrip (L.limᵢ () f)
reference-roundtrip (L.up () x)

-- 可直接对任意终点参照使用；候选 a 仍在独立的 Cd 定义侧。
reference-lower : ∀ {r a} → forget r ≤ᵛ a → r V.≼ read a
reference-lower {r} p = V.≼-trans
  (V.≅→≼ (L.≅-sym (reference-roundtrip r))) (read-mono p)

reference-lower-reflect : ∀ {r a} → r V.≼ read a → forget r ≤ᵛ a
reference-lower-reflect {a = a} p = ≤-trans (forget-mono p) (roundtrip≤ a)
```

任意可数参照树都可用于此连接，不需要基本列一致的标签前提。
本篇不提供 ψ₀Λ 下界；它只保证在 Cd 上完成的值比较能进入既有终点
接口，反方向也不丢失大小信息。定义仍留在 Lean，验收导入不会回流。
