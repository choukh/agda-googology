# 用构造替代轨道证书的完整解释器

所有反馈都执行：每一步实际结果重新成为下一步的层号。不同于原
`forceᴺ`，不索取预言轨道、分支合法性、观察输出步进或旧 `GᴺTᵠ`。
代价是用加法插入界，并对所有输出取部分和，值可能改变。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.TotalOrbitBuild where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ)
open import OCF.Free.TotalOrbitIf

open import OCF.Free.TotalOrbitRun public

-- Ordᴵ 已内置合法步进；下面只忘掉证明，保留整个树骨架。
read : Ordᴵ → Ordᶜ zero
read zero = zero
read (suc a) = suc (read a)
read (lim f st) = lim (λ n → read (f n))

read-cong : ∀ {a b} → a ≅ᴵ b → read a ≅ read b
read-cong z≅ = z≅
read-cong (s≅ e) = s≅ (read-cong e)
read-cong (l≅ h) = l≅ (λ n → read-cong (h n))

read-path : ∀ {a b ℓ} {x : Ordᶜ ℓ} → a <ᴵ b → x ≅ read a → x ≺ read b
read-path zero e = ≺z e
read-path (suc q) e = ≺s (read-path q e)
read-path (lim n q) e = ≺l n (read-path q e)

push-path : ∀ {a b ℓ} {x : Ordᶜ ℓ} → a <ᴵ b → x ≺ read a → x ≺ read b
push-path zero p = ≺s p
push-path (suc q) p = ≺s (push-path q p)
push-path (lim n q) p = ≺l n (push-path q p)

read-mono : ∀ {a b} → a ⊑ᴵ b → read a ⊑⁰ read b
read-mono z⊑ ()
read-mono (s⊑ e q) (≺z d) = read-path q (≅-trans d (read-cong e))
read-mono (s⊑ e q) (≺s p) = push-path q (≅→⊑ (read-cong e) p)
read-mono (l⊑ h) (≺l n p) = read-mono (h n) p

lawful : ∀ a → HS (read a)
lawful zero = hz
lawful (suc a) = hs (lawful a)
lawful (lim f st) = hl (λ n → lawful (f n)) (λ n → read-mono (st n))

interpreter : TotalInterpreter
interpreter = record { run = run ; read = read ; lawful = lawful }

open TotalInterpreter interpreter public using (tree; legal; fgh)
```

这是真正的全域解释，不是将旧 `forceᴺ` 包一层；其定义与合法性不导入
`Goodᴺ`。不过它仍使用旧 `Z` 接口，本篇单独不构成 EBO 闭项或值证明。
