# 有界前驱嵌入自身给出序数值下界

把本轮的结构事实兑现为值判据。此定理可以比较反馈坐标本身；不能
把任意读坐标的 Z 函数当作保序函数，再把结论传过它。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueEmbeddingValue where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Free.Level
open import OCF.Align.TotalValueBuildIf
import OCF.Free.TotalOrbitBuild as A
open import OCF.Align.ValueJudgeBase

-- 每一个限制仍只比较同一源界里的两个前驱。
restrict : ∀ {a b d} (E : BoundedEmbedding a b) (p : d ≺ᴵ a) →
  BoundedEmbedding d (BoundedEmbedding.map E p)
restrict E p = record
  { map = λ q → BoundedEmbedding.map E (≺ᴵ-trans q p)
  ; bound = λ q → BoundedEmbedding.ordered E (≺ᴵ-trans q p) p q
  ; ordered = λ q r h → BoundedEmbedding.ordered E (≺ᴵ-trans q p) (≺ᴵ-trans r p) h
  ; coherent = λ q r h → BoundedEmbedding.coherent E (≺ᴵ-trans q p) (≺ᴵ-trans r p) h
  }

branch : ∀ {f st b} (E : BoundedEmbedding (lim f st) b) n → BoundedEmbedding (f n) b
branch E n = record
  { map = λ q → BoundedEmbedding.map E (≺-lim n q)
  ; bound = λ q → BoundedEmbedding.bound E (≺-lim n q)
  ; ordered = λ q r h → BoundedEmbedding.ordered E (≺-lim n q) (≺-lim n r) h
  ; coherent = λ q r h → BoundedEmbedding.coherent E (≺-lim n q) (≺-lim n r) h
  }

read-strict : ∀ {a b} → a ≺ᴵ b → suc (A.read a) ≼ A.read b
read-strict (via e q) = ≺→s≼ (A.read-path q (A.read-cong e))

embedding-value : ∀ a {b} → BoundedEmbedding a b → A.read a ≼ A.read b
embedding-value zero E = z≼
embedding-value (suc a) E = ≼-trans (s≼s (embedding-value a (restrict E p)))
  (read-strict (BoundedEmbedding.bound E p))
  where p = via (≅ᴵ-refl a) zero
embedding-value (lim f st) E = l≼ (λ n → embedding-value (f n) (branch E n))
```

所有前提可满足：例如下一文件 TotalValueBuildEmbedding 的 cumulative
对任意 c/a 实填本嵌入。这里没有声称闭项的具名高下界已经证明。
