# 每次真实反馈的完整前驱嵌入

新增前缀界并非只有一个值不等式：原低输出的每个前驱可一致、保序地
映入新坐标。此处对完整原反馈列给出实例，未把输出回调当作保序函数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueBuildEmbedding where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ)
open import OCF.Align.TotalValueBuildIf
import OCF.Free.TotalOrbitRun as R

shift-predecessor : ∀ c {a b} → a ≺ᴵ b → R.add c a ≺ᴵ R.add c b
shift-predecessor c (via e p) = via (R.add-cong c e) (R.add-path c p)

cumulative : ∀ c a → BoundedEmbedding a (R.add c a)
cumulative c a = record
  { map = λ {d} p → R.add c d
  ; bound = λ p → shift-predecessor c p
  ; ordered = λ p q r → shift-predecessor c r
  ; coherent = λ p q e → R.add-cong c e
  }

contract : CumulativeEmbedding
contract = record { cumulative = cumulative }

-- 这里直接取实际节点回调，而不重建一条可能证据不同的轨道。
module Actual (c : Ordᴵ) (t : Z)
  (g : (η : Ordᴵ) → c ⊑ᴵ η → Z)
  (o₀ : Z) (o : (η : Ordᴵ) → c ⊑ᴵ η → Z) where

  initial-embedded : BoundedEmbedding (R.run t) (R.add c (R.run t))
  initial-embedded = cumulative c (R.run t)

  feedback-embedded : ∀ η (e : c ⊑ᴵ η) →
    BoundedEmbedding (R.run (g η e)) (R.add c (R.run (g η e)))
  feedback-embedded η e = cumulative c (R.run (g η e))

  actual-node : Z
  actual-node = ĉᴸ c t g o₀ o
```

feedback-embedded 量化原节点全部可入回调，故包括原运行器每一次实际
调用，不复制其私有 coord/coord-bound。未声称旧轨道 η 与新轨道 ζ
已经相关。要完成高值下界，还必须对原 Ω̇ 生成的 g/o 同时证明：相关
旧坐标和新坐标产生相关低输出及有向观察输出。任意 Goodᴺ 节点没有
该性质，既有反例仍然适用。
