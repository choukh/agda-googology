# 反馈关系同时保存前驱映射：基本闭包

值不等式不能反向充当前驱嵌入。本篇直接在有界嵌入上给恒等、复合、
扩目标和后继；所有被比较点仍带同一源界的前驱证据。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueEmbeddingOps where
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Free.Level
open import OCF.Align.TotalValueBuildIf
import OCF.Align.TotalValueBuildTypedEmbedding as T

identity : ∀ a → BoundedEmbedding a a
identity a = record
  { map = λ {d} p → d
  ; bound = λ p → p
  ; ordered = λ p q h → h
  ; coherent = λ p q h → h }

compose : ∀ {a b c} → BoundedEmbedding a b → BoundedEmbedding b c → BoundedEmbedding a c
compose E F = record
  { map = λ p → BoundedEmbedding.map F (BoundedEmbedding.bound E p)
  ; bound = λ p → BoundedEmbedding.bound F (BoundedEmbedding.bound E p)
  ; ordered = λ p q h → BoundedEmbedding.ordered F
      (BoundedEmbedding.bound E p) (BoundedEmbedding.bound E q) (BoundedEmbedding.ordered E p q h)
  ; coherent = λ p q h → BoundedEmbedding.coherent F
      (BoundedEmbedding.bound E p) (BoundedEmbedding.bound E q) (BoundedEmbedding.coherent E p q h) }

prec-upper : ∀ {d b c} → d ≺ᴵ b → b ⊑ᴵ c → d ≺ᴵ c
prec-upper (via e q) h = ≺ᴵ-respˡ e (sim h q)

widen : ∀ {a b c} → BoundedEmbedding a b → b ⊑ᴵ c → BoundedEmbedding a c
widen E h = record
  { map = BoundedEmbedding.map E
  ; bound = λ p → prec-upper (BoundedEmbedding.bound E p) h
  ; ordered = BoundedEmbedding.ordered E
  ; coherent = BoundedEmbedding.coherent E }

module Successor {a b : Ordᴵ} (E : BoundedEmbedding a b) where
  module P = T.PE (T.from-bounded E)

  picked : ∀ {d} → d ≺ᴵ suc a → Σ Ordᴵ (P.E d)
  picked (via e zero) = b , P.top e (≅ᴵ-refl b)
  picked (via e (suc q)) = BoundedEmbedding.map E (via e q) , P.sub (via e q) (≅ᴵ-refl _)

  bound : ∀ {d} (p : d ≺ᴵ suc a) → proj₁ (picked p) ≺ᴵ suc b
  bound (via e zero) = via (≅ᴵ-refl b) zero
  bound (via e (suc q)) = ≺-suc (BoundedEmbedding.bound E (via e q))

  result : BoundedEmbedding (suc a) (suc b)
  result = record
    { map = λ p → proj₁ (picked p)
    ; bound = bound
    ; ordered = λ p q h → P.lt′ (proj₂ (picked p)) (proj₂ (picked q)) h
    ; coherent = λ p q h → P.eq′ (proj₂ (picked p)) (proj₂ (picked q)) h }

successor : ∀ {a b} → BoundedEmbedding a b → BoundedEmbedding (suc a) (suc b)
successor E = Successor.result E
```
