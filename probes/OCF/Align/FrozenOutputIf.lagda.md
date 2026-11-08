# 冻结输出比较的共享接口

本接口固定待比较的带种子解释器。它是验收模型，尚未证明等于实际 OT/NT。
零点参数 A 表示第一分量前缀的值；后继、ℕ-极限和 Ω 的回灌均明写。
不假定任意旧界被零界吸收。原解释器在 Ω 回灌时改种子，冻结解释器保留种子。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenOutputIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; _×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; mul)
import OCF.Lean.Fold1Fold as F
import OCF.Align.FrozenValueSecond as S

data Mode : Set where
  changing frozen : Mode

update : Mode → Cd → Cd → Cd
update changing b e = e
update frozen b e = b

module Model (A : Cd) where
  run : Mode → Cd → HB (step S⊥) → Cd
  run m b hz = A
  run m b (hs c) = hl (mul (run m b c))
  run m b (hl f) = hl (λ n → run m b (f n))
  run m b (hΩ (inj₁ ()) g)
  run m b (hΩ (inj₂ tt) g) = hl
    (F.Col.oO _⊞_ _⊞_ b b (update m)
      (λ w e → run m w (g e)) (λ w e → run m w (g e)))

  -- 明确的待检验局部律；支持谓词不能任意留空，须提供下面的实际实例。
  record SupportedComparison (P : HB (step S⊥) → Set) : Set where
    field
      actual-old : ∀ n → P (S.Old.ce n)
      actual-frozen : ∀ n → P (S.Frozen.ce n)
      at-zero : ∀ c → P c → run changing hz c ≤ᵛ run frozen hz c

  -- 共尾错位的备选接口只比较实际轨道，不要求所有合法树整支有限覆盖。
  record OutputCover : Set where
    field
      cover : ∀ n → Σ ℕ (λ k → S.Old.oo n ≤ᵛ S.Frozen.oo k)
```

`SupportedComparison` 不是已证结论：其 `at-zero` 正是交给构造与否定两侧审计
的局部律。实际 OT/NT 与模型之间的桥也仍须证明。`OutputCover` 允许输出错位，
但不能从整棵树的值比较反推此字段；它仅是充分条件候选。
接口冻结后只增加定理，不改变上述字段或解释器。

下面给出非空的结构生成域，包含全部实际外层坐标。它允许加法与整个坐标
解释器作用，不把每个 n 当成独立公设。此域尚未获得 `at-zero` 定理。

```agda
open import OCF.Lean.Fold1If using (top; Lv)
import OCF.Lean.SupCollapseClosed as C

data Generated : HB (step S⊥) → Set where
  initial : Generated (top (hs hz))
  plus : ∀ {a b} → Generated a → Generated b → Generated (a ⊞ b)
  old-step : ∀ w {c} → Generated c → Generated (S.OX w c)
  frozen-step : ∀ w {c} → Generated c → Generated (S.NX w c)

actual-old-generated : ∀ n → Generated (S.Old.ce n)
actual-old-generated zero = initial
actual-old-generated (suc n) = plus (actual-old-generated n)
  (old-step (S.Old.cw n) (actual-old-generated n))
actual-frozen-generated : ∀ n → Generated (S.Frozen.ce n)
actual-frozen-generated zero = initial
actual-frozen-generated (suc n) = plus (actual-frozen-generated n)
  (frozen-step (S.Frozen.cw n) (actual-frozen-generated n))
```
