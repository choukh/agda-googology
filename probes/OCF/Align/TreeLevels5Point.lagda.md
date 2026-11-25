# 第五轮：实际种子第 0→1 步的原始目标

**结果 (c) 的卡点陈述，不是已填的 Cp。** 本篇只固定原 ψ₀Λ 的实际
actual-seed 第 0 支与第 1 支。FirstStep 要求给两支各自的原 Goodᵁ，
再给其原 forceᵁ / rdR 在第 0 层读回之间的原 Cp。StepAt 只是将
同一个目标的层参数写出；没有另换合法性标准。

FirstStep 的两个计值证书均存在量化，允许选择适当的原 Goodᵁ；
没有把第四轮那一个左证书强加成唯一选择。left-good 记录一个已知
左证书，不提供右证书。right-limit 来自第三轮已核对的实际构造子。
这些定义完全保留原对象，没有用结构互模拟的模型代替读回。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevels5Point where
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.LevelFixCore using (LF; Cp; Lgl)
import OCF.Align.NoKCertEval as E
import OCF.Align.TreeLevels3FeedbackShape as A
import OCF.Align.TreeLevels4SeedZero as M
left right : E.Zᵁ
left = A.lim-at A.actual-seed 0
right = A.lim-at A.actual-seed 1
StepAt : LF → Set
StepAt k = Σ (E.Goodᵁ left) λ G₀ → Σ (E.Goodᵁ right) λ G₁ →
  Cp k (E.rdR k (E.forceᵁ left G₀)) (E.rdR k (E.forceᵁ right G₁))
FirstStep : Set
FirstStep = StepAt LF.zero
left-good : E.Goodᵁ left
left-good = M.actual-seed-zero-good
right-limit : A.IsLimit right
right-limit = A.BadPair.right-limit A.actual-bad-pair
child-good : ∀ z → A.IsLimit z → E.Goodᵁ z → ∀ n → E.Goodᵁ (A.lim-at z n)
child-good (E.lim f) A.is-limit (E.gl G step) n = G n
right-child-good : E.Goodᵁ right → E.Goodᵁ (A.lim-at right 1)
right-child-good G = child-good right right-limit G 1
OneEquality : ∀ k → E.Goodᵁ left → E.Goodᵁ right → Set
OneEquality k G₀ G₁ =
  E.rdR k (E.forceᵁ left G₀) ≡ E.rdR k (E.forceᵁ (A.lim-at right 1) (right-child-good G₁))
limit-one : ∀ k z (lim : A.IsLimit z) (G : E.Goodᵁ z) (a : E.Ord₀) →
  E.rdR k a ≡ E.rdR k (E.forceᵁ (A.lim-at z 1) (child-good z lim G 1)) →
  Cp k (E.rdR k a) (E.rdR k (E.forceᵁ z G))
limit-one k (E.lim f) A.is-limit (E.gl G step) a e = inj₂ (1 , inj₁ e)
step-from-one : ∀ k (G₀ : E.Goodᵁ left) (G₁ : E.Goodᵁ right) → OneEquality k G₀ G₁ → StepAt k
step-from-one k G₀ G₁ e = G₀ , G₁ , limit-one k right right-limit G₁ (E.forceᵁ left G₀) e
NeededAt : E.Zᵁ → LF → Set
NeededAt z k = Σ (E.Goodᵁ (A.lim-at z 0)) λ G₀ → Σ (E.Goodᵁ (A.lim-at z 1)) λ G₁ →
  Cp k (E.rdR k (E.forceᵁ _ G₀)) (E.rdR k (E.forceᵁ _ G₁))
needed-at-limit : ∀ k z → A.IsLimit z → (G : E.Goodᵁ z) → Lgl k (E.rdR k (E.forceᵁ z G)) → NeededAt z k
needed-at-limit k (E.lim f) A.is-limit (E.gl G step) l = G 0 , G 1 , proj₁ l 0
actual-step-needed : ∀ k (G : E.Goodᵁ A.actual-seed) → Lgl k (E.rdR k (E.forceᵁ A.actual-seed G)) → StepAt k
actual-step-needed k G l = needed-at-limit k A.actual-seed (A.BadPair.outer-limit A.actual-bad-pair) G l
```

**精确未决式。** 以 left / right 表示原实际两支，目标为：

```text
∃ G₀ : Goodᵁ left, ∃ G₁ : Goodᵁ right,
  Cp zero (rdR zero (forceᵁ left G₀))
          (rdR zero (forceᵁ right G₁)).
```

actual-step-needed 只是原 Lgl 定义在 ℕ 极限第 0 步的必要性展开；
它的实际 Goodᵁ / Lgl 前提尚未构造，不计候选进展，更不能反过来当作
FirstStep 的实例。needed-at-limit 的一般形式有可满足实例：令各项
都是 E.zero，G 取 gl (λ n → gz) (λ n q → q)，Lgl 是相邻自反 Cp
及各项的 tt。这个平凡实例不涉及原候选的未知证书。

**选择右支第 1 项的尝试。** OneEquality 保留原 forceᵁ / rdR 的字面
等号；step-from-one 只说这个等号若连同两份原计值证书给出，就能选
原 Dn 的有限支 1，构造原 Cp。右证书和这条等号在实际输入上均未交付。
这条充分策略没有被判为必要；原 Cp 仍允许自身相等、其它任何有限支，
或再向下走后继/极限。该尝试失败不能用于证明 FirstStep 不存在。

limit-one 的前提可满足：取 z 为零的常值 ℕ 极限、a 为零、G 为上述
全零计值证书，等号取 refl。它只验证通用构造子接线，不为实际的
right-child-good 供应 Goodᵁ right。本轮未给新的候选值或闭项。
