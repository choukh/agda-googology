# 含 Ω 指标坐标的原生分类接口

上一 Ω 指标层的实际合法分支已经给出含 Ω 坐标。本篇直接把分量高度
从 Cd 提升到 HB(step S⊥)，不把它的 Ω 分支擦成自然数极限。分量的
种类若经过指标的某个分支，该分支必须在给定低世界内可入。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexClassIf where
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay

U : KS
U = step S⊥
prefix : LH
prefix = ΩL (ls lz)
Native : HB U → KS
Native c = Lv (prefix ⊕L upL (ls lz) c)

Position : (w : Wd U) → (c : HB U) → K (Native c) → Set
Position w hz κ = ⊤
Position w (hs c) (inj₁ κ) = Position w c κ
Position w (hs c) (inj₂ _) = ⊤
Position w (hl f) (n , κ) = Position w (f n) κ
Position w (hΩ (inj₁ ()) g) κ
Position w (hΩ (inj₂ _) g) (inj₁ _ , κ) = ⊤
Position w (hΩ (inj₂ _) g) (inj₂ e , κ) =
  (e ⊲ proj₂ w) × Position w (g e) κ

data Class (w : Wd U) (c : HB U) (A : Set) : Set where
  base : (κ : K (Native hz)) →
    (to : E (Native hz) κ → A) (fr : A → E (Native hz) κ) →
    (∀ a → to (fr a) ≡ a) → (∀ e → fr (to e) ≡ e) → Class w c A
  rank : (i : HB U) → hs i ⊲[ w ] c →
    (to : HB (Native i) → A) (fr : A → HB (Native i)) →
    (∀ a → to (fr a) ≡ a) → (∀ e → fr (to e) ≡ e) → Class w c A

record Classification : Set₁ where
  field
    classify : ∀ w c κ → Position w c κ → Class w c (E (Native c) κ)
```

Position 不要求比较两个裸指标；rank 中的字面公共界就是 c。后续
比较两个 rank/目标时还须同一合法 B、合法世界 w 及两条字面路径。
此接口尚不提供高层树下降或值保持，也不把模块参数当终点闭项。
