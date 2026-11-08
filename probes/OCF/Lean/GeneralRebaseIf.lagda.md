# 任意底层种类结构上的一步重定位

把旧双槽编码改写成对结构参数 S 的一个定义。顶层种类的坐标本来就是
HB S；捕获槽与访问坐标相加后，同时用作递归捕获槽与原分支的参数。
旧种类逐枝保留。本篇不定义新层号、记号节点或额外的基本列规则。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralRebaseIf where
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedCompletionUniformIf using (TreeValue)

module Layer (S : KS) (Q : ∀ κ → E S κ → E S κ → Set) where
  R : HB S → HB S → Set
  R = TreeValue S Q
  Q⁺ : ∀ κ → E (step S) κ → E (step S) κ → Set
  Q⁺ (inj₁ κ) = Q κ
  Q⁺ (inj₂ _) = R
  R⁺ : HB (step S) → HB (step S) → Set
  R⁺ = TreeValue (step S) Q⁺

  enc : HB S → HB (step S) → HB (step S)
  enc b hz = hz
  enc b (hs a) = hs (enc b a)
  enc b (hl f) = hl (λ n → enc b (f n))
  enc b (hΩ (inj₁ κ) g) = hΩ (inj₁ κ) (λ e → enc b (g e))
  enc b (hΩ (inj₂ _) g) = hΩ (inj₂ tt) (λ e → enc (b ⊞ e) (g (b ⊞ e)))

  record Comparison : Set where
    field
      mono : ∀ {a b u v} → R⁺ a b → R u v → R⁺ (enc u a) (enc v b)
      inflate : ∀ {a b} → R⁺ a b → ∀ m → R⁺ a (enc m b)
```

R 与 R⁺ 是有向结构关系，不给任意裸坐标判等、三歧或第一位置比较。
顶层坐标的关系来自低层树自身；不假设关系自反、传递或端点自证。
Comparison 仅比较编码，尚不声称编码保合法或存在一般层的折叠值桥。
