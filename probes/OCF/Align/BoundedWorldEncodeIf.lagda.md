# 捕获中槽的编码与受限源关系

编码不改原运行器。中Ω分支前置捕获的中槽b，递归状态改为当前坐标e。
旧层允许完整底Ω树；SourceRel只禁中Ω右统一，不禁底Ω右统一。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldEncodeIf where
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Align.BoundedCompletionUniformIf using (Value)
open import OCF.Align.BoundedWorldValueTwoSlot using (U; V)

Old : HB V → Set
Old hz = ⊤
Old (hs a) = Old a
Old (hl f) = ∀ n → Old (f n)
Old (hΩ (inj₁ (inj₁ ())) g)
Old (hΩ (inj₁ (inj₂ _)) g) = ∀ c → Old (g c)
Old (hΩ (inj₂ _) g) = ⊥

enc : HB U → HB V → HB V
enc b hz = hz
enc b (hs a) = hs (enc b a)
enc b (hl f) = hl (λ n → enc b (f n))
enc b (hΩ (inj₁ (inj₁ ())) g)
enc b (hΩ (inj₁ (inj₂ _)) g) = hΩ (inj₁ (inj₂ tt)) (λ c → enc b (g c))
enc b (hΩ (inj₂ _) g) = hΩ (inj₂ tt) (λ e → up b ⊞ enc e (g e))

data SourceRel : HB V → HB V → Set where
  old : ∀ {a b} → Old a → Old b → Value (hs hz) a b → SourceRel a b
  ss : ∀ {a b} → SourceRel a b → SourceRel (hs a) (hs b)
  sr : ∀ {a b} → SourceRel a b → SourceRel a (hs b)
  sl : ∀ {f b} → (∀ n → SourceRel (f n) b) → SourceRel (hl f) b
  si : ∀ {a f} n → SourceRel a (f n) → SourceRel a (hl f)
  bottom : ∀ {f g : Cd → HB V} → (∀ x y → x ≤ᵛ y → SourceRel (f x) (g y)) →
    SourceRel (hΩ (inj₁ (inj₂ tt)) f) (hΩ (inj₁ (inj₂ tt)) g)
  middle : ∀ {f g : HB U → HB V} → (∀ x y → Value hz x y → SourceRel (f x) (g y)) →
    SourceRel (hΩ (inj₂ tt) f) (hΩ (inj₂ tt) g)
  uniform-bottom : ∀ {a : HB V} {g : Cd → HB V} → (∀ c → SourceRel a (g c)) →
    SourceRel a (hΩ (inj₁ (inj₂ tt)) g)
```

SourceRel不假设所有raw树自相关，也不把单向关系当作端点自证。
后续须实例化floor、原act/add及Whole.Model.ce，接口本身不证明覆盖C。
