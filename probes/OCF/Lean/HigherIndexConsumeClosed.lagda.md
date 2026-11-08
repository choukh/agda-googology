# 完整高层地板的合法可数闭项与内部View

输入逐字是已证Supported的原完整flL(lΩ k g)，没有截为单个组件。
raw由新全部Ω回灌运行器总递归求出；tree是已有可数完成leg作用后的
新闭项。完成可能提高值，不宣称raw本身合法或新旧折叠等值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexConsumeClosed where
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Lean.CountableCompletionRun using (inflation)
import OCF.Lean.HigherIndexSupportSource as S
import OCF.Lean.HigherIndexConsumeRun as R

raw : Cd
raw = R.run hz tt hz tt S.input (S.input-supported hz hz)
tree : Cd
tree = leg raw
legal-tree : LgB tree
legal-tree = Lg-leg raw
raw-lower : raw ≤ᵛ tree
raw-lower = inflation raw

Object : Set
Object = Σ Cd LgB
value : Object → Cd
value = proj₁

data Shape : Set where
  zero : Shape
  successor : Object → Shape
  limit : (f : ℕ → Object) → (∀ n → value (f n) ⊲ value (f (suc n))) → Shape
assemble : Shape → Cd
assemble zero = hz
assemble (successor a) = hs (value a)
assemble (limit f st) = hl (λ n → value (f n))
view : Object → Shape
view (hz , l) = zero
view (hs a , l) = successor (a , l)
view (hl f , st , l) = limit (λ n → f n , l n) st
view (hΩ () f , l)
value-view : ∀ a → value a ≡ assemble (view a)
value-view (hz , l) = refl
value-view (hs a , l) = refl
value-view (hl f , l) = refl
value-view (hΩ () f , l)
both-values : ∀ a → (value a ≤ᵛ assemble (view a)) × (assemble (view a) ≤ᵛ value a)
both-values a rewrite value-view a = ≤-refl _ , ≤-refl _

rec : ∀ {A : Set} → A → (A → A) → ((ℕ → A) → A) → Object → A
rec z s l (hz , p) = z
rec z s l (hs a , p) = s (rec z s l (a , p))
rec z s l (hl f , st , p) = l (λ n → rec z s l (f n , p n))
rec z s l (hΩ () f , p)

closed : Object
closed = tree , legal-tree
internal-view : Shape
internal-view = view closed
```

这里的View是同类型合法对象的内部View，递归沿字面Cd子树，不是
fixed-world restrict。raw-lower是关于实际闭项的无条件值定理；完整
参照下界与上界仍应单独验收，不能据此命名ψ₀Λ。
