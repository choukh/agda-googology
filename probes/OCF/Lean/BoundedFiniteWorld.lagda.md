# 实际 Ω 高度的任意有限分量世界可扩张

全自然数混合的每个分量具有字面有限编号。识别这个有限构造形状
不需要任意可数树判等。这里只替换一个指定有限槽，证明该槽投影
精确相等；不判定两棵任意树的值、第一位置或相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedFiniteWorld where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.LHRecLeg using (w₀L; lw₀L)
open import OCF.Lean.BoundedFoldIf
open import OCF.Lean.BoundedContextClosed using (num)

replace : (F : Cd → Set) → (∀ e → F e) → ∀ n → F (num n) → ∀ e → F e
replace F d zero a hz = a
replace F d zero a (hs e) = d (hs e)
replace F d zero a (hl f) = d (hl f)
replace F d (suc n) a hz = d hz
replace F d (suc n) a (hs e) = replace (λ x → F (hs x)) (λ x → d (hs x)) n a e
replace F d (suc n) a (hl f) = d (hl f)

at : ∀ F d n a → replace F d n a (num n) ≡ a
at F d zero a = refl
at F d (suc n) a = at (λ x → F (hs x)) (λ x → d (hs x)) n a

preserves : ∀ F (Q : ∀ e → F e → Set) d → (∀ e → Q e (d e)) →
  ∀ n a → Q (num n) a → ∀ e → Q e (replace F d n a e)
preserves F Q d ld zero a la hz = la
preserves F Q d ld zero a la (hs e) = ld (hs e)
preserves F Q d ld zero a la (hl f) = ld (hl f)
preserves F Q d ld (suc n) a la hz = ld hz
preserves F Q d ld (suc n) a la (hs e) =
  preserves (λ x → F (hs x)) (λ x → Q (hs x)) (λ x → d (hs x))
    (λ x → ld (hs x)) n a la e
preserves F Q d ld (suc n) a la (hl f) = ld (hl f)

B : HB U
B = hΩ (inj₂ tt) up
module Whole (n : ℕ) (W : Wd (T (up (num n)))) where
  F : Cd → Set
  F e = Wd (T (up e))
  defaults : ∀ e → F e
  defaults e = w₀L (G (up e))

  world : Wd (T B)
  world (inj₁ _) = tt , hz
  world (inj₂ e) = replace F defaults n W e

  exact : world (inj₂ (num n)) ≡ W
  exact = at F defaults n W

  legal : LgW (T (up (num n))) W → LgW (T B) world
  legal l (inj₁ _) = tt , tt
  legal l (inj₂ e) = preserves F (λ e → LgW (T (up e))) defaults
    (λ e → lw₀L (G (up e))) n W l e

  admitted : ∀ κ {c} → Bd (T (up (num n))) κ c W →
    Bd (T B) (inj₂ (num n) , κ) c world
  admitted κ {c} b = subst (λ V → Bd (T (up (num n))) κ c V) (sym exact) b
```

Whole 不预设分量世界为零，接受任意合法的 W；所以某个有限分量中
反馈坐标已有可入世界时，完整原始 Ω 源世界也能实现它。Safe 的世界
与这里相同，若种类已有 Pos 就可直接使用；Pos 仍需其共同 β 证据。
这尚不提供分量内部任意种类的坐标世界，也不覆盖非有限编号的任意槽。
没有扩展下标三歧、没有一般保旧信息更新律，未改变树或折叠。
