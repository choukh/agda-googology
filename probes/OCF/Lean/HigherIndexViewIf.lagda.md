# 固定合法公共世界内的内部树View

这是新的实验值域，不宣称保留原raw树的全部值。Ω坐标携带在同一
原合法世界w内的可入证据；因此比较直接消费公共界，不要求裸三歧。
对象仍携带原树及合法证书，值定义为本实验布劳威尔树。View的部分
仍为同一Object，并可沿原树结构递归。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexViewIf where
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase

Bounded : (S : KS) → (w : Wd S) → LgW S w → KS
Bounded S w lw = record
  { K = K S
  ; E = λ κ → Σ (E S κ) (λ e → Bd S κ e w)
  ; Wd = ⊤ ; LgW = λ _ → ⊤ ; _≤w_ = λ _ _ → ⊤
  ; ≤w-tr = λ _ _ → tt
  ; Bd = λ _ _ _ → ⊤
  ; Pr = λ κ _ e d → Pr S κ w (proj₁ e) (proj₁ d)
  ; Bd↑ = λ _ _ → tt
  ; cmpK = λ { {c = e} {c′ = d} _ _ _ → cmpK S (proj₂ e) (proj₂ d) lw }
  ; bot = λ κ → bot S κ , botBd S κ w
  ; botBd = λ _ _ → tt }

module Domain (S : KS) (w : Wd S) (lw : LgW S w) where
  Target = Bounded S w lw
  Object : Set
  Object = Σ (HB S) LgB
  value : Object → HB Target
  restrict : HB S → HB Target
  restrict hz = hz
  restrict (hs a) = hs (restrict a)
  restrict (hl f) = hl (λ n → restrict (f n))
  restrict (hΩ κ g) = hΩ κ (λ e → restrict (g (proj₁ e)))
  value x = restrict (proj₁ x)
```

Bounded的Bd虽为真，E已含原共同世界的Bd；不是把无界坐标全部当可入。
后续证明实际对象的合法View及一个真实含Ω组件实例。此处不把restrict
当原值保持，也不声称已给全动态支持折叠。
