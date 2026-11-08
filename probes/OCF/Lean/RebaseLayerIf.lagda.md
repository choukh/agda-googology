# 只在有证坐标上采样的分层验收关系

原TreeValue的统一右规则量化全部raw坐标；仅限制Ω配对还不足以
证明高层传递，因为vor/vo需要右端每个坐标可被配对。本篇明确同时
限制统一右规则。它是新的验收关系，不替换树、运行器或合法性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseLayerIf where
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Align.BoundedDescentValueBridge using (Native)

data SampleValue (S : KS) (A : ∀ κ → E S κ → Set)
  (Q : ∀ κ → E S κ → E S κ → Set) : HB S → HB S → Set where
  vz : ∀ {b} → SampleValue S A Q hz b
  vs : ∀ {a b} → SampleValue S A Q a b → SampleValue S A Q (hs a) (hs b)
  vr : ∀ {a b} → SampleValue S A Q a b → SampleValue S A Q a (hs b)
  vl : ∀ {f b} → (∀ n → SampleValue S A Q (f n) b) → SampleValue S A Q (hl f) b
  vli : ∀ {a f} n → SampleValue S A Q a (f n) → SampleValue S A Q a (hl f)
  vo : ∀ {κ f g} → (∀ x y → Q κ x y → SampleValue S A Q (f x) (g y)) →
    SampleValue S A Q (hΩ κ f) (hΩ κ g)
  vor : ∀ {a κ g} → (∀ e → A κ e → SampleValue S A Q a (g e)) →
    SampleValue S A Q a (hΩ κ g)

Value : ∀ c → HB (Native c) → HB (Native c) → Set
Admit : ∀ c κ → E (Native c) κ → Set
Coord : ∀ c κ → E (Native c) κ → E (Native c) κ → Set
Value c = SampleValue (Native c) (Admit c) (Coord c)
Admit hz (inj₁ ())
Admit hz (inj₂ _) e = ⊤
Admit (hs c) (inj₁ κ) e = Admit c κ e
Admit (hs c) (inj₂ _) e = Value c e e
Admit (hl f) (n , κ) e = Admit (f n) κ e
Coord hz (inj₁ ())
Coord hz (inj₂ _) x y = x ≤ᵛ y
Coord (hs c) (inj₁ κ) x y = Coord c κ x y
Coord (hs c) (inj₂ _) x y = Value c x y × (Value c x x × Value c y y)
Coord (hl f) (n , κ) x y = Coord (f n) κ x y
```

比较只在固定Native层的值上进行，没有层号判等或槽选择。连接实际
fold仍须为每个实际采样坐标给Admit；不能把本关系当原Value的别名。
