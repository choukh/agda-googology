# 全有限原下降的分层有向关系接口

低层坐标关系递归进入高层Ω配对；Ω右规则必须对全部raw分支给出
统一下界。不从有向关系推出右侧raw树自相关，不使用任取Ω坐标的消去。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionUniformIf where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunIf using (at)

data TreeValue (S : KS) (Q : ∀ κ → E S κ → E S κ → Set) :
  HB S → HB S → Set where
  vz : ∀ {b} → TreeValue S Q hz b
  vs : ∀ {a b} → TreeValue S Q a b → TreeValue S Q (hs a) (hs b)
  vr : ∀ {a b} → TreeValue S Q a b → TreeValue S Q a (hs b)
  vl : ∀ {f b} → (∀ n → TreeValue S Q (f n) b) → TreeValue S Q (hl f) b
  vli : ∀ {a f} n → TreeValue S Q a (f n) → TreeValue S Q a (hl f)
  vo : ∀ {κ f g} → (∀ x y → Q κ x y → TreeValue S Q (f x) (g y)) →
    TreeValue S Q (hΩ κ f) (hΩ κ g)
  vor : ∀ {a κ g} → (∀ c → TreeValue S Q a (g c)) → TreeValue S Q a (hΩ κ g)

Value : ∀ c → HB (Native c) → HB (Native c) → Set
CoordValue : ∀ c κ → E (Native c) κ → E (Native c) κ → Set
Value c = TreeValue (Native c) (CoordValue c)
CoordValue hz (inj₁ ())
CoordValue hz (inj₂ _) = _≤ᵛ_
CoordValue (hs c) (inj₁ κ) = CoordValue c κ
CoordValue (hs c) (inj₂ _) = Value c
CoordValue (hl f) (n , κ) = CoordValue (f n) κ

record NativeComparison : Set₁ where
  field
    compare : ∀ n m {B B′} (lB : LgB B) (lB′ : LgB B′)
      (pc : num n ⊲ B) (pc′ : num n ⊲ B′)
      (pt : num m ⊲ B) (pt′ : num m ⊲ B′)
      {a b} → Value (num n) a b →
      Value (num m) (at n m lB pc pt a) (at n m lB′ pc′ pt′ b)
```

compare是待实例化的原函数比较，未预设Old世界与固定seed1相容。
所有层比较分别带字面公共界B/B′；坐标结构关系不给三歧或判等操作。
