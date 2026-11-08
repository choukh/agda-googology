# 原生固定分量输入世界视图接口

以原decide为准，每个c与t带同一合法B下的位置。不先假定base-kind
与along选择的目标拷贝相容；接口是否普遍可实现由构造/反例共同检验。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeViewIf where
open import Data.Unit using (tt)
open import Data.Product using (Σ; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldRun using (Decision; keep; same; above; decide)

module Laws {B c t : Cd} (W : Wd (Native t)) (V : Wd (Native c)) (κ : K (Native c)) where
  For : Decision B t (E (Native c) κ) → Set
  For (keep j fr) =
    (∀ e → Bd (Native t) j e W → Bd (Native c) κ (fr e) V) ×
    (∀ e d → Bd (Native t) j e W → Bd (Native t) j d W →
      Pr (Native t) j W e d → Pr (Native c) κ V (fr e) (fr d)) ×
    (∀ a → Bd (Native c) κ a V →
      Σ (E (Native t) j) (λ e → (fr e ≡ a) × Bd (Native t) j e W))
  For (same to) =
    Bd (Native c) κ (to (hs hz)) V ×
    (∀ a → Bd (Native c) κ a V → Pr (Native c) κ V a (to (hs hz)))
  For (above i pi ti to) =
    Bd (Native c) κ (to (hs hz)) V ×
    (∀ a → Bd (Native c) κ a V → Pr (Native c) κ V a (to (hs hz)))

record View {B : Cd} (lB : LgB B) (c : Cd) (pc : c ⊲ B)
  (t : Cd) (pt : t ⊲ B) (W : Wd (Native t)) : Set where
  field
    input-world : Wd (Native c)
    legal-world : LgW (Native t) W → LgW (Native c) input-world
    node-laws : ∀ κ → Laws.For W input-world κ (decide pt lB (raise pc (classify c κ)))
```

keep的Pr律明确要求两坐标同在当前目标world的同一种类界下。
co的比较以实际seed1为字面界；源其他可入坐标必须位于它的第一位置。
本记录只刻画实际所需律，没有给全Source不可判定Cd分量单槽更新。
