# YiXVReadSlots
> 验收文件。档位：编译定理。实际坐标换型的合法性与 PER、分支弱化和原源节点的模拟入口。
> 从 YiXVSourceAffine*、ReadFamily 与原 Level 推广，参照侧重用 CountableFold/Retain；未交完整世界 up/node 输出、外层 n≥2 界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadSlots where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
cast : ∀ {r s : S.Tr S.zero} → r ≡ s → L.Ordᶜ (T.lvl r) → L.Ordᶜ (T.lvl s)
cast e X = subst (λ r → L.Ordᶜ (T.lvl r)) e X
cast-good : ∀ {r s : S.Tr S.zero} (e : r ≡ s) {X} → A.Gd X → A.Gd (cast e X)
cast-good refl gx = gx
cast-self : ∀ {r s : S.Tr S.zero} (e : r ≡ s) {X} → A.Gd X → cast e X L.≅ X
cast-self refl gx = A.self gx
fam-weak : ∀ r p a {X Y} → U.Fam r p a X → A.Le X Y → U.Fam r p a Y
fam-weak r p a {X} {Y} h t = subst (λ Z → Z) (sym (B.stable r p a Y))
  (B.weak (J.slot r p) (subst (λ Z → Z) (B.stable r p a X) h) t)
node : ∀ r (p : S.Pos (J.ℓ r)) {g f} →
  (∀ a X Y → A.Gd X → A.Gd Y → A.Le (L.Ω (T.lvl (J.slot r p))) Y →
    U.Fam r p a X → A.Le (L.suc X) Y →
    U.UR r (g a) (f (L.into (L.<→◃ (J.q r p)) Y))) →
  U.UR r (S.Ω p g) (L.limᵢ (J.q r p) f)
node S.zero () h
node (S.suc r) p h = U.Layer.un p h
node (S.lim g d) p h = U.Layer.un p h
node (S.Ω () g) p h
node (S.up r () y ny) p h
```
