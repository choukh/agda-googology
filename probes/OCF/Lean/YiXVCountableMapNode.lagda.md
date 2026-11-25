# YiXVCountableMapNode
> 验收文件。档位：编译定理。统一映射接口把原节点的合法性证书送到目标节点。
> 推广 YiXVFiniteFamily/Level 的结构递归；共享映射证明供搬运与加法复用。未证明可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableMapNode where
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst; subst₂)
open import Data.Product using (proj₁)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as Omega
import OCF.Lean.YiXVCountableMapInput as V

module Node {κ ν} (φ : L.Ordᶜ κ → L.Ordᶜ ν) (view : V.View κ ν φ)
  {i} (q : i L.<ᴵ κ) (f : L.U i (L.<→◃ q) → L.Ordᶜ κ)
  (ex : L.limᵢ q f L.≅ L.limᵢ q f)
  (gb : ∀ X → A.Layer.GU κ A.Gd< A.Le< q X → A.Layer.Floor κ A.Gd< A.Le< q X → A.Gd (φ (f (L.into (L.<→◃ q) X))))
  (mo : ∀ X Y → A.Layer.GU κ A.Gd< A.Le< q X → A.Layer.GU κ A.Gd< A.Le< q Y →
    A.Layer.Floor κ A.Gd< A.Le< q X → A.Layer.RU κ A.Gd< A.Le< q X Y →
    A.Le (φ (f (L.into (L.<→◃ q) X))) (φ (f (L.into (L.<→◃ q) Y))))
  (db : ∀ X → A.Layer.GU κ A.Gd< A.Le< q X → A.Layer.Floor κ A.Gd< A.Le< q X →
    A.Le (φ (L.suc (f (L.into (L.<→◃ q) X)))) (φ (f (L.into (L.<→◃ q) (L.suc X)))))
  (po : A.Le (φ (L.suc L.zero)) (φ (f (L.into (L.<→◃ q) (L.Ω i))))) where
  module D = A.Layer ν A.Gd< A.Le<
  module S = A.Layer κ A.Gd< A.Le<
  p = V.View.node view q
  j = V.Pull.index p
  r = V.Pull.bound p
  raw : L.U j (L.<→◃ r) → L.Ordᶜ ν
  raw u = φ (f (V.Pull.raw p u))
  body : L.Ordᶜ j → L.Ordᶜ ν
  body X = φ (f (L.into (L.<→◃ q) (V.Pull.back p X)))
  at : ∀ X → raw (L.into (L.<→◃ r) X) Relation.Binary.PropositionalEquality.≡ body X
  at X = cong (λ u → φ (f u)) (V.Pull.input p X)
  good : ∀ X → D.GU r X → S.GU q (V.Pull.back p X)
  good X gx = A.good-in (L.<→◃ q) (V.Pull.good p (A.good-out (L.<→◃ r) gx))
  floor : ∀ X → D.Floor r X → S.Floor q (V.Pull.back p X)
  floor X o = A.le-in (L.<→◃ q) (V.Pull.floor p (A.le-out (L.<→◃ r) o))
  rel : ∀ X Y → D.RU r X Y → S.RU q (V.Pull.back p X) (V.Pull.back p Y)
  rel X Y t = A.le-in (L.<→◃ q) (V.Pull.mono p (A.le-out (L.<→◃ r) t))
  body-good : ∀ X → D.GU r X → D.Floor r X → D.Gd (raw (L.into (L.<→◃ r) X))
  body-good X gx o = subst D.Gd (sym (at X)) (gb (V.Pull.back p X) (good X gx) (floor X o))
  law : D.SC r raw
  D.SC.mo law X Y gx gy o t = subst₂ (A.Le {κ = ν}) (sym (at X)) (sym (at Y))
    (mo (V.Pull.back p X) (V.Pull.back p Y) (good X gx) (good Y gy) (floor X o) (rel X Y t))
  D.SC.db law X gx o = subst₂ (A.Le {κ = ν}) (sym (cong L.suc (at X))) (sym (at (L.suc X)))
    (subst₂ (A.Le {κ = ν}) (V.View.suc view (f (L.into (L.<→◃ q) (V.Pull.back p X))))
      (sym (cong (λ Y → φ (f (L.into (L.<→◃ q) Y))) (V.Pull.suc p X)))
      (db (V.Pull.back p X) (good X gx) (floor X o)))
  D.SC.po law = subst (A.Le D.one) (sym (at (L.Ω j))) (D.trans
    (D.trans
      (subst (D.Le D.one) (sym (V.View.suc view L.zero))
        (A.Basics.s≤ ν (A.Basics.z≤ ν (V.View.zero view)))) po)
    (mo (L.Ω i) (V.Pull.back p (L.Ω j)) (A.good-in (L.<→◃ q) (proj₁ (Omega.model i)))
      (good (L.Ω j) (A.good-in (L.<→◃ r) (proj₁ (Omega.model j))))
      (A.le-in (L.<→◃ q) (A.Layer.rfl i A.Gd< A.Le< (proj₁ (Omega.model i))))
      (floor (L.Ω j) (A.le-in (L.<→◃ r) (A.Layer.rfl j A.Gd< A.Le< (proj₁ (Omega.model j)))))))
  result : A.Gd (φ (L.limᵢ q f))
  result = subst D.Gd (sym (V.View.node-shape view q f))
    (D.gn (subst₂ L._≅_ (V.View.node-shape view q f) (V.View.node-shape view q f) (V.View.cong view ex)) law body-good)

module Model where
  module D = A.Layer (L.suc L.zero) A.Gd< A.Le<
  law : D.SC L.zero (L.up L.zero)
  law = D.sc (λ X Y gx gy o t → A.Basics.up-mono (L.suc L.zero) L.zero t)
    (λ X gx o → A.Basics.up-suc (L.suc L.zero) L.zero gx)
    (A.Basics.one-up (L.suc L.zero) L.zero A.ground-pos)
  module Run = Node (λ X → X) (V.identity (L.suc L.zero)) L.zero (L.up L.zero)
    (L.Ω-≅ (L.s≅ L.z≅)) (λ X gx o → A.Basics.up (L.suc L.zero) L.zero gx)
    (D.SC.mo law) (D.SC.db law) (D.SC.po law)
  actual : A.Gd (L.Ω (L.suc L.zero))
  actual = Run.result
```
