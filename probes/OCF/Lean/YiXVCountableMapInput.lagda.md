# YiXVCountableMapInput
> 验收文件。档位：编译定理。统一映射接口：回搬带守卫，孩子效果输出到同一目标，并给恒等闭实例。
> 推广 YiXVFiniteFamily/Level 的结构递归；共享映射证明供搬运与加法复用。未证明可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableMapInput where
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A

record Pull {κ ν i} (q : i L.<ᴵ κ) : Set where
  constructor pull
  field
    index : L.Ordᴵ
    bound : index L.<ᴵ ν
    same : i ≡ index
    raw : L.U index (L.<→◃ bound) → L.U i (L.<→◃ q)
    back : L.Ordᶜ index → L.Ordᶜ i
    input : ∀ X → raw (L.into (L.<→◃ bound) X) ≡ L.into (L.<→◃ q) (back X)
    good : ∀ {X} → A.Gd X → A.Gd (back X)
    mono : ∀ {X Y} → A.Le X Y → A.Le (back X) (back Y)
    floor : ∀ {X} → A.Le (L.Ω index) X → A.Le (L.Ω i) (back X)
    suc : ∀ X → back (L.suc X) ≡ L.suc (back X)
    transparent : ∀ {X} → A.Gd X → back X L.≅ X

record Child {κ ν i} (r : i L.◃₁ κ) (base : L.Ordᶜ ν) : Set where
  constructor child
  field
    map : L.Ordᶜ i → L.Ordᶜ ν
    good : ∀ {X} → A.Gd X → A.Gd (map X)
    mono : ∀ {X Y} → A.Le X Y → A.Le (map X) (map Y)
    right : ∀ {X} → A.Gd X → A.Le base (map X)

record View (κ ν : L.Ordᴵ) (φ : L.Ordᶜ κ → L.Ordᶜ ν) : Set where
  field
    zero : A.Gd (φ L.zero)
    suc : ∀ X → φ (L.suc X) ≡ L.suc (φ X)
    lim : ∀ f → φ (L.lim f) ≡ L.lim (λ n → φ (f n))
    node : ∀ {i} (q : i L.<ᴵ κ) → Pull {κ} {ν} q
    node-shape : ∀ {i} (q : i L.<ᴵ κ) f →
      φ (L.limᵢ q f) ≡ L.limᵢ (Pull.bound (node q)) (λ u → φ (f (Pull.raw (node q) u)))
    up : ∀ {i} (r : i L.◃₁ κ) → Child {κ} {ν} r (φ L.zero)
    up-shape : ∀ {i} (r : i L.◃₁ κ) X → φ (A.Up r X) ≡ Child.map (up r) X
    cong : ∀ {X Y} → X L.≅ Y → φ X L.≅ φ Y

identity : ∀ κ → View κ κ (λ X → X)
View.zero (identity κ) = A.Layer.gz
View.suc (identity κ) X = refl
View.lim (identity κ) f = refl
Pull.index (View.node (identity κ) {i} q) = i
Pull.bound (View.node (identity κ) q) = q
Pull.same (View.node (identity κ) q) = refl
Pull.raw (View.node (identity κ) q) u = u
Pull.back (View.node (identity κ) q) X = X
Pull.input (View.node (identity κ) q) X = refl
Pull.good (View.node (identity κ) q) gx = gx
Pull.mono (View.node (identity κ) q) t = t
Pull.floor (View.node (identity κ) q) t = t
Pull.suc (View.node (identity κ) q) X = refl
Pull.transparent (View.node (identity κ) q) gx = A.self gx
View.node-shape (identity κ) q f = refl
Child.map (View.up (identity κ) r) X = A.Up r X
Child.good (View.up (identity κ) r) gx = A.Basics.up κ r gx
Child.mono (View.up (identity κ) r) t = A.Basics.up-mono κ r t
Child.right (View.up (identity κ) r) gx = A.Basics.z≤ κ (A.Basics.up κ r gx)
View.up-shape (identity κ) r X = refl
View.cong (identity κ) e = e
```
