# 首个 Ω 坐标层的局部折叠接口

本轮先限定 k=ls lz，前缀 P=ΩL k。源是实际 `P⊕L upL k B`
的种类限制，坐标仍原始坐标；指标分量放回 P。目标仍是原始目标层，
不把回灌坐标限制成 Safe 子类型。此接口不声称总保合法。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedFoldIf where
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; _×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay

k : LH
k = ls lz
U : KS
U = Lv k
P : LH
P = ΩL k
G : HB U → LH
G B = P ⊕L upL k B
T : HB U → KS
T B = Lv (G B)

Pos : HB S⊥ → (B : HB U) → K (T B) → Set
Pos β hz κ = ⊤
Pos β (hs B) (inj₁ κ) = Pos β B κ
Pos β (hs B) (inj₂ _) = ⊤
Pos β (hl f) (n , κ) = Pos β (f n) κ
Pos β (hΩ (inj₁ ()) f) κ
Pos β (hΩ (inj₂ _) f) (inj₁ _ , κ) = ⊤
Pos β (hΩ (inj₂ _) f) (inj₂ e , κ) = (e ⊲[ tt ] β) × Pos β (f e) κ

Safe : HB S⊥ → HB U → KS
Safe β B = record
  { K = Σ (K (T B)) (Pos β B)
  ; E = λ x → E (T B) (proj₁ x)
  ; Wd = Wd (T B) ; LgW = LgW (T B)
  ; _≤w_ = _≤w_ (T B) ; ≤w-tr = ≤w-tr (T B)
  ; Bd = λ x → Bd (T B) (proj₁ x)
  ; Pr = λ x → Pr (T B) (proj₁ x)
  ; Bd↑ = λ {κ} → Bd↑ (T B) {κ = proj₁ κ}
  ; cmpK = λ {κ} → cmpK (T B) {κ = proj₁ κ}
  ; bot = λ x → bot (T B) (proj₁ x)
  ; botBd = λ x → botBd (T B) (proj₁ x) }

record Local (β : HB S⊥) (B : HB U) : Set₁ where
  field
    fold : ∀ t → t ⊲[ (tt , β) ] B → HB (Safe β B) → HB (T t)
```

所有目标与源坐标高度比较均须带字面公共界 B。后续分类器只在合法
β、B 下消费这些证据，不增加裸下标三歧。世界 ext 与输入合法条件
另列，未藏进 Local.fold 的全函数类型。
