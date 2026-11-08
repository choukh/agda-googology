# 局部折叠的输入世界重设

沿高度树递归，把应保留的前缀和指标拷贝统一从目标世界投影；新增
后继层的折叠界仍来自源世界。这里不要求任意独立源世界相干。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedFoldWorld where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.LHRecLeg using (pw; lgpw)
open import OCF.Lean.BoundedContextRun using (node-context)
open import OCF.Lean.BoundedIndexContext using (omega-context)

assemble : ∀ P k κ (h : E (Lv k) κ → LH) →
  Wd (step (Lv (lvl k κ))) → (∀ e → Wd (Lv (P ⊕L h e))) → Wd (Lv (P ⊕L node k κ h))
assemble P lz () h u v
assemble P (ls k) (inj₁ κ) h u v = assemble P k κ h u v
assemble P (ls k) (inj₂ _) h u v (inj₁ _) = u
assemble P (ls k) (inj₂ _) h u v (inj₂ e) = v e
assemble P (ll f) (n , κ) h u v = assemble P (f n) κ h u v
assemble P (lΩ k g) (inj₁ _ , inj₁ κ) h u v = assemble P k κ h u v
assemble P (lΩ k g) (inj₁ _ , inj₂ _) h u v (inj₁ _) = u
assemble P (lΩ k g) (inj₁ _ , inj₂ _) h u v (inj₂ e) = v e
assemble P (lΩ k g) (inj₂ c , κ) h u v = assemble P (g c) κ h u v

assemble-legal : ∀ P k κ h u v → LgW (step (Lv (lvl k κ))) u → (∀ e → LgW (Lv (P ⊕L h e)) (v e)) →
  LgW (Lv (P ⊕L node k κ h)) (assemble P k κ h u v)
assemble-legal P lz () h u v lu l
assemble-legal P (ls k) (inj₁ κ) h u v lu l = assemble-legal P k κ h u v lu l
assemble-legal P (ls k) (inj₂ _) h u v lu l (inj₁ _) = lu
assemble-legal P (ls k) (inj₂ _) h u v lu l (inj₂ e) = l e
assemble-legal P (ll f) (n , κ) h u v lu l = assemble-legal P (f n) κ h u v lu l
assemble-legal P (lΩ k g) (inj₁ _ , inj₁ κ) h u v lu l = assemble-legal P k κ h u v lu l
assemble-legal P (lΩ k g) (inj₁ _ , inj₂ _) h u v lu l (inj₁ _) = lu
assemble-legal P (lΩ k g) (inj₁ _ , inj₂ _) h u v lu l (inj₂ e) = l e
assemble-legal P (lΩ k g) (inj₂ c , κ) h u v lu l = assemble-legal P (g c) κ h u v lu l

assemble-project : ∀ P k κ h u v e →
  pw (node-context P k κ h e) (assemble P k κ h u v) ≡ v e
assemble-project P lz () h u v e
assemble-project P (ls k) (inj₁ κ) h u v e = assemble-project P k κ h u v e
assemble-project P (ls k) (inj₂ _) h u v e = refl
assemble-project P (ll f) (n , κ) h u v e = assemble-project P (f n) κ h u v e
assemble-project P (lΩ k g) (inj₁ _ , inj₁ κ) h u v e = assemble-project P k κ h u v e
assemble-project P (lΩ k g) (inj₁ _ , inj₂ _) h u v e = refl
assemble-project P (lΩ k g) (inj₂ c , κ) h u v e = assemble-project P (g c) κ h u v e

module Relative (k : LH) where
  P = ΩL k
  T : HB (Lv k) → KS
  T B = Lv (P ⊕L upL k B)

  ext : ∀ B → Wd (Lv P) → Wd (T B) → Wd (T B)
  ext hz v W = v
  ext (hs B) v W = ext B v (proj₁ W) , proj₂ W
  ext (hl f) v W = λ n → ext (f n) v (W n)
  ext (hΩ κ h) v W = assemble P k κ (λ e → upL k (h e))
    (pw (omega-context k κ) v)
    (λ e → ext (h e) v (pw (node-context P k κ (λ e → upL k (h e)) e) W))

  legal-ext : ∀ B {v W} → LgW (Lv P) v → LgW (T B) W → LgW (T B) (ext B v W)
  legal-ext hz lv lW = lv
  legal-ext (hs B) lv lW = legal-ext B lv (proj₁ lW) , proj₂ lW
  legal-ext (hl f) lv lW = λ n → legal-ext (f n) lv (lW n)
  legal-ext (hΩ κ h) lv lW = assemble-legal P k κ (λ e → upL k (h e)) _ _
    (lgpw (omega-context k κ) lv)
    (λ e → legal-ext (h e) lv (lgpw (node-context P k κ (λ e → upL k (h e)) e) lW))
```

assemble 是已有累加扩界节点组装的推广：指标世界从参数给出，而非
固定为零。ext 保合法并不说明保持原世界或原折叠值；它供输入单调性
定理使用，未给完整分类器、折叠或强度结论。
