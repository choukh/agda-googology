# 原生零目标的实际种类世界

目标Native0没有重复分量。给定它的世界v，将每个高秩界设为种子1，
所有底拷贝取v；分类器的每个base/rank都直接取得相应Bd/Pr等式。
这里不要求任意非零目标的不同副本相干，也不改变原运行器。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeZeroWorld where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge using (Native; Class; base; rank; raise; classify)

seed : ∀ c → Wd (Native hz) → Wd (Native c)
seed hz v = v
seed (hs c) v = seed c v , hs hz
seed (hl f) v = λ n → seed (f n) v

seed-legal : ∀ c {v} → LgW (Native hz) v → LgW (Native c) (seed c v)
seed-legal hz lv = lv
seed-legal (hs c) lv = seed-legal c lv , tt
seed-legal (hl f) lv = λ n → seed-legal (f n) lv

Law : ∀ {B A} → Wd (Native hz) → (A → Set) → (A → A → Set) → Class B A → Set₁
Law v bd pr (base κ to fr a b) =
  (∀ e → bd (to e) ≡ Bd (Native hz) κ e v) ×
  (∀ e d → pr (to e) (to d) ≡ Pr (Native hz) κ v e d)
Law v bd pr (rank i p to fr a b) =
  (∀ e → bd (to e) ≡ (e ⊲[ seed i v ] hs hz)) ×
  (∀ e d → pr (to e) (to d) ≡ (e ⊲[ seed i v ] d))

raise-law : ∀ {B C A} v bd pr (p : B ⊲ C) (cl : Class B A) →
  Law v bd pr cl → Law v bd pr (raise p cl)
raise-law v bd pr p (base κ to fr a b) l = l
raise-law v bd pr p (rank i q to fr a b) l = l

classified : ∀ c κ v →
  Law v (λ e → Bd (Native c) κ e (seed c v))
    (Pr (Native c) κ (seed c v)) (classify c κ)
classified hz κ v = (λ e → refl) , (λ e d → refl)
classified (hs c) (inj₁ κ) v =
  raise-law v _ _ (hsuc hself) (classify c κ) (classified c κ v)
classified (hs c) (inj₂ _) v = (λ e → refl) , (λ e d → refl)
classified (hl f) (n , κ) v =
  raise-law v _ _ (hlim n hself) (classify (f n) κ) (classified (f n) κ v)

-- 实际共同高度B只扩大rank路径；不改变上述世界律的内容。
component : ∀ {B} c κ v → (pc : c ⊲ B) →
  Law v (λ e → Bd (Native c) κ e (seed c v))
    (Pr (Native c) κ (seed c v)) (raise pc (classify c κ))
component c κ v pc = raise-law v _ _ pc (classify c κ) (classified c κ v)
```

这是对任意可数原生高度的实际输入世界与全部种类的定理，前提v合法
时源世界合法。尚未把决定的same/above递归输出证明合法；中间坐标
目标可能非零，不能从本篇推出完整Native.fold保合法。
