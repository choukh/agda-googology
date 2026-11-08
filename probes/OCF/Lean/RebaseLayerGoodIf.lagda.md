# 按层递归的实际采样域

本篇不改已冻SampleValue或仅self的Native接口。新域把最高坐标的
准入要求改为低层Good；Good同时保存自证与直接子树的递归证书。
这样原floor的up分支接收到的坐标确有可递归证书。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseLayerGoodIf where
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Lean.RebaseLayerIf using (SampleValue)

Value : ∀ c → HB (Native c) → HB (Native c) → Set
Admit : ∀ c κ → E (Native c) κ → Set
Coord : ∀ c κ → E (Native c) κ → E (Native c) κ → Set
Good : ∀ c → HB (Native c) → Set
Value c = SampleValue (Native c) (Admit c) (Coord c)
Admit hz (inj₁ ())
Admit hz (inj₂ _) e = ⊤
Admit (hs c) (inj₁ κ) e = Admit c κ e
Admit (hs c) (inj₂ _) e = Good c e
Admit (hl f) (n , κ) e = Admit (f n) κ e
Coord hz (inj₁ ())
Coord hz (inj₂ _) x y = x ≤ᵛ y
Coord (hs c) (inj₁ κ) x y = Coord c κ x y
Coord (hs c) (inj₂ _) x y = Value c x y × (Good c x × Good c y)
Coord (hl f) (n , κ) x y = Coord (f n) κ x y
Good c hz = Value c hz hz
Good c (hs a) = Value c (hs a) (hs a) × Good c a
Good c (hl f) = Value c (hl f) (hl f) × (∀ n → Good c (f n))
Good c (hΩ κ g) = Value c (hΩ κ g) (hΩ κ g) × (∀ e → Admit c κ e → Good c (g e))
```

域没有标签、没有判等，也不要求所有raw坐标Good。值关系只用于
验收；Good的非空实例与原生成算子闭包在下一篇给出。
