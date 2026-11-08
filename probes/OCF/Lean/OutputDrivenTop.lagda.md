# 读取实际底世界和塔世界的界

不再为更新后的世界固定选零。沿原 Sb/Tw 结构读出每一种类在当前
世界里的界；新种类直接取该世界的第二分量。没有查找或判定组件下标。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.OutputDrivenTop where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (Sb)

topS : ∀ n (w : Wd (Sb n)) κ → E (Sb n) κ
topT : ∀ n m (w : Wd (Tw (Sb n) m)) κ → E (Tw (Sb n) m) κ
topS zero w ()
topS (suc n) w (inj₁ _ , inj₂ _) = proj₂ (w (inj₁ tt))
topS (suc n) w (inj₁ _ , inj₁ κ) = topS n (proj₁ (w (inj₁ tt))) κ
topS (suc n) w (inj₂ c , κ) = topT n (hs c) (w (inj₂ c)) κ
topT n hz w κ = topS n w κ
topT n (hs m) w (inj₂ _) = proj₂ w
topT n (hs m) w (inj₁ κ) = topT n m (proj₁ w) κ
topT n (hl f) w (i , κ) = topT n (f i) (w i) κ
topT n (hΩ κ₀ g) w (e , κ) = topT n (g e) (w e) κ

topS-bd : ∀ n w κ → Bd (Sb n) κ (topS n w κ) w
topT-bd : ∀ n m w κ → Bd (Tw (Sb n) m) κ (topT n m w κ) w
topS-bd zero w ()
topS-bd (suc n) w (inj₁ _ , inj₂ _) = hself
topS-bd (suc n) w (inj₁ _ , inj₁ κ) = topS-bd n (proj₁ (w (inj₁ tt))) κ
topS-bd (suc n) w (inj₂ c , κ) = topT-bd n (hs c) (w (inj₂ c)) κ
topT-bd n hz w κ = topS-bd n w κ
topT-bd n (hs m) w (inj₂ _) = hself
topT-bd n (hs m) w (inj₁ κ) = topT-bd n m (proj₁ w) κ
topT-bd n (hl f) w (i , κ) = topT-bd n (f i) (w i) κ
topT-bd n (hΩ κ₀ g) w (e , κ) = topT-bd n (g e) (w e) κ

-- 新种类实际读取更新后的界，不是总取 bot。
reads-bound : ∀ n m w b → topT n (hs m) (w , b) (inj₂ tt) ≡ b
reads-bound n m w b = refl
```

本篇只有世界操作，不改折叠。读取世界界并不保证没有其他值损失，
但使后续闭项真实消费更新后的槽值；可入证书不要求新增裸下标比较。
