# 极限分量升层与结构搬运：单侧关系交换

与后继版本相同，逐构造保持原Rq；self分量无需按值严格。
在marker头部只消去构造子，不对函数分支断言字面相等。

```agda
{-# OPTIONS --safe --without-K #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueTransportMarker (𝕊 : HtB) where
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Free.Level
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊

erase-tr-marker : ∀ {m a b c k φ χ} (e : a ≅ᴵ b)
  (r : k ◃₁ a) (z : Us m k (◃₁→◃ r) φ χ) (x : Q m a φ χ) (s : b ◃ c) →
  ι s (trQ e (omk r z x)) ≡ ι s (trQ e x)
erase-tr-marker (s≅ e) zero z x s = refl
erase-tr-marker (l≅ f) (self n) z x s = refl

```
