# 全种类坐标准入编码的实际实例

每个回调输出先leg。rank坐标含原本层地板与输出的纯树嵌入，低指标
扩β；前缀内部组件的坐标按实际LH层编码。没有全raw支持补证字段。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexConsumeCode where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (lvl; ΩL; _⊕L_; upL)
open import OCF.Lean.HigherIndexClassIf using (U; Native)
open import OCF.Lean.HigherIndexSupportIf
import OCF.Lean.HigherIndexSupportClosure as S
open import OCF.Lean.HigherIndexSupportFloor using (floor; floor-support)
open import OCF.Lean.HigherIndexConsumeIf

pure : ∀ S → Cd → HB S
pure S hz = hz
pure S (hs a) = hs (pure S a)
pure S (hl f) = hl (λ n → pure S (f n))
pure S (hΩ () f)
pure-support : ∀ c β d → Support c β (pure (Native c) d)
pure-support c β hz = tt
pure-support c β (hs d) = pure-support c β d
pure-support c β (hl f) = λ n → pure-support c β (f n)
pure-support c β (hΩ () f)

from : ∀ x κ → HB (Lv (lvl x κ)) → E (Lv x) κ
from lz () a
from (ls x) (inj₁ κ) a = from x κ a
from (ls x) (inj₂ _) a = a
from (ll f) (n , κ) a = from (f n) κ a
from (lΩ k g) (inj₁ _ , inj₁ κ) a = from k κ a
from (lΩ k g) (inj₁ _ , inj₂ _) a = a
from (lΩ k g) (inj₂ d , κ) a = from (g d) κ a

code : ∀ c κ β → LgB β → Cd → Σ (E (Native c) κ) (Coord c κ β)
code hz (inj₁ _ , inj₁ ()) β lb d
code hz (inj₁ _ , inj₂ _) β lb d = β ⊞ leg d , ⊞-fst β (leg d) , Lg-⊞ β (leg d) lb (Lg-leg d)
code hz (inj₂ a , κ) β lb d = from x κ (pure (Lv (lvl x κ)) (leg d)) , tt
  where x = ΩL lz ⊕L upL lz a
code (hs c) (inj₁ κ) β lb d = code c κ β lb d
code (hs c) (inj₂ _) β lb d = floor c ⊞ pure (Native c) (leg d) , β , hself , lb ,
  S.add c β _ _ (floor-support c β) (pure-support c β (leg d))
code (hl f) (n , κ) β lb d = code (f n) κ β lb d
code (hΩ (inj₁ ()) f) κ β lb d
code (hΩ (inj₂ _) f) (inj₁ _ , inj₁ ()) β lb d
code (hΩ (inj₂ _) f) (inj₁ _ , inj₂ _) β lb d = β ⊞ leg d , ⊞-fst β (leg d) , Lg-⊞ β (leg d) lb (Lg-leg d)
code (hΩ (inj₂ _) f) (inj₂ a , κ) β lb d = code (f a) κ β lb d

legal-next : ∀ c κ β → LgB β → ∀ e (ad : Coord c κ β e) → LgB (next c κ β e ad)
legal-next hz (inj₁ _ , inj₁ ()) β lb e ad
legal-next hz (inj₁ _ , inj₂ _) β lb e ad = proj₂ ad
legal-next hz (inj₂ a , κ) β lb e ad = lb
legal-next (hs c) (inj₁ κ) β lb e ad = legal-next c κ β lb e ad
legal-next (hs c) (inj₂ _) β lb e ad = proj₁ (proj₂ (proj₂ ad))
legal-next (hl f) (n , κ) β lb e ad = legal-next (f n) κ β lb e ad
legal-next (hΩ (inj₁ ()) f) κ β lb e ad
legal-next (hΩ (inj₂ _) f) (inj₁ _ , inj₁ ()) β lb e ad
legal-next (hΩ (inj₂ _) f) (inj₁ _ , inj₂ _) β lb e ad = proj₂ ad
legal-next (hΩ (inj₂ _) f) (inj₂ a , κ) β lb e ad = legal-next (f a) κ β lb e ad

instance-coding : CoordinateCoding
instance-coding = record { code = code ; legal-next = legal-next }
```
