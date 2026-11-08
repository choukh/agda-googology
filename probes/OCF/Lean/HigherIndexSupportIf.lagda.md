# 分层坐标准入与相对支持

Support按原层叠高度c与树a递归；新kind的坐标证书降到c的直接子层。
rank准入携带将来的合法低界及相对Support，不以raw合法性代替支持。
底层prefix的组件编号仍必须在字面β内；底指标与内层Ω指标都更新β。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexSupportIf where
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.HigherIndexClassIf using (U; Native)

Support : ∀ c → Cd → HB (Native c) → Set
Event : ∀ c → Cd → K (Native c) → Set
Coord : ∀ c κ → Cd → E (Native c) κ → Set
next : ∀ c κ β e → Coord c κ β e → Cd

Support c β hz = ⊤
Support c β (hs a) = Support c β a
Support c β (hl f) = ∀ n → Support c β (f n)
Support c β (hΩ κ f) = Event c β κ ×
  (∀ e → (ad : Coord c κ β e) → Support c (next c κ β e ad) (f e))

Event hz β (inj₁ _ , inj₁ ())
Event hz β (inj₁ _ , inj₂ _) = ⊤
Event hz β (inj₂ d , κ) = d ⊲ β
Event (hs c) β (inj₁ κ) = Event c β κ
Event (hs c) β (inj₂ _) = ⊤
Event (hl f) β (n , κ) = Event (f n) β κ
Event (hΩ (inj₁ ()) f) β κ
Event (hΩ (inj₂ _) f) β (inj₁ _ , inj₁ ())
Event (hΩ (inj₂ _) f) β (inj₁ _ , inj₂ _) = ⊤
Event (hΩ (inj₂ _) f) β (inj₂ d , κ) = d ⊲ β × Event (f d) β κ

Coord hz (inj₁ _ , inj₁ ()) β e
Coord hz (inj₁ _ , inj₂ _) β e = β ⊲ e × LgB e
Coord hz (inj₂ d , κ) β e = ⊤
Coord (hs c) (inj₁ κ) β e = Coord c κ β e
Coord (hs c) (inj₂ _) β e = Σ Cd (λ β′ → β ⊲ β′ × LgB β′ × Support c β′ e)
Coord (hl f) (n , κ) β e = Coord (f n) κ β e
Coord (hΩ (inj₁ ()) f) κ β e
Coord (hΩ (inj₂ _) f) (inj₁ _ , inj₁ ()) β e
Coord (hΩ (inj₂ _) f) (inj₁ _ , inj₂ _) β e = β ⊲ e × LgB e
Coord (hΩ (inj₂ _) f) (inj₂ d , κ) β e = Coord (f d) κ β e

next hz (inj₁ _ , inj₁ ()) β e ad
next hz (inj₁ _ , inj₂ _) β e ad = hs e
next hz (inj₂ d , κ) β e ad = β
next (hs c) (inj₁ κ) β e ad = next c κ β e ad
next (hs c) (inj₂ _) β e ad = proj₁ ad
next (hl f) (n , κ) β e ad = next (f n) κ β e ad
next (hΩ (inj₁ ()) f) κ β e ad
next (hΩ (inj₂ _) f) (inj₁ _ , inj₁ ()) β e ad
next (hΩ (inj₂ _) f) (inj₁ _ , inj₂ _) β e ad = hs e
next (hΩ (inj₂ _) f) (inj₂ d , κ) β e ad = next (f d) κ β e ad
```

这不是fold的总函数定义：输出原raw HB时，keep分支还需处理任意raw
目标坐标。源Support只给Coord域上的分支证书，故不能仅凭此接口宣称
已有总运行器或全floor可折叠。后续分别验收支持闭包、实际地板及运行器。
