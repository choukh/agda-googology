# 原完整高层地板的分层支持证书

在原Source树上消费各组件的Coord；不复制源树或要求所有raw坐标准入。
最高指标仍取原J₁的AdmK。全地板以及θ的支持直接按原树结构构造。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexSupportSource where
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lΩ)
open import OCF.Lean.LHRecFl using (flL; Lg-flL; cxI; gcF)
open import OCF.Lean.LHRecLeg using (AdmK; J₁; module New)
open import OCF.Lean.LHRecIf using (LHRecIf)
open import OCF.Lean.HigherIndexClassIf using (U; Native)
open import OCF.Lean.HigherIndexFoldIf using (k; g; Source)
open import OCF.Lean.HigherIndexSupportIf
import OCF.Lean.HigherIndexSupportClosure as S
open import OCF.Lean.HigherIndexSupportFloor using (floor; floor-support)

Supported : Cd → HB U → HB Source → Set
Supported β B hz = ⊤
Supported β B (hs a) = Supported β B a
Supported β B (hl f) = ∀ n → Supported β B (f n)
Supported β B (hΩ (inj₁ _ , inj₁ (inj₁ ())) f)
Supported β B (hΩ (inj₁ _ , inj₁ (inj₂ _)) f) =
  ∀ e → β ⊲ e → LgB e → Supported (hs e) B (f e)
Supported β B (hΩ (inj₁ _ , inj₂ _) f) =
  ∀ e → (ad : AdmK k ((tt , β) , B) e) → Supported (proj₂ (proj₁ ad)) (hs e) (f e)
Supported β B (hΩ (inj₂ c , κ) f) = (c ⊲[ tt , β ] B × Event c β κ) ×
  (∀ e → (ad : Coord c κ β e) → Supported (next c κ β e ad) B (f e))

mono : ∀ {β β′ B B′} → β ⊲ β′ → B ⊲[ tt , β′ ] B′ →
  ∀ a → Supported β B a → Supported β′ B′ a
mono q r hz p = tt
mono q r (hs a) p = mono q r a p
mono q r (hl f) p = λ n → mono q r (f n) (p n)
mono q r (hΩ (inj₁ _ , inj₁ (inj₁ ())) f) p
mono q r (hΩ (inj₁ _ , inj₁ (inj₂ _)) f) p = λ e qe le →
  mono hself (⊲ᴮ↑ (tt , hsuc qe) r) (f e) (p e (⊲ᴮ-tr q qe) le)
mono q r (hΩ (inj₁ _ , inj₂ _) f) p = λ e ad →
  p e (proj₁ (LHRecIf.adm↓ J₁ k ((tt , q) , r) ad))
mono q r (hΩ (inj₂ c , κ) f) ((pc , ev) , p) =
  (⊲ᴮ-tr (⊲ᴮ↑ (tt , q) pc) r , S.event-up c q κ ev) , λ e ad →
  mono (proj₂ (S.coord-down c κ q e ad))
    (⊲ᴮ↑ (tt , S.next-up c κ _ e ad) r) (f e)
    (p e (proj₁ (S.coord-down c κ q e ad)))

add : ∀ {β B} a b → Supported β B a → Supported β B b → Supported β B (a ⊞ b)
add a hz pa pb = pa
add a (hs b) pa pb = add a b pa pb
add a (hl f) pa pb = λ n → add a (f n) pa (pb n)
add a (hΩ (inj₁ _ , inj₁ (inj₁ ())) f) pa pb
add a (hΩ (inj₁ _ , inj₁ (inj₂ _)) f) pa pb = λ e qe le →
  add a (f e) (mono (hsuc qe) hself a pa) (pb e qe le)
add a (hΩ (inj₁ _ , inj₂ _) f) pa pb = λ e ad →
  add a (f e) (mono (proj₂ (proj₁ (LHRecIf.nx-up J₁ k ad)))
    (proj₂ (LHRecIf.nx-up J₁ k ad)) a pa) (pb e ad)
add {β} a (hΩ (inj₂ c , κ) f) pa (ev , pb) = ev , λ e ad →
  add a (f e) (mono (S.next-up c κ β e ad) hself a pa) (pb e ad)

component : ∀ β B c → c ⊲[ tt , β ] B → ∀ a → Support c β a →
  Supported β B (ι (inj₂ c) a)
component β B c pc hz p = tt
component β B c pc (hs a) p = component β B c pc a p
component β B c pc (hl f) p = λ n → component β B c pc (f n) (p n)
component β B c pc (hΩ κ f) (ev , p) = (pc , ev) , λ e ad →
  component (next c κ β e ad) B c (⊲ᴮ↑ (tt , S.next-up c κ β e ad) pc) (f e) (p e ad)

θ : HB U → HB Source
θ = New.θ (cxI k g) (gcF (λ d → ι (inj₂ d) (flL (g d))))
θ-supported : ∀ β B e → e ⊲[ tt , β ] B → Supported β B (θ e)
θ-supported β B hz p = tt
θ-supported β B (hs e) p = add _ _
  (θ-supported β B e (⊲ᴮ-tr (hsuc hself) p))
  (component β B e (⊲ᴮ-tr (hsuc hself) p) (floor e) (floor-support e β))
θ-supported β B (hl f) p = λ n → θ-supported β B (f n) (⊲ᴮ-tr (hlim n hself) p)
θ-supported β B (hΩ (inj₁ ()) f) p
θ-supported β B (hΩ (inj₂ _) f) p = λ e qe le →
  θ-supported (hs e) B (f e)
    (⊲ᴮ-tr (hLim (hsuc hself) hself) (⊲ᴮ↑ (tt , hsuc qe) p))

input : HB Source
input = flL (lΩ k g)
input-legal : LgB input
input-legal = Lg-flL (lΩ k g)
input-supported : ∀ β B → Supported β B input
input-supported β B e ad = θ-supported (proj₂ (proj₁ ad)) (hs e) e (hsuc hself)
```

input-supported覆盖原完整高层地板，没有固定全raw Position假设。
它不是HigherIndexFoldStrategyRun的旧Path实例；旧运行器不可直接消费。
下一步需要消费分层准入的总运行器及其生成坐标闭包，尤其keep的raw
分支总定义。这里不把证书存在冒充输出闭项，更不宣称达到ψ₀Λ。
