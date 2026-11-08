# 关系 marker 生成域沿原层同构运输

同时递归原层结构可达证与源树。低坐标反送使用原 resQ/res⁻Q，
marker 的 body 用关系通勤，不把函数逐点关系改写为等式。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildRelatedGenTransport (𝕊 : HtB) where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Free.Level
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open import OCF.Align.TotalValueBuildRelatedGenIf 𝕊
open import OCF.Align.TotalValueBuildRelatedGenUp 𝕊 using (Well; acc; well; C)
open import OCF.Align.TotalValueTransportSuccessor 𝕊
open import OCF.Align.TotalValueTransportLimit 𝕊

mutual
  move : ∀ {m a b φ χ} → Well a → Well b → (e : a ≅ᴵ b) →
    {x : Q m a φ χ} → Gen m a x → Gen m b (trQ e x)
  move wa wb e (rx , gx) = R-trʳ e (R-trˡ e rx) , move-core wa wb e _ gx

  unmove : ∀ {m a b φ χ} → Well a → Well b → (e : a ≅ᴵ b) →
    {x : Q m b φ χ} → Gen m b x → Gen m a (tr⁻Q e x)
  unmove wa wb e (rx , gx) = R-tr⁻ʳ e (R-tr⁻ˡ e rx) , unmove-core wa wb e _ gx

  back : ∀ {m a b j φ χ} → Well a → Well b → (q : j <ᴵ a) → (e : a ≅ᴵ b) →
    {x : Q m (repQ (resQ {m} q e)) φ χ} →
    Gen m _ x → Gen m j (backQ (resQ q e) x)
  back (acc fa) (acc fb) zero (s≅ e) gx = unmove (fa zero) (fb zero) e gx
  back (acc fa) (acc fb) (suc q) (s≅ e) gx = back (fa zero) (fb zero) q e gx
  back (acc fa) (acc fb) (lim i q) (l≅ e) gx = back (fa (self i)) (fb (self i)) q (e i) gx

  back⁻ : ∀ {m a b j φ χ} → Well a → Well b → (q : j <ᴵ b) → (e : a ≅ᴵ b) →
    {x : Q m (repQ (res⁻Q {m} q e)) φ χ} →
    Gen m _ x → Gen m j (backQ (res⁻Q q e) x)
  back⁻ (acc fa) (acc fb) zero (s≅ e) gx = move (fa zero) (fb zero) e gx
  back⁻ (acc fa) (acc fb) (suc q) (s≅ e) gx = back⁻ (fa zero) (fb zero) q e gx
  back⁻ (acc fa) (acc fb) (lim i q) (l≅ e) gx = back⁻ (fa (self i)) (fb (self i)) q (e i) gx

  move-core : ∀ {m a b φ χ} → Well a → Well b → (e : a ≅ᴵ b) →
    (x : Q m a φ χ) → C m a x → C m b (trQ e x)
  move-core wa wb e q0 gx = tt
  move-core wa wb e (qs x) gx = move-core wa wb e x gx
  move-core wa wb e (ql f) gf = λ i → move-core wa wb e (f i) (gf i)
  move-core wa wb e (qi ac f) gf = λ x sx → move-core wa wb e (f x) (gf x sx)
  move-core wa wb e (qŝ c t g) (gt , gg) = move-core wa wb e t gt , (λ η d → move-core wa wb e (g η d) (gg η d))
  move-core wa wb e (qĉ c t g o h) (st , sg , go , gh) = st , sg , move-core wa wb e o go , (λ η d → move-core wa wb e (h η d) (gh η d))
  move-core wa wb e (qclo t g) (gt , gg) = move-core wa wb e t gt , (λ η → move-core wa wb e (g η) (gg η))
  move-core wa wb e (qcl q ψ st t g) (gt , gg) = move-core wa wb e t gt , (λ η → move-core wa wb e (g η) (gg η))
  move-core wa wb e (qwk le lc x) gx = move-core wa wb e x gx
  move-core wa wb e (qΩ↓ q fe ac h) gh = λ ξ ζ z gz → move-core wa wb e (h ξ ζ z) (gh ξ ζ z gz)
  move-core {m} wa wb e (qΩ fe q h) gh = λ ξ ζ z gz →
    move-core wa wb e (h ξ ζ (intoU (<→◃ q) (backQ (resQ q e) (outU (<→◃ (ltQ (resQ q e))) z))))
      (gh ξ ζ (intoU (<→◃ q) (backQ (resQ q e) (outU (<→◃ (ltQ (resQ q e))) z)))
        (subst (Low m (GHeight m) _ (<→◃ q))
          (sym (out-intoU (<→◃ q) (backQ (resQ q e) (outU (<→◃ (ltQ (resQ q e))) z))))
          (low-in (<→◃ q) (back wa wb q e (low-out (<→◃ (ltQ (resQ q e))) gz)))))
  move-core (acc fa) (acc fb) (s≅ e) (omk zero z x) (gz , gx , rel) =
    move (fa zero) (fb zero) e gz ,
    move-core (acc fa) (acc fb) (s≅ e) x gx , successor-marker e rel
  move-core (acc fa) (acc fb) (l≅ e) (omk (self i) z x) (gz , gx , rel) =
    move (fa (self i)) (fb (self i)) (e i) gz ,
    move-core (acc fa) (acc fb) (l≅ e) x gx , limit-marker e i rel

  unmove-core : ∀ {m a b φ χ} → Well a → Well b → (e : a ≅ᴵ b) →
    (x : Q m b φ χ) → C m b x → C m a (tr⁻Q e x)
  unmove-core wa wb e q0 gx = tt
  unmove-core wa wb e (qs x) gx = unmove-core wa wb e x gx
  unmove-core wa wb e (ql f) gf = λ i → unmove-core wa wb e (f i) (gf i)
  unmove-core wa wb e (qi ac f) gf = λ x sx → unmove-core wa wb e (f x) (gf x sx)
  unmove-core wa wb e (qŝ c t g) (gt , gg) = unmove-core wa wb e t gt , (λ η d → unmove-core wa wb e (g η d) (gg η d))
  unmove-core wa wb e (qĉ c t g o h) (st , sg , go , gh) = st , sg , unmove-core wa wb e o go , (λ η d → unmove-core wa wb e (h η d) (gh η d))
  unmove-core wa wb e (qclo t g) (gt , gg) = unmove-core wa wb e t gt , (λ η → unmove-core wa wb e (g η) (gg η))
  unmove-core wa wb e (qcl q ψ st t g) (gt , gg) = unmove-core wa wb e t gt , (λ η → unmove-core wa wb e (g η) (gg η))
  unmove-core wa wb e (qwk le lc x) gx = unmove-core wa wb e x gx
  unmove-core wa wb e (qΩ↓ q fe ac h) gh = λ ξ ζ z gz → unmove-core wa wb e (h ξ ζ z) (gh ξ ζ z gz)
  unmove-core {m} wa wb e (qΩ fe q h) gh = λ ξ ζ z gz →
    unmove-core wa wb e (h ξ ζ (intoU (<→◃ q) (backQ (res⁻Q q e) (outU (<→◃ (ltQ (res⁻Q q e))) z))))
      (gh ξ ζ (intoU (<→◃ q) (backQ (res⁻Q q e) (outU (<→◃ (ltQ (res⁻Q q e))) z)))
        (subst (Low m (GHeight m) _ (<→◃ q))
          (sym (out-intoU (<→◃ q) (backQ (res⁻Q q e) (outU (<→◃ (ltQ (res⁻Q q e))) z))))
          (low-in (<→◃ q) (back⁻ wa wb q e (low-out (<→◃ (ltQ (res⁻Q q e))) gz)))))
  unmove-core (acc fa) (acc fb) (s≅ e) (omk zero z x) (gz , gx , rel) =
    unmove (fa zero) (fb zero) e gz ,
    unmove-core (acc fa) (acc fb) (s≅ e) x gx , successor-marker-back e rel
  unmove-core (acc fa) (acc fb) (l≅ e) (omk (self i) z x) (gz , gx , rel) =
    unmove (fa (self i)) (fb (self i)) (e i) gz ,
    unmove-core (acc fa) (acc fb) (l≅ e) x gx , limit-marker-back e i rel

transport : ∀ {m a b φ χ} (e : a ≅ᴵ b) {x : Q m a φ χ} →
  Gen m a x → Gen m b (trQ e x)
transport {a = a} {b} e = move (well a) (well b) e
transport-back : ∀ {m a b φ χ} (e : a ≅ᴵ b) {x : Q m b φ χ} →
  Gen m b x → Gen m a (tr⁻Q e x)
transport-back {a = a} {b} e = unmove (well a) (well b) e
```
