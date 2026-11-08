# 原下降保持遗传生成域

原 ι↓ 将顶节点转为低高度节点。获准坐标由目标高度的 Gen
沿原 Rec-β 回到源高度，再沿原 ◃ 进入源回调；不要求任意 raw
坐标有证。marker 则直接取低字段，结构 Well 严格下降。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildAdmittedGenDown (𝕊 : HtB) where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Free.Level
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open import OCF.Align.TotalValueBuildAdmittedGenIf 𝕊
open import OCF.Align.TotalValueBuildAdmittedGenUp 𝕊 using (Well; acc; well; C)

down-core : ∀ {m m′ a b φ χ} → Well a → (δ : m <ᴸ m′) →
  (x : Q m a φ χ) → C m a x → C m′ b (ι↓ δ x)
down-core wa δ q0 gx = tt
down-core wa δ (qs x) gx = down-core wa δ x gx
down-core wa δ (ql f) gf = λ i → down-core wa δ (f i) (gf i)
down-core wa δ (qi ac f) gf = λ x sx → down-core wa δ (f x) (gf x sx)
down-core wa δ (qŝ c t g) (gt , gg) = down-core wa δ t gt , (λ η e → down-core wa δ (g η e) (gg η e))
down-core wa δ (qĉ c t g o h) (st , sg , go , gh) = st , sg , down-core wa δ o go , (λ η e → down-core wa δ (h η e) (gh η e))
down-core wa δ (qclo t g) (gt , gg) = down-core wa δ t gt , (λ η → down-core wa δ (g η) (gg η))
down-core wa δ (qcl q ψ s t g) (gt , gg) = down-core wa δ t gt , (λ η → down-core wa δ (g η) (gg η))
down-core wa δ (qwk le lc x) gx = down-core wa δ x gx
down-core {m} wa δ (qΩ↓ q fe ac h) gh = λ ξ ζ z gz →
  down-core wa δ (h ξ ζ (intoV q (outV (tr< q δ) z)))
    (gh ξ ζ (intoV q (outV (tr< q δ) z))
      (subst (GHeight m q) (sym (out-intoV q (outV (tr< q δ) z)))
        (height-in q (height-out (tr< q δ) gz))))
down-core {m} wa δ (qΩ fe q h) gh = λ ξ ζ z gz →
  down-core wa δ (h ξ ζ (intoU (<→◃ q) (outV δ z)))
    (gh ξ ζ (intoU (<→◃ q) (outV δ z))
      (subst (Low m (GHeight m) _ (<→◃ q))
        (sym (out-intoU (<→◃ q) (outV δ z)))
        (low-in (<→◃ q) (height-out δ gz))))
down-core {a = suc a} (acc next) δ (omk zero z x) (gz , eq) =
  down-core (next zero) δ z (proj₂ (low-out zero gz))
down-core {a = lim f s} (acc next) δ (omk (self i) z x) (gz , eq) =
  down-core (next (self i)) δ z (proj₂ (low-out {a = lim f s} (self i) gz))

descend : ∀ {m m′ a b φ χ} (δ : m <ᴸ m′) {x : Q m a φ χ} →
  Gen m a x → Gen m′ b (ι↓ δ x)
descend {a = a} δ {x} (rx , gx) = R-ι↓ δ (≅ᴵ-refl a) rx , down-core (well a) δ x gx
```
