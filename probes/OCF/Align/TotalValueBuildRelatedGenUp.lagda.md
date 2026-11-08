# 遗传生成域沿原 ι 保持

结构可达性沿 ◃ 而非严格值位置；极限 self 分量同样下降。
marker 直接使用 body Core，对原 body 子树递归；低 Gen 仍供下降保持使用。
无停机指示，不把关系相容当作函数等式。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildRelatedGenUp (𝕊 : HtB) where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Free.Level
open import OCF.Free.Tree using (<◃)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open import OCF.Align.TotalValueBuildRelatedGenIf 𝕊

-- 这里的路径包括 self，不要求原层号有严格列。
data Well (a : Ordᴵ) : Set where
  acc : (∀ {k} → k ◃ a → Well k) → Well a
well : ∀ a → Well a
well-below : ∀ {k} a → k ◃ a → Well k
well a = acc (well-below a)
well-below (suc a) zero = well a
well-below (suc a) (suc r) = well-below a r
well-below (lim f s) (self i) = well (f i)
well-below (lim f s) (lim i r) = well-below (f i) r

C : ∀ m a {φ χ} → Q m a φ χ → Set
C m a = Core m a (Low m (GHeight m) a) (GHeight m)

raise-core : ∀ {m a b φ χ} → Well a → (r : a ◃ b) →
  (x : Q m a φ χ) → C m a x → C m b (ι r x)
raise-core wa r q0 gx = tt
raise-core wa r (qs x) gx = raise-core wa r x gx
raise-core wa r (ql f) gf = λ i → raise-core wa r (f i) (gf i)
raise-core wa r (qi ac f) gf = λ x sx → raise-core wa r (f x) (gf x sx)
raise-core wa r (qŝ c t g) (gt , gg) = raise-core wa r t gt , (λ η e → raise-core wa r (g η e) (gg η e))
raise-core wa r (qĉ c t g o h) (st , sg , go , gh) = st , sg , raise-core wa r o go , (λ η e → raise-core wa r (h η e) (gh η e))
raise-core wa r (qclo t g) (gt , gg) = raise-core wa r t gt , (λ η → raise-core wa r (g η) (gg η))
raise-core wa r (qcl q ψ s t g) (gt , gg) = raise-core wa r t gt , (λ η → raise-core wa r (g η) (gg η))
raise-core wa r (qwk le lc x) gx = raise-core wa r x gx
raise-core wa r (qΩ↓ q fe ac h) gh = λ ξ ζ z gz → raise-core wa r (h ξ ζ z) (gh ξ ζ z gz)
raise-core {m} wa r (qΩ fe q h) gh = λ ξ ζ z gz →
  raise-core wa r (h ξ ζ (intoU (<→◃ q) (outU (<→◃ (<◃ q r)) z)))
    (gh ξ ζ (intoU (<→◃ q) (outU (<→◃ (<◃ q r)) z))
      (subst (Low m (GHeight m) _ (<→◃ q))
        (sym (out-intoU (<→◃ q) (outU (<→◃ (<◃ q r)) z)))
        (low-in (<→◃ q) (low-out (<→◃ (<◃ q r)) gz))))
raise-core wa r (omk q z x) (gz , gx , rel) = raise-core wa r x gx

raise : ∀ {m a b φ χ} (r : a ◃ b) {x : Q m a φ χ} →
  Gen m a x → Gen m b (ι r x)
raise {a = a} r {x} (rx , gx) = R-ι r r rx , raise-core (well a) r x gx
```
