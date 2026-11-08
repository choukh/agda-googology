# 遗传生成域的原全后继行与极限闭包

这一步包含任意源高度和任意后继参数，不只参数一。原 Ω 回调
接收获准的完整低坐标，然后确切保留 marker 的低字段与 ι body。
极限闭包保全部原 self 分量，既不删退化列，也不加入严格列前提。
尚未在此证明零行、ψ/Ψ 及下降的完整联立闭包。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildRelatedGenGenerated (𝕊 : HtB) where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; subst)
open import OCF.Free.Level
open import OCF.Free.Tree using (Fl)
open import OCF.Free.Floor using (Flr; Ev; _⊔_; _∼ᶠ_; ∼ᶠ-refl)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open import OCF.Align.TotalValueBuildRelatedGenIf 𝕊
open import OCF.Align.TotalValueBuildRelatedGenUp 𝕊 using (raise)

zero-gen : ∀ m a {φ χ} → Gen m a (q0 {φ = φ} {χ = χ})
zero-gen m a = rz , tt

successor-gen : ∀ m a → Gen m (suc a) (Ω̇ m (suc a))
successor-gen m a = RΩ̇ m (≅ᴵ-refl (suc a)) , (λ ξ ζ z gz → gz , proj₂ (raise zero gz) , R-ι zero zero (proj₁ gz))

limit-gen : ∀ m f s → (∀ i → Gen m (f i) (Ω̇ m (f i))) →
  Gen m (lim f s) (Ω̇ m (lim f s))
limit-gen m f s gf = RΩ̇ m (≅ᴵ-refl (lim f s)) , (λ i → gf i , proj₂ (raise (self i) (gf i)) , R-ι (self i) (self i) (proj₁ (gf i)))

-- 原顶 Ω 的全部实际获准回调；z 不是纯坐标替身。
successor-callback : ∀ m a ξ ζ (z : Q m a ξ ζ) → Gen m a z →
  Core m (suc a) (Low m (GHeight m) (suc a)) (GHeight m)
    (qwk {φ′ = ξ ⊔ Fl} {χ′ = lo m ζ ∪ κ Fl}
      proj₁ (λ i q e → subst (Ev _) (lo-lt ζ q) (proj₁ e))
      (omk zero z (ι zero z)))
successor-callback m a ξ ζ z gz = gz , proj₂ (raise zero gz) , R-ι zero zero (proj₁ gz)
```
