# 获准坐标域内的原全部 Ω 行

qi 使用输入的原结构自相关证据；因此 tl 的高阶分支不需为任意
不相容 raw 回调补证。随后按原 HtB.Rec 组合 base/clos/chain，
保留每个原 ΩI 分量，不替换成预给地板。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildRelatedGenFloor (𝕊 : HtB) where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ordˢ; Ord₊ˢ; Ωˢ; intoˢ)
open import OCF.Free.Eq using (_≅ˢ_; s≅; l≅; ŝ≅; ĉ≅; s-invˢ; l-invˢ; i-respˢ; u-reflˢ; toZ-≅; Ωˢ-≅)
open import OCF.Free.Floor using (Flr; Ev; flo; cvFlo)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open import OCF.Align.TotalValueBuildRelatedGenIf 𝕊
open import OCF.Align.TotalValueBuildRelatedGenUp 𝕊 using (C)
open import OCF.Align.TotalValueBuildRelatedGenDown 𝕊 using (descend)
open import OCF.Align.TotalValueBuildRelatedGenGenerated 𝕊 using (successor-gen; limit-gen)

tl-core : ∀ {m c k χ} φ (cv : ∀ {L} → Ev L φ → Simᴵ k L)
  (x : Ordˢ k) → x ≅ˢ x → C m c (tl {χ = χ} φ cv x)
tl-core φ cv Ord₊ˢ.zero sx = tt
tl-core φ cv (Ord₊ˢ.suc x) sx = tl-core φ cv x (s-invˢ sx)
tl-core φ cv (Ord₊ˢ.lim f) sx = λ i → tl-core φ cv (f i) (l-invˢ sx i)
tl-core φ cv (Ord₊ˢ.limᵢ q f) sx = λ x ss → tl-core φ cv (f (intoˢ (<→◃ q) x)) (i-respˢ sx ss)
tl-core {k = suc k} φ cv (Ord₊ˢ.up zero x) sx = tl-core (flo k) (cvFlo k) x (u-reflˢ zero sx)
tl-core {k = lim f s} φ cv (Ord₊ˢ.up (self i) x) sx = tl-core (flo (f i)) (cvFlo (f i)) x (u-reflˢ (self i) sx)
tl-core {k = zero} φ cv (Ord₊ˢ.ŝ c t g) (ŝ≅ e ec et eg) =
  toZ-≅ et , (λ η d η′ d′ ee → toZ-≅ (eg η d η′ d′ ee)) ,
  tl-core φ cv t et , (λ η d → tl-core φ cv (g η d) (eg η d η d (≅ᴵ-refl η)))
tl-core {k = suc k} φ cv (Ord₊ˢ.ŝ c t g) (ŝ≅ e ec et eg) =
  tl-core φ cv t et , (λ η d → tl-core φ cv (g η d) (eg η d η d (≅ᴵ-refl η)))
tl-core {k = lim f s} φ cv (Ord₊ˢ.ŝ c t g) (ŝ≅ e ec et eg) =
  tl-core φ cv t et , (λ η d → tl-core φ cv (g η d) (eg η d η d (≅ᴵ-refl η)))
tl-core φ cv (Ord₊ˢ.ĉᴸ c t g o h) (ĉ≅ ec dt dg eo eh) =
  dt , dg , tl-core φ cv o eo , (λ η d → tl-core φ cv (h η d) (eh η d η d (≅ᴵ-refl η)))

GoodΩ : Ht → Set
GoodΩ m = ∀ a → Gen m a (Ω̇ m a)

row-core : ∀ m (I : ∀ {n} → n <ᴸ m → XΩ n) →
  (∀ {n} (q : n <ᴸ m) a → Gen n a (I q a)) →
  (v : View _<ᴸ_ h₀ m) → C m zero (rowV m I v)
row-core m I gi base =
  tl-core _ _ (Ωˢ (suc zero)) (Ωˢ-≅ (≅ᴵ-refl (suc zero))) ,
  (λ η → tl-core _ _ (Ωˢ η) (Ωˢ-≅ (≅ᴵ-refl η)))
row-core m I gi (clos q) = proj₂ (descend q (gi q (suc zero))) , (λ η → proj₂ (descend q (gi q η)))
row-core m I gi (chain F qq) zero = tt
row-core m I gi (chain F qq) (suc i) = proj₂ (descend (qq i) (gi (qq i) zero))

good-step : ∀ m → (∀ {n} → n <ᴸ m → GoodΩ n) → GoodΩ m
good-step m below zero = RΩ̇ m (≅ᴵ-refl zero) ,
  row-core m (ΩI m)
    (λ q a → subst (λ X → Gen _ a (X a)) (sym (ΩI≡ q)) (below q a)) (view m)
good-step m below (suc a) = successor-gen m a
good-step m below (lim f s) = limit-gen m f s (λ i → good-step m below (f i))

omega-gen : ∀ m a → Gen m a (Ω̇ m a)
omega-gen m = good-step m (Rec GoodΩ good-step m)
```
