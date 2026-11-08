# 原非零顶地板的跨层生成实例

坐标为任意原 Q n 0，不缩为纯树；其中仍可含所有低高度 Ω 与闭包。
source 顶 Ω 的全部实际回调使用此族。没有声称任意高阶坐标都自动可回收。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildRecoverGenerated (𝕊 : HtB) where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ; toZ; intoˢ)
open import OCF.Free.Aux using (tf)
open import OCF.Free.Eq using (_≅ᶻ_; _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; Ωˢ-≅; toZ-≅; _≈ᴿ_; limR; sucR; limᵢR; ŝR; ĉR; cloR; wkR)
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; Run; flo; cvFlo; toFlo; wk; limA; ∅ᴿ; _∼ᶠ_; fz∼; fk∼; fb∼; ⊔∼; ∼ᶠ-refl; bound; bound-≅; evF)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Free.Base using (clash; r∅)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open RestrQ
open import OCF.Free.Eq using (_≅ˢ_)

open import OCF.Align.TotalValueBuildRecoverIf 𝕊

below-cap : ∀ {m χ ρ bnd} → Sim∼ m χ ρ → Sim∼ m χ (cap ρ m bnd)
below-cap {m} {ρ = ρ} {bnd} c i q = subst (_ ∼ᶠ_) (sym (cap-lt ρ bnd q)) (c i q)

up-zero-down : ∀ {m m′ b φ χ ψ ρ} (δ : m <ᴸ m′)
  {x : Q m zero φ χ} {y : Q m zero ψ ρ} → Rq m zero zero x y →
  Cross δ (suc zero) b (ι zero x) (ι↓ δ y)
up-zero-down δ rz = dz
up-zero-down δ (rs sa sb r) = ds sa (below-cap sb) (up-zero-down δ r)
up-zero-down δ (rl h) = dl (λ i → up-zero-down δ (h i))
up-zero-down δ (ri d h) = di d (λ x y rel → up-zero-down δ (h x y rel))
up-zero-down δ (rŝ e r h) = dŝ e (up-zero-down δ r) (λ η ee η′ e′ rel → up-zero-down δ (h η ee η′ e′ rel))
up-zero-down δ (rĉ e dzz dg r h) = dĉ e dzz dg (up-zero-down δ r) (λ η ee η′ e′ rel → up-zero-down δ (h η ee η′ e′ rel))
up-zero-down δ (rclo s r h) = dclo s (up-zero-down δ r) (λ η η′ rel → up-zero-down δ (h η η′ rel))
up-zero-down δ (rcl {q = q} same s r h) = dcl s (up-zero-down δ r) (λ η η′ rel → dwkʳ (up-zero-down δ (h η η′ rel)))
up-zero-down δ (rwkˡ r) = dwkˡ (up-zero-down δ r)
up-zero-down δ (rwkʳ r) = dwkʳ (up-zero-down δ r)
up-zero-down {m} {m′} {b} δ (rΩ↓ {q = q} {h = h} {h′ = h′} same ek s c f) =
  dΩ↓ ek s (below-cap c) (λ ξ ξ′ ζ ζ′ ds dc z z′ rel → dwkʳ
    (subst (λ v → Cross δ (suc zero) b
      (ι zero (h ξ ζ (intoV q z))) (ι↓ δ (h′ ξ′ ζ′ (intoV q v))))
      (sym (out-intoV (tr< q δ) z′))
      (up-zero-down δ (f ξ ξ′ ζ ζ′ ds dc dc z z′ (intoVq q rel)))))

one-cross : ∀ {m m′ b} (δ : m <ᴸ m′) →
  Cross δ (suc zero) b (Ω̇ m (suc zero)) (ι↓ δ (Ω̇ m (suc zero)))
one-cross {m} {m′} {b} δ =
  dΩtop z≅ (∼ᶠ-refl Fl) (below-cap (λ i q → ∼ᶠ-refl Fl))
    (λ ξ ξ′ ζ ζ′ ds dc z z′ rel → dwkˡ (dwkʳ (dwkʳ
      (subst (λ v → Cross δ (suc zero) b
        (omk zero z (ι zero z))
        (qwk (λ e → e) (⇑ (cap-map m (λ e → toFlo zero (λ q → e (suc q))))) (ι↓ δ v)))
        (sym (out-intoV δ z′))
        (dwkʳ (dmark (up-zero-down δ rel)))))))
open import OCF.Align.TotalValueBuildRecoverRun 𝕊 using (recover)

one-recover : ∀ {m m′ b w} (δ : m <ᴸ m′) (ok : Ok w)
  (e : Eh m m′ w (cap (κ Fl) m (flo (suc zero)))) (p : zero <ᴵ w m) →
  Rq m zero zero (ψᵠ zero (Ω̇ m (suc zero)))
    (Ψ δ ok e p (ι↓ {α = b} δ (Ω̇ m (suc zero))))
one-recover δ ok e p = recover δ zero ok e p z≅ (one-cross δ)
```
