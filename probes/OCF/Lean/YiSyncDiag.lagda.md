# 静态对角线 ψ₁(Ω_{ℓ₀}) 在 Ω₁ 结点 `ψ₁ top` 之下 (关系 `⊴⁺`)

验收文件. 编译定理 `Diag : L.ψ (σB L.zero) (λ r → r) (L.Ω S2.ℓ₀) ⊴⁺ ψ₁ G.top`: 参照的 ψ₁(Ω_{ℓ₀}) = lim F₁ 经 `dg` 落在保留结点 `ψ₁ top = lc (inj₁ tt) K₁` 之下. 逐项 `F₁⊴K`: 每个 F₁ n 在 `top + Tw 2` 以上的一切分支 `K₁ a` 之下; n ≥ 1 取 [YiL1Base](YiL1Base.lagda.md) `chain₁` 的证明去掉最后一步 (`chain₁′`), n = 0 经 `F₁ 0 ≅ γ 1 1`. 只是下界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSyncDiag where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore hiding (Le)
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open NA using (⊴l; ⊴-+ˡ)
open import OCF.Lean.YiDlVOne using (V2; topᶜʷ)
import OCF.Lean.YiDlVBtbo as DB
open import OCF.Lean.YiShpOmega using (cpT)
open import OCF.Lean.YiShpSq using (ψ₁)
open import OCF.Lean.YiShpEps using (Tψ; K₁; γ1⊴)
open import OCF.Lean.YiShpTwo using (σB)
open import OCF.Lean.YiL1Stmt using (F₁)
open import OCF.Lean.YiL1Emb using (module Fix01; lower₁ᴱ; one≺; ⊴-cp; ℓ₀≅)
open import OCF.Lean.YiL1Chain using (one≺κ; ≺⊑; sucT)
open import OCF.Lean.YiL1Base using (ξ; Q; fixQ)
open import OCF.Lean.YiLeanValFin using (κ)
open import OCF.Lean.YiPEStep using (⊑⊕)
import OCF.Lean.YiBtboLower as YB
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.BTBOFullEmb using (PEmb)
open import OCF.Align.YiMonoEmb using (PEmb-∘)
open import OCF.Align.YiLvValBase using (γ)
import OCF.Align.Level as L
import OCF.Align.Stage2 as S2
open import OCF.Lean.YiSyncRel using (_⊴⁺_; dg; ≅⊴; ⊴→⊴⁺)
```

## 1 逐项

```agda
chain₁′ : ∀ n → F₁ (suc n) NA.⊴ K₁ (G.suc (ξ (proj₁ (YB.chainV (suc n)))))
chain₁′ n = ⊴l 1 (lower₁ᴱ (WL.nrmk zero (G.suc (ξ m))) (WL.nrmk-lgl zero (G.suc (ξ m))) P₂ r₁ e11
    (ℓ₀≅ (suc n)) _ (λ q → L.lim (suc n) q) (WL.Kfk zero Tψ (ξ m)))
  where
  m₀ = proj₁ (YB.chainV n)
  m = proj₁ (YB.chainV (suc n))
  E₀ = YB.emb (suc n) m (proj₂ (YB.chainV (suc n)))
  hE : ∀ {c} (r : c L.≺ᴵ D.L (suc n)) → L.suc L.zero L.≺ᴵ PEmb.map E₀ r
  hE r = ≺⊑ (one≺κ (suc m₀)) (⊑⊕ (κ m) _)
  P₁ = Fix01.P′ E₀ hE
  P₂ = PEmb-∘ P₁ (sucT (Q m))
  r₁ = one≺ (D.L n) (D.cert (suc n))
  e11 : PEmb.map P₂ r₁ L.≅ᴵ L.suc L.zero
  e11 = fixQ m (PEmb.bnd P₁ r₁)

γK : γ 1 1 NA.⊴ K₁ (G.suc G.top)
γK = ⊴l 1 (⊴-+ˡ (Tψ G.top) (⊴l 1 (γ1⊴ 1)))

F₁0≅ : F₁ 0 L.≅ γ 1 1
F₁0≅ = L.ψ-≅ {p = σB L.zero} {σ = λ q → L.lim 0 q} {p′ = L.zero} {σ′ = λ q → L.suc q}
  (L.≅ᴵ-refl (L.suc L.zero)) (L.Ω-refl (L.suc L.zero))
```

## 2 门槛 `top + Tw 2`

```agda
c0 : Cp zero (G.suc G.top) (plus zero G.top (W.Tw 2))
c0 = add-cp zero G.lc dnLc G.top (topᶜʷ zero V2 (λ _ → fold) G.top)

c₁ : ∀ k → Cp zero (G.suc (psum zero DB.obs k)) (W.Tw 2)
c₁ k = inj₂ (suc k , add-cp zero G.lc dnLc (psum zero DB.obs k)
  (topᶜʷ zero (DB.Vw (WL.Pk.co (DB.P (suc k))) (WL.Pk.lw (DB.P (suc k)))) (λ _ → fold) G.top))

F₁⊴K : ∀ n a → Cp zero (plus zero G.top (W.Tw 2)) a → F₁ n ⊴⁺ K₁ a
F₁⊴K zero a c = ≅⊴ F₁0≅ (⊴→⊴⁺ (⊴-cp γK (WL.Kfk-cp zero Tψ (cpT zero c0 c))))
F₁⊴K (suc n) a c = ⊴→⊴⁺ (⊴-cp (chain₁′ n) (WL.Kfk-cp zero Tψ
  (cpT zero (add-cp zero G.lc dnLc G.top (c₁ (proj₁ (YB.chainV (suc n))))) c)))

Diag : L.ψ (σB L.zero) (λ r → r) (L.Ω S2.ℓ₀) ⊴⁺ ψ₁ G.top
Diag = dg F₁⊴K
```
