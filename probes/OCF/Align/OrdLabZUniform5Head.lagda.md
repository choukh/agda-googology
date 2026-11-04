# Uniform5Head (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [LadderLabZUniform5Head](LadderLabZUniform5Head.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZUniform5Head where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong) 
open import OCF.Align.OrdLabZLevel
import OCF.Align.EBO as E
open import OCF.Align.LadderLabZSystemOmega using (cmp-CΩ; cmp-ΩC; Ctbl-suc)
open import OCF.Align.OrdLabZDecouple using (Idx; lvI; Ilt; Ieq)
open import OCF.Align.OrdLabZClosure using (Pen)
open import OCF.Align.OrdLabZBachmann using (<sucT; pen→<; gt→<)
open import OCF.Align.OrdLabZGoodLBase using (Idx-Ctbl)
open import OCF.Align.OrdLabZUniform4Head using (Ωp) public
open import OCF.Align.LadderLabZUniform5Head public using (μ)
```

```agda
open E using (T; PT; cof; c1; cΩ; Ωt; 𝟏; sucT; pred; cmpᵀ; lt; eq; gt; Cmp; _<ᵀ_) renaming (ψ to ψᵗ)
```

## §1 下标

```agda
gtμ : ∀ {w} ν → Idx w → cmpᵀ (sucT (μ ν)) w ≡ gt
gtμ ν Iw = cmp-ΩC (Idx-Ctbl Iw) (sucT ν)

ltμ : ∀ {ν} τ → Idx ν → cmpᵀ (sucT ν) (μ τ) ≡ lt
ltμ τ I = cmp-CΩ (Ctbl-suc (Idx-Ctbl I)) τ
```

## §2 `<ᴵ-dec` 对上 `cmpᵀ`

```agda
module _ {k t ν τ} (Iν : Idx ν) (ek : k ≅ᴵ lvI Iν) (Iτ : Idx τ) (et : t ≅ᴵ lvI Iτ) where
  private
    lτt : lvI Iτ ≅ᴵ t
    lτt = ≅ᴵ-sym et

    upc : ∀ {a b} (Ia : Idx a) (Ib : Idx b) {x y} → x ≅ᴵ lvI Ia → y ≅ᴵ lvI Ib → a <ᵀ b → x ≺ᴵ y
    upc Ia Ib ex ey q = ≺ᴵ-respʳ (≺ᴵ-respˡ ex (Ilt Ia Ib q)) (≅ᴵ-sym ey)

    no< : k ≺ᴵ t → t ≺ᴵ k → ⊥
    no< a b = ≺ᴵ-irrefl (≺ᴵ-trans a b)

    no≅ : k ≺ᴵ t → k ≅ᴵ t → ⊥
    no≅ a e = ≺ᴵ-irrefl (≺ᴵ-respʳ a (≅ᴵ-sym e))

  pen-of : k ≺ᴵ t → Pen (cmpᵀ (sucT ν) τ)
  pen-of d with cmpᵀ (sucT ν) τ in c
  ... | lt = inj₁ refl
  ... | eq = inj₂ refl
  ... | gt with <sucT ν (gt→< _ _ c)
  ...   | inj₁ q = ⊥-elim (no< d (upc Iτ Iν et ek q))
  ...   | inj₂ refl = ⊥-elim (no≅ d (≅ᴵ-trans ek (≅ᴵ-trans (Ieq Iν Iτ) lτt)))

  gt-of : (k ≺ᴵ t → ⊥) → cmpᵀ (sucT ν) τ ≡ gt
  gt-of n with cmpᵀ (sucT ν) τ in c
  ... | gt = refl
  ... | lt = ⊥-elim (n (upc Iν Iτ ek et (pen→< ν τ (inj₁ c))))
  ... | eq = ⊥-elim (n (upc Iν Iτ ek et (pen→< ν τ (inj₂ c))))

  gt-ofᵇ : t ≺ᴵ k → cmpᵀ (sucT ν) τ ≡ gt
  gt-ofᵇ b = gt-of (λ a → no< a b)

  gt-ofᶜ : k ≅ᴵ t → cmpᵀ (sucT ν) τ ≡ gt
  gt-ofᶜ e = gt-of (λ a → no≅ a e)
```
