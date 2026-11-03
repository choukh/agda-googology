> **机械克隆.** 由 `Uniform5Head` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 统一形 (五): 层号 $\Omega+\nu$ ($\nu$ 可数) 的记号规则

> 接 [Uniform4Head](Uniform4Head.lagda.md). 把 `μ m` ($m\in\mathbb N$) 换成 `μ ν` $=\Omega+\nu$, $\nu$ 是任意项; 用到的都只要 $\nu$ 带 `Idx`. `cmp<` 的规格换成 `<ᴵ-dec` 与 `cmpᵀ` 的相容 (§2): 层号 $k\cong$ `lvI Iν`, $t\cong$ `lvI Iτ`. $k\prec t$ 给 `Pen (cmpᵀ (ν+1) τ)` (穿透), $t\prec k$ 或 $k\cong t$ 给 `gt` (折叠). 证明只用 `Ilt`/`Ieq` (已有) 加离散性 `<sucT`: **没有 `pickMax`, `Idx` 的定义不变.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZUniform5Head where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
import OCF.Align.EBO as E
open E using (T; PT; cof; c1; cΩ; Ωt; 𝟏; sucT; pred; cmpᵀ; lt; eq; gt; Cmp; _<ᵀ_) renaming (ψ to ψᵗ)
open import OCF.Align.ScafLadderZSystemOmega using (cmp-CΩ; cmp-ΩC; Ctbl-suc)
open import OCF.Align.ScafLadderZDecouple using (Idx; lvI; Ilt; Ieq)
open import OCF.Align.Closure using (Pen)
open import OCF.Align.Bachmann using (<sucT; pen→<; gt→<)
open import OCF.Align.ScafLadderZGoodLBase using (Idx-Ctbl)
open import OCF.Align.ScafLadderZUniform4Head using (Ωp) public
```

## §1 下标

```agda
μ : T → T
μ ν = Ωp ∷ ν

gtμ : ∀ {w} ν → Idx w → cmpᵀ (sucT (μ ν)) w ≡ gt
gtμ ν Iw = cmp-ΩC (Idx-Ctbl Iw) (sucT ν)

ltμ : ∀ {ν} τ → Idx ν → cmpᵀ (sucT ν) (μ τ) ≡ lt
ltμ τ I = cmp-CΩ (Ctbl-suc (Idx-Ctbl I)) τ
```

## §2 `<ᴵ-dec` 对上 `cmpᵀ`

```agda
module _ {k t ν τ} (Iν : Idx ν) (ek : k ≅ᴵ lvI Iν) (Iτ : Idx τ) (et : t ≅ᴵ lvI Iτ) where
  private
    lνk : lvI Iν ≅ᴵ k
    lνk = ≅ᴵ-sym ek
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
