# 判决的规格: 旧地板的树 (底座)

> 底座, 文本不含记号. 结论写在 [VerdictSpec](VerdictSpec.lagda.md). `fold`, `repA`, `Ω̂A` 是 [Uniform2Base](Uniform2Base.lagda.md) 的旧树, 证书是记号无关的 `Goodᴺ` ([NotFree](NotFree.lagda.md)). 导入链经过记号模块 (旧树的文件本来就这样); 定义切片见 [VerdictSpec](VerdictSpec.lagda.md).
>
> **`floor-high`, `reject-floor`.** 旧树的第 2 份副本的闭包, 界是 $L+1$, $L$ 是 `up (self n)` 留下来的地板. 所以它的证书 (`dy 0`) 要第 0 个链点的层号**高于** $L$. 这是合法性, 不是判决的正确性: **`CV` 看不到它**, 旧树的比较都由 `<ᴵ-dec` 算出, 都是对的. `reject-floor` 把 "第 0 个链点的层号不高于 $L$" 当前提. 这个前提对真实的 $L_1$ 成立, 但目前的证明 ([OmegaSqA](OmegaSqA.lagda.md) 的 `Z≺L`) 读了标签.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.VerdictSpecFloor where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; toZ; Ωˢ)
open import OCF.Align.NotFree using (Goodᴺ; gc; forceᴺ; forceᴺ-HS)
open import OCF.Align.Uniform2Base using
  (fold; repA; Ω̂A; ∅ᴿ; Flr; fz; fk; _⊔_; Ev; bound; Mx; Run; wk)
open import OCF.Align.OmegaSqA using (MxL)
```

## §1 地板把界抬高

```agda
module Leaf (L : Ordᴵ) (ℓ : Ordᴵ) (σ₁ : Simᴵ (suc zero) ℓ) (σ₂ : Simᴵ (suc L) ℓ) (p : zero <ᴵ ℓ)
            (cv : ∀ {L′} → Ev L′ (fk L) → Simᴵ (suc zero) L′) (pos : zero ≺ᴵ L) where

  X : Ordˢ zero
  X = repA 0 ∅ᴿ (fold 1 (fk L) cv (Ω̂A 0) Ord₊ˢ.zero) 2 (tt , (σ₁ , σ₂)) p

  Q : Run (fz ⊔ (fk zero ⊔ fk L))
  Q = wk 0 (λ { (u , v) → u , proj₁ v }) (Ω̂A 0 ∅ᴿ)

  t₀′ : Ordˢ zero
  t₀′ = fold 0 (fk zero) (λ e → e) Q (Ωˢ (suc zero)) ((tt , (σ₁ , σ₂)) , σ₁) p

  -- 第 0 个链点的层号高于地板
  floor-high : (G : Goodᴺ (toZ X)) → Σ (Ordᶜ zero) λ Y → Σ (HS Y) λ hY → L ≺ᴵ toLevel Y hY
  floor-high (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) =
    ys 0 , hy 0 , ≺ᴵ-respˡ (≅ᴵ-sym (subst (λ M → M ≅ᴵ L) (sym (MxL tt σ₁ σ₂ σ₁ p pos)) (≅ᴵ-refl L))) (sim (dy 0) zero)

  -- 如果第 0 个链点的层号不高于地板, 就没有证书
  reject-floor : (∀ (G₀ : Goodᴺ (toZ t₀′)) → toLevel (forceᴺ _ G₀) (forceᴺ-HS _ G₀) ≺ᴵ L) → Goodᴺ (toZ X) → ⊥
  reject-floor low (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) =
    ≺ᴵ-irrefl (≺ᴵ-trans L≺Y (≺ᴵ-respˡ (toLevel-≅ (hy 0) (forceᴺ-HS _ G₀) (≅-sym l₀)) (low G₀)))
    where
    L≺Y : L ≺ᴵ toLevel (ys 0) (hy 0)
    L≺Y = ≺ᴵ-respˡ (≅ᴵ-sym (subst (λ M → M ≅ᴵ L) (sym (MxL tt σ₁ σ₂ σ₁ p pos)) (≅ᴵ-refl L))) (sim (dy 0) zero)
```
