# 关系生成域的原部分和与反馈轨道闭包

这里不改原 repᵠ 与 chainᵠ。加法的 marker 分支按原程序读取 body，
证书使用 body Core；种子仍为该层原完整 Ω̇。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildRelatedGenOps (𝕊 : HtB) where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Free.Level
open import OCF.Free.Tree using (Fl)
open import OCF.Free.Floor using (Ev; ∼ᶠ-refl)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open import OCF.Align.TotalValueBuildRelatedGenIf 𝕊
open import OCF.Align.TotalValueBuildRelatedGenUp 𝕊 using (C)
open import OCF.Align.TotalValueBuildRelatedGenFloor 𝕊 using (omega-gen)

add-core : ∀ {m a φ χ ψ ρ} {W : Q m a φ χ} → C m a W →
  (x : Q m a ψ ρ) → C m a x → C m a (W ⊞ x)
add-core gW q0 gx = gW
add-core gW (qs x) gx = add-core gW x gx
add-core gW (ql f) gf = λ i → add-core gW (f i) (gf i)
add-core gW (qi ac f) gf = λ x sx → add-core gW (f x) (gf x sx)
add-core gW (qŝ c t g) (gt , gg) = add-core gW t gt , (λ η e → add-core gW (g η e) (gg η e))
add-core gW (qĉ c t g o h) (st , sg , go , gh) = st , sg , add-core gW o go , (λ η e → add-core gW (h η e) (gh η e))
add-core gW (qclo t g) (gt , gg) = add-core gW t gt , (λ η → add-core gW (g η) (gg η))
add-core gW (qcl q ψ s t g) (gt , gg) = add-core gW t gt , (λ η → add-core gW (g η) (gg η))
add-core gW (qwk le lc x) gx = add-core gW x gx
add-core gW (qΩ↓ q fe ac h) gh = λ ξ ζ z gz → add-core gW (h ξ ζ z) (gh ξ ζ z gz)
add-core gW (qΩ fe q h) gh = λ ξ ζ z gz → add-core gW (h ξ ζ z) (gh ξ ζ z gz)
add-core gW (omk q z x) (gz , gx , rel) = add-core gW x gx

add : ∀ {m a φ χ ψ ρ} {W : Q m a φ χ} {x : Q m a ψ ρ} →
  Gen m a W → Gen m a x → Gen m a (W ⊞ x)
add (rW , gW) (rx , gx) = R-⊞ (∼ᶠ-refl _) (λ i p → ∼ᶠ-refl _) rW rx , add-core gW _ gx

repeat-core : ∀ {m a φ χ} {x : Q m a φ χ} → C m a x → ∀ n → C m a (repᵠ x n)
repeat-core gx zero = tt
repeat-core gx (suc zero) = gx
repeat-core {x = x} gx (suc (suc n)) = add-core (repeat-core gx (suc n)) x gx
repeat : ∀ {m a φ χ} {x : Q m a φ χ} → Gen m a x → ∀ n → Gen m a (repᵠ x n)
repeat (rx , gx) n = R-repᵠ (∼ᶠ-refl _) (λ i p → ∼ᶠ-refl _) rx n , repeat-core gx n

chain-gen : ∀ {m a φ χ} (fe : ∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) (fc : Sub m χ (κ Fl))
  (f : Q m a φ χ → Q m a φ χ) →
  (∀ z → Gen m a z → Gen m a (f z)) → ∀ n → Gen m a (chainᵠ fe fc f n)
chain-gen {m} {a} fe fc f gf zero = rwk (proj₁ (omega-gen m a)) , proj₂ (omega-gen m a)
chain-gen fe fc f gf (suc n) = gf (chainᵠ fe fc f n) (chain-gen fe fc f gf n)
```
