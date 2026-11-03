# 一切深度: 底抬高封闭性的否定 (编译)

> 接 [UniformNF3D3T](UniformNF3D3T.lagda.md). [UniformNF3D2U](UniformNF3D2U.lagda.md) §4 怕的封闭性是: `fo O X P Q ∈ 𝓚` 且 $B\sqsupseteq Q$ 推出 `fo O X P B ∈ 𝓚`. 结论先说:
>
> 1. **`¬BaseRaise`: 这条封闭性对满足 `clk` 的类是假的.** 在深度 1 的最小例子上编译: $X=\Theta_0$, $Q=\emptyset$, $B=\Theta_0\,\emptyset$, 尾巴 $a=$ `up zero 1`, 层号 1. 类取 "$C\approx O_0$ 或 `FlOver a O₀ C`", 它满足 `bs` 的全部三个字段 `clk`, `cgk`, `ho`. 尾巴 $t=0$ 处 $X\,B=\Theta_0\Theta_0\emptyset$ 严格低于 $F_a\,Q\ni\Theta_0\Theta_0\Theta_0\emptyset$.
> 2. 所以 D2U §4 的路线走不通, 也不需要走: 真正要的是 "头值压过 $F_a\,P\,s$" 的抬高 ([UniformNF3D3R](UniformNF3D3R.lagda.md) `kUp`).
>
> 深度 2 的同形例子 $B\sqsupseteq Q$ 只在纸面: 比较要读两族不同的树, 这里不编译. 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D3Neg where

open import Level using () renaming (lift to ↑)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; toZ)
open import OCF.Align.UniformNF3Eq using (_≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; upˡ; upʳ; toZ-≅)
open import OCF.Align.Uniform3Base using (fz; fk; _⊔_; Ev; flo; cvFlo)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-≅)
open import OCF.Align.UniformNF3D3O using (Fr; Sp; sf; fold1; repU; rowU; Obs; idO; fo1; run; _≈ᵒ_; run-≅)
open import OCF.Align.UniformNF3D3N using (Goodᴺ-tr)
open import OCF.Align.UniformNF3D3G using (𝟏; ≅→⊑ᴱ; up-rᴱ; _⊑ᴱ_; Ctx; FFl; FlU; FlU≈; SF; SF≈; fflF; flRep; leHd; F≅; lim-rᴱ; Rs)
open import OCF.Align.UniformNF3D3C
open import OCF.Align.UniformNF3D3F using (VF)
open import OCF.Align.UniformNF3D3S using (read1)
open import OCF.Align.UniformNF3D3W
open import OCF.Align.UniformNF3D3H using (module FF1)
open import OCF.Align.UniformNF3D3T using (Θ₀; RFΘ₀; ∅U; pfl∅U; w∅; RF∅; b⊤)

BaseRaise : Set₁
BaseRaise = ∀ (𝓚 : Cl (suc zero)) {a : Ordˢ (suc zero)} → a ≅ˢ a → (∀ {O C″} → 𝓚 O → FlOver a O C″ → 𝓚 C″) →
            (∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓚 C′ → 𝓚 C) → (∀ {C} → 𝓚 C → Hon (suc zero) a C) →
            ∀ {Q B : Sp 1} → SF Q → SF B →
            (∀ {i ℓ} (e : Ev ℓ (sf Q)) (e′ : Ev ℓ (sf B)) (p : i <ᴵ ℓ) → proj₁ (proj₂ Q) tt e p ⊑ᴱ proj₁ (proj₂ B) tt e′ p) →
            ∀ {ℓ} {ev : Ev ℓ (sf Q ⊔ (fk zero ⊔ fk zero))} {ev′ : Ev ℓ (sf B ⊔ (fk zero ⊔ fk zero))} {p : zero <ᴵ ℓ} →
            𝓚 (fo1 {k = suc zero} idO Θ₀ Q ev p) → 𝓚 (fo1 {k = suc zero} idO Θ₀ B ev′ p)
```

## §1 例子

```agda
fΘ₀ : FFl Θ₀
fΘ₀ = fX RFΘ₀

F₀ : Fr 1 (fk zero ⊔ fz)
F₀ = fold1 (flo zero) (cvFlo zero) Θ₀ Ord₊ˢ.zero

fF₀ : FFl F₀
fF₀ = fflF fΘ₀ z≅

rep : ℕ → Fr 0 (fz ⊔ (fk zero ⊔ fz))
rep = repU ∅U F₀

flr : ∀ m → FlU 0 (rep (suc m))
flr m = flRep 0 pfl∅U fF₀ m

Q₀ B₀ : Sp 1
Q₀ = fz , ∅U , tt
B₀ = (fz ⊔ (fk zero ⊔ fz)) , rep 1 , tt

sfQ : SF Q₀
sfQ = pfl∅U , tt

sfB : SF B₀
sfB = flr 0 , tt

a₀ : Ordˢ (suc zero)
a₀ = Ord₊ˢ.up zero (Ord₊ˢ.suc Ord₊ˢ.zero)

ea : a₀ ≅ˢ a₀
ea = upˡ (upʳ (s≅ z≅ z≅))

σ₁ : Simᴵ (suc zero) (suc zero)
σ₁ q = q

ev₀ : Ev (suc zero) (sf Q₀ ⊔ (fk zero ⊔ fk zero))
ev₀ = (tt , tt) , (σ₁ , σ₁)

ev₁ : Ev (suc zero) (sf B₀ ⊔ (fk zero ⊔ fk zero))
ev₁ = (tt , (tt , (σ₁ , tt))) , (σ₁ , σ₁)

p₁ : zero <ᴵ suc zero
p₁ = zero

O₀ : Obs (suc zero)
O₀ = fo1 idO Θ₀ Q₀ ev₀ p₁

C₀ : Obs (suc zero)
C₀ = fo1 idO Θ₀ B₀ ev₁ p₁

𝓚₀ : Cl (suc zero)
𝓚₀ C = Ctx C × ((C ≈ᵒ O₀) ⊎ FlOver a₀ O₀ C)

clk₀ : ∀ {O C″} → 𝓚₀ O → FlOver a₀ O C″ → 𝓚₀ C″
clk₀ (_ , inj₁ o) h = cxo h , inj₂ (flo-over (cxo h) (λ t et G →
  let R = flw h t et G
      d = toZ-≅ (run-≅ o ea)
      H′ = Goodᴺ-tr d (proj₁ R)
  in H′ , ⊑-trans (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym d) H′ (proj₁ R))) (proj₂ R)))
clk₀ (_ , inj₂ h₀) h = cxo h , inj₂ (flo-over (cxo h) (λ t et G →
  let R₁ = flw h t et G
      R₂ = flw h₀ a₀ ea (proj₁ R₁)
  in proj₁ R₂ , ⊑-trans (proj₂ R₂) (proj₂ R₁)))

cgk₀ : ∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓚₀ C′ → 𝓚₀ C
cgk₀ c₀ o (_ , inj₁ o′) = c₀ , inj₁ (≈-trans o o′)
cgk₀ c₀ o (_ , inj₂ h) = c₀ , inj₂ (flo-over c₀ (λ t et G →
  let d = toZ-≅ (run-≅ o et)
      G′ = Goodᴺ-tr d G
      R = flw h t et G′
  in proj₁ R , ⊑-trans (proj₂ R) (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym d) G′ G))))

ho₀ : ∀ {C} → 𝓚₀ C → Hon (suc zero) a₀ C
ho₀ {C} (c , _) G = read1 C c a₀ ea (up-rᴱ {r = zero} (≅→⊑ᴱ {x = 𝟏} (s≅ z≅ z≅))) G

e₂ : Ev (suc zero) (sf Q₀ ⊔ (fk zero ⊔ fz))
e₂ = (tt , tt) , (σ₁ , tt)

e₃ : Ev (suc zero) (fz ⊔ (fz ⊔ (fk zero ⊔ fz)))
e₃ = tt , (tt , (σ₁ , tt))

y₀ : Ordˢ zero
y₀ = run O₀ a₀

x₂ : Ordˢ zero
x₂ = rep 2 tt e₃ p₁

x₃ : Ordˢ zero
x₃ = run C₀ Ord₊ˢ.zero

ex₂ : x₂ ≅ˢ x₂
ex₂ = FlU≈ 0 (flr 1) {tt} {tt} tt e₃ p₁ e₃ p₁ (≅ᴵ-refl zero)

ex₂₃ : x₂ ≅ˢ x₃
ex₂₃ = FFl.rE fΘ₀ (SF≈ sfB) _ p₁ _ p₁ (≅ᴵ-refl zero)

sx : Ord₊ˢ.suc x₂ ⊑ᴱ y₀
sx = lim-rᴱ {h = λ m → rep m tt e₃ p₁} 3 (FFl.stE fF₀ (flr 1 , tt) (e₃ , (σ₁ , tt)) p₁)

Gy : Goodᴺ (toZ y₀)
Gy = Good→N (refl , tt) (FF1.FF₁ RFΘ₀ (FF1.pk b⊤ (fz , ∅U , w∅ , RF∅ , ↑ tt) (b⊤ , (λ _ → tt) , ↑ (λ _ _ → tt) , ↑ tt) (↑ (λ _ _ → tt)))
       {k = zero} {ev = e₂} {p = p₁} {𝓖 = isId} {𝓖′ = VF (λ _ → ⊤) zero} {x = Ord₊ˢ.suc Ord₊ˢ.zero} refl (λ v → v) (refl , tt) (b1 z≅) (s≅ z≅ z≅))

¬BaseRaise : BaseRaise → ⊥
¬BaseRaise BR with BR 𝓚₀ {a₀} ea clk₀ cgk₀ ho₀ {Q₀} {B₀} sfQ sfB
       (λ e e′ p → leHd {E = F₀} {Q = Q₀} fF₀ sfQ ((proj₁ e′ , proj₁ (proj₂ e′)) , proj₂ (proj₂ e′)) p) {ev = ev₀} {ev′ = ev₁} {p = p₁} ((fΘ₀ , sfQ , tt) , inj₁ (fo1 idO (FFl.rE fΘ₀) (SF≈ sfQ)))
... | _ , inj₁ ()
... | _ , inj₂ fo = ≺-irrefl (≅→⊑ (≅-sym e₄) (proj₂ L (proj₂ S)))
  where
  G₂ = proj₁ (Rs {a = x₂} {y = y₀} ex₂ sx {O = idO} {O′ = idO} idO tt Gy)
  G₃ : Goodᴺ (toZ x₃)
  G₃ = Goodᴺ-tr (toZ-≅ ex₂₃) G₂
  L = flw fo Ord₊ˢ.zero z≅ G₃
  S = Rs {a = x₂} {y = y₀} ex₂ sx {O = idO} {O′ = idO} idO tt (proj₁ L)
  e₄ : forceᴺ _ (proj₁ S) ≅ forceᴺ _ G₃
  e₄ = forceᴺ-≅ (toZ-≅ ex₂₃) (proj₁ S) G₃
```
