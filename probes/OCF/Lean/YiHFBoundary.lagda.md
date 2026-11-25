# 带高度族：现有验收工具的局部边界
验收文件；正规形边界的反演方法来自 `EmbVVStop`；初始段边界由码的有限投影证明。
`no-NF-target` 与 `no-NF-third` 只限制现有 `NF₁`，不否定对应值下界。
`no-prefix-zero/one` 只说原反馈链前两个高度；不推断后续高度。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiHFBoundary where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import OCF.Align.Standard using (c[]; c∷)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import OCF.Align.EBO using (T; ψ; natT; Ωs; Ωt)
open import OCF.Align.EmbVVLZStandardOmega using (Sb; sC; sΩ; sΩ²; sψ; sψ⁺; NF₁; n∷; nψ)
open import OCF.Lean.YiHFTarget using (Target)
open import OCF.Align.LadderOrdPos using (Code; cz; cs; cl)
open import OCF.Align.LadderOrdCode using (ωᶜ; ω²ᶜ)
open import OCF.Align.CrossMNode using (C)
open import OCF.Align.CrossMInst using (𝒯)
open import OCF.Align.CrossMUp using (_⊂_; ⊂r; es; el)

firstArg : T → T
firstArg [] = []
firstArg (ψ u a ∷ xs) = a

singleton-arg : ∀ {u a} → Sb u → u ≡ (ψ (natT 1) a ∷ []) →
  (a ≡ []) ⊎ (a ≡ natT 1)
singleton-arg (sψ⁺ k n c) e = inj₂ (sym (cong firstArg e))
singleton-arg (sψ n c) e = inj₂ (sym (cong firstArg e))
singleton-arg (sC c[]) ()
singleton-arg (sC (c∷ c)) ()
singleton-arg (sΩ c) e = inj₁ (sym (cong firstArg e))
singleton-arg (sΩ² n c) e = inj₁ (sym (cong firstArg e))

admitted : Sb (ψ (natT 1) (natT 1) ∷ [])
admitted = sψ zero c[]

no-Sb-target : Sb (ψ (natT 1) (Ωs []) ∷ []) → ⊥
no-Sb-target h with singleton-arg h refl
... | inj₁ ()
... | inj₂ ()
no-NF-target : NF₁ Target → ⊥
no-NF-target (n∷ (nψ _ _ (n∷ (nψ _ s _ _) _ _) _) _ _) = no-Sb-target s

tag : Code → ℕ
tag cz = 0
tag (cs c) = 1
tag (cl g) = 2
hd : Code → Code
hd cz = cz
hd (cs c) = c
hd (cl g) = g 0
snd : Code → Code
snd (cl g) = g 1
snd _ = cz

M₁ : Code
M₁ = C 𝒯 ωᶜ 1

data Avoid : Code → Set where
  az : Avoid cz
  as : ∀ {c} → Avoid c → Avoid (cs c)
  al : ∀ {g} → (cl g ≡ ω²ᶜ → ⊥) → Avoid (g 0) → Avoid (cl g)

avoid : ∀ {c} → Avoid c → ω²ᶜ ⊂ c → ⊥
avoid az ()
avoid (as h) (es e) = avoid h e
avoid (al neq h) ⊂r = neq refl
avoid (al neq h) (el e) = avoid h e

noω : ωᶜ ≡ ω²ᶜ → ⊥
noω e with cong (λ c → tag (hd c)) e
... | ()
noD : hd M₁ ≡ ω²ᶜ → ⊥
noD e with cong (λ c → tag (hd (snd c))) e
... | ()
noD0 : hd (hd M₁) ≡ ω²ᶜ → ⊥
noD0 e with cong (λ c → tag (snd c)) e
... | ()

safe₁ : Avoid M₁
safe₁ = as (al noD (al noD0 (al noω az)))

no-prefix-one : ω²ᶜ ⊂ C 𝒯 ωᶜ 1 → ⊥
no-prefix-one = avoid safe₁

no-prefix-zero : ω²ᶜ ⊂ C 𝒯 ωᶜ 0 → ⊥
no-prefix-zero = avoid (al noω az)

Third : T
Third = ψ [] (Ωt (ψ (natT 1) (natT 3) ∷ [])) ∷ []

no-Sb-third : Sb (ψ (natT 1) (natT 3) ∷ []) → ⊥
no-Sb-third h with singleton-arg h refl
... | inj₁ ()
... | inj₂ ()

no-NF-third : NF₁ Third → ⊥
no-NF-third (n∷ (nψ _ _ (n∷ (nψ _ s _ _) _ _) _) _ _) = no-Sb-third s
```
