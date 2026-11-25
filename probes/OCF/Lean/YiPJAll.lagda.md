# 任意有限路径的折叠保持
验收文件；编译定理。源与目标层号均带等式，all 沿任意实际路径结构归纳填满 Pres。
self 用有限端点证书换型与已有 Qu/PF，inc/inu 用 YiPJDown 的一步；没有路径规范形前提。
不改树、折叠、合法性与原关系；完整 ω+1 的 Q 另证。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPJAll where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using (_++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow hiding (nat; fn; h₁)
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiHCBridge using (MB; GBB)
open import OCF.Lean.YiANFam using (ψᴺ)
open import OCF.Lean.YiPJCase using (unique)
open import OCF.Lean.YiPJDown using (Mode; ic; uc; DLF)
import OCF.Lean.YiLTFold as Old
import OCF.Align.EboLeanDef as E

Pres : (N : ℕ) (ℓ : L) → ℓ ≡ fn N → (j : ℕ) (j′ : L) → j′ ≡ fn j → j′ ≤ ℓ → Set
Pres N ℓ e j j′ e′ v = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (t₀ : E.T) → GBB ℓ e B t₀
  → (β : Tr⁺ j′) → MB j′ e′ (ψᴺ j t₀) (proj₁ β)
  → ∀ {a x} → MB ℓ e a x → MB j′ e′ (ψᴺ j (t₀ ++ a)) (proj₁ (ψ ℓ o r B j′ v β x))

samePF : ∀ N ℓ (e : ℓ ≡ fn N) → Pres N ℓ e N ℓ e self
samePF zero _ refl o r B t₀ gb β hβ m = Old.Qu o r B self β hβ m
samePF (suc N) _ refl o r B t₀ gb β hβ m = Old.Self.PF N o r B β hβ m

selfPJ : ∀ N ℓ (e : ℓ ≡ fn N) j (e′ : ℓ ≡ fn j) → Pres N ℓ e j ℓ e′ self
selfPJ N ℓ e j e′ = subst (λ p → Pres N ℓ e (proj₁ p) ℓ (proj₂ p) self)
  (unique ℓ (N , e) (j , e′)) (samePF N ℓ e)

stepP : ∀ {a b} → Mode → a ≤ b → a ≤ nd sS (λ _ → b)
stepP ic u = inc tt u
stepP uc u = inu (λ _ → u)

downJ : ∀ mode n j j′ (e′ : j′ ≡ fn j) (u : j′ ≤ fn n) → Pres n (fn n) refl j j′ e′ u
      → Pres (suc n) (fn (suc n)) refl j j′ e′ (stepP mode u)
downJ ic n j .(fn j) refl u child o r B t₀ gb β hβ m = DLF ic u child o r t₀ B gb β hβ m
downJ uc n j .(fn j) refl u child o r B t₀ gb β hβ m = DLF uc u child o r t₀ B gb β hβ m

all : ∀ N ℓ (e : ℓ ≡ fn N) j j′ (e′ : j′ ≡ fn j) v → Pres N ℓ e j j′ e′ v
all N ℓ e j .ℓ e′ self = selfPJ N ℓ e j e′
all zero (nd s h) () j j′ e′ v
all (suc N) (nd sL h) () j j′ e′ v
all (suc N) (nd (sΩ k) h) () j j′ e′ v
all (suc N) _ refl j j′ e′ (inc tt u) = downJ ic N j j′ e′ u (all N _ refl j j′ e′ u)
all (suc N) _ refl j j′ e′ (inu vs) = downJ uc N j j′ e′ (vs tt) (all N _ refl j j′ e′ (vs tt))
```
