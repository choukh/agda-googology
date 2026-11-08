# 正则公共界把值方向还原成实际位置

这是配对检验得到的正面域校准，不是否定。合法公共界先给位置比较，
正则性排除值方向相反的非平凡位置。因此不能拿任意两个同值正则
极限当作共享接口的输入，而忽略它们是否真的处于同一合法界内。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableRegularNegOrder where
open import Data.Nat using (suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; s≤s; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans; ≤-refl)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Lean.GeneralOmegaCountableRegularIf using (Reg; reg-zero; reg-one)
open import OCF.Lean.GeneralOmegaCountableObservePrefix using (position-value)

-- 相等分支保留字面树相等；严格分支并非声称所有位置都严格。
position-strict : ∀ {a b : Cd} → Reg b → a ⊲ b → (a ≡ b) ⊎ (hs a ≤ᵛ b)
position-strict r hself = inj₁ refl
position-strict r (hsuc p) = inj₂ (s≤s (position-value p))
position-strict (step , sub) (hlim n p) = inj₂
  (≤l (suc n) (≤-trans (s≤s (position-value p)) (step n)))
position-strict r (hLim {κ = ()} e p)

orient : ∀ {a b : Cd} → Reg a → a ≤ᵛ b → b ⊲ a → a ⊲ b
orient {a} {b} ra v p with position-strict ra p
... | inj₁ e = subst (λ x → a ⊲ x) (sym e) hself
... | inj₂ strict = ⊥-elim (¬s≤ᵛ b (≤-trans strict v))

value-to-position : ∀ {B a b : Cd} → LgB B → Reg a → Reg b →
  a ⊲ B → b ⊲ B → a ≤ᵛ b → a ⊲ b
value-to-position lB ra rb pa pb v with cmpB pa pb tt lB
... | inj₁ p = orient ra v p
... | inj₂ p = p

-- 真实非零合法共同界，兼容共享RestrictedValueMonotone的所有输入前提。
zero-to-one : hz ⊲ hs hz
zero-to-one = value-to-position tt reg-zero reg-one (hsuc hself) hself
  (OCF.Lean.Fold1If.z≤)
```

value-to-position没有选择或判定裸序数值；值界由调用者提供，cmpB
只比较同一个原合法B内的两条路径。结论仍是原位置，并未把它穿过Γ。
若要实现受限值单调，仍须证明Γ在这里的正则位置域上保持值方向。
