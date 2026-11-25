# YiXV：下一实际前缀的更新底
> 验收文件。编译定理：pre 2 的层号 3 展开、底 b⊥ B3 = pre 1，以及其第 2、1 层种子的原折叠展开。
> β₂ 展开为 Upc₂(Ω₂,Ω₁)；这些是形状定理，不是 pre 2 的值上界。
> B3、B31 均直接取自原 pre 列，供 YiXVSlotSrc 的实际非零目标实例使用。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVThird where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiXVStart using (fg; e1; r1; pre; B2)

B3 : Base (suc (suc (suc zero)))
B3 = dL fg e1 r1 (B₀ (lim fg)) 2 (cumΩ fg 1)

pre2-form : pre 2 ≡ ψ⊥ (suc (suc (suc zero))) tt tt B3 (Ωt (suc (suc (suc zero))))
pre2-form = refl

bottom3-form : b⊥ B3 ≡ pre 1
bottom3-form = refl

γ₂ : Tr (suc (suc zero))
γ₂ = bs B3 (suc (suc zero)) (ins self)

B31 : Base (suc (suc (suc zero)))
B31 = dL fg e1 r1 (B₀ (lim fg)) 2 (cumΩ fg 0)

β₂ : Tr (suc (suc zero))
β₂ = ψs (lim fg) e1 r1 (B₀ (lim fg)) (suc (suc zero)) (inl 2 (ins self))
  (Ωt (suc (suc zero))) (Ωt-nz (suc (suc zero))) (cumΩ fg 0)

nβ₂ : suc (suc zero) ⊢ zero ◃ β₂
nβ₂ = nzs (lim fg) e1 r1 (B₀ (lim fg)) (suc (suc zero)) (inl 2 (ins self))
  (Ωt (suc (suc zero))) (Ωt-nz (suc (suc zero))) (cumΩ fg 0)

seed2-form : γ₂ ≡ ψs (suc (suc zero)) tt tt
  (dS (suc (suc zero)) tt tt B31 zero) (suc (suc zero)) self β₂ nβ₂ (Ωt (suc (suc zero)))
seed2-form = refl

β₂-form : β₂ ≡ Upc (suc (suc zero)) tt (Ωt (suc (suc zero)))
  (Ωt-nz (suc (suc zero))) (Ωt (suc zero))
β₂-form = refl

η₁ : Tr (suc zero)
η₁ = bs B3 (suc zero) (ins (ins self))

η₁-form : η₁ ≡ ψs (suc (suc zero)) tt tt
  (dS (suc (suc zero)) tt tt B31 zero) (suc zero) (ins self)
  (bs B2 (suc zero) (ins self))
  (ns B2 (suc zero) (ins self)) (Ωt (suc (suc zero)))
η₁-form = refl
```
