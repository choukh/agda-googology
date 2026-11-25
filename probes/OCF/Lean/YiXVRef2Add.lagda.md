# YiXV：第 2 层比较的加法接口
> 验收文件。编译定理：≤₂ 对同层加法、固定低层尾部及尾部结合保持，Ω₂+Ω₂ 的实例已填。
> 尾部比较分别用目标层 1 的受限比较与目标层 0 的值序；各项共用字面层 2。
> 按 YiOverOps 的加法证明扩展；供 YiXVAffRef 与 YiXVAffine 的更新底行使用。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVRef2Add where
open import Data.Nat using (zero; suc)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
open import OCF.Lean.YiXVRef2 using (T₂; _≤₂_; z₂; s₂; w₂; l₂; r₂; n₀; n₁; a₀; a₁; u₁; Ω₂; Ω₂-refl)

σ₁ : L.Simᴵ (L.suc L.zero) (L.suc (L.suc L.zero))
σ₁ q = L.suc q
σ₀ : L.Simᴵ L.zero (L.suc (L.suc L.zero))
σ₀ q = L.suc (L.suc q)

mutual
  right₀ : ∀ {X X′ : T₂} → X ≤₂ X′ → (Y : R.T₀) → X ≤₂ L.add X′ σ₀ Y
  right₀ q L.zero = q
  right₀ q (L.suc Y) = w₂ (right₀ q Y)
  right₀ q (L.lim f) = r₂ 0 (right₀ q (f 0))
  right₀ q (L.limᵢ () f)
  right₀ q (L.up () y)

  right₁ : ∀ {X X′ : T₂} → X ≤₂ X′ → (Y : R.T₁) → X ≤₂ L.add X′ σ₁ Y
  right₁ q L.zero = q
  right₁ q (L.suc Y) = w₂ (right₁ q Y)
  right₁ q (L.lim f) = r₂ 0 (right₁ q (f 0))
  right₁ q (L.limᵢ L.zero f) = a₀ (right₁ q (f R.𝟙))
  right₁ q (L.limᵢ (L.suc ()) f)
  right₁ q (L.up L.zero y) = right₀ q y

  right₂ : ∀ {X X′ : T₂} → X ≤₂ X′ → (Y : T₂) → X ≤₂ (X′ L.+ Y)
  right₂ q L.zero = q
  right₂ q (L.suc Y) = w₂ (right₂ q Y)
  right₂ q (L.lim f) = r₂ 0 (right₂ q (f 0))
  right₂ q (L.limᵢ L.zero f) = a₁ (right₂ q (f O.Ω₁))
  right₂ q (L.limᵢ (L.suc L.zero) f) = a₀ (right₂ q (f R.𝟙))
  right₂ q (L.up L.zero y) = right₁ q y

mutual
  ground : ∀ {X X′ : T₂} {Y Y′ : R.T₀} → X ≤₂ X′ → Y ≼ Y′ → L.add X σ₀ Y ≤₂ L.add X′ σ₀ Y′
  ground q z≼ = right₀ q _
  ground q (s≼s p) = s₂ (ground q p)
  ground q (≼l n p) = r₂ n (ground q p)
  ground q (l≼ h) = l₂ (λ n → ground q (h n))
  ground q (≼i {p = ()} x ex p)
  ground q (i≼ {p = ()} h)
  ground q (≼u {r = ()} p)
  ground q (u≼ {r = ()} p)

  flat : ∀ {X X′ : T₂} {Y : R.T₁} {y : R.T₀} → X ≤₂ X′ → R.Flat Y → Y ≼ y →
    L.add X σ₁ Y ≤₂ L.add X′ σ₀ y
  flat q fy z≼ = right₀ q _
  flat q (R.fs fy) (s≼s p) = s₂ (flat q fy p)
  flat q fy (≼l n p) = r₂ n (flat q fy p)
  flat q (R.fl fy) (l≼ h) = l₂ (λ n → flat q (fy n) (h n))
  flat q fy (≼i {p = ()} x ex p)
  flat q () (i≼ h)
  flat q fy (≼u {r = ()} p)
  flat q R.fu (u≼ p) = ground q p

  tail : ∀ {X X′ : T₂} {Y Y′ : R.T₁} → X ≤₂ X′ → Y R.≤ₚ Y′ → L.add X σ₁ Y ≤₂ L.add X′ σ₁ Y′
  tail q R.zz = q
  tail q (R.ss p) = s₂ (tail q p)
  tail q (R.ws p) = w₂ (tail q p)
  tail q (R.≤l n p) = r₂ n (tail q p)
  tail q (R.l≤ h) = l₂ (λ n → tail q (h n))
  tail q (R.ii h) = n₀ (λ x y o p → tail q (h x y o p))
  tail q (R.i1 p) = a₀ (tail q p)
  tail q (R.fu fy p) = flat q fy p

  plus : ∀ {X X′ Y Y′ : T₂} → X ≤₂ X′ → Y ≤₂ Y′ → (X L.+ Y) ≤₂ (X′ L.+ Y′)
  plus q z₂ = right₂ q _
  plus q (s₂ p) = s₂ (plus q p)
  plus q (w₂ p) = w₂ (plus q p)
  plus q (l₂ h) = l₂ (λ n → plus q (h n))
  plus q (r₂ n p) = r₂ n (plus q p)
  plus q (n₀ h) = n₀ (λ x y o p → plus q (h x y o p))
  plus q (n₁ h) = n₁ (λ x y o p → plus q (h x y o p))
  plus q (a₀ p) = a₀ (plus q p)
  plus q (a₁ p) = a₁ (plus q p)
  plus q (u₁ p) = tail q p

sample : (Ω₂ L.+ Ω₂) ≤₂ (Ω₂ L.+ Ω₂)
sample = plus Ω₂-refl Ω₂-refl
assoc-tail : (X : T₂) → X ≤₂ X → (Y : R.T₁) → O.Gd Y →
  (σ : L.Simᴵ L.zero (L.suc L.zero)) → (z : R.T₀) →
  L.add (L.add X σ₁ Y) σ₀ z ≤₂ L.add X σ₁ (L.add Y σ z)
assoc-tail X rx Y gd σ L.zero = tail rx (O.reflₚ gd)
assoc-tail X rx Y gd σ (L.suc z) = s₂ (assoc-tail X rx Y gd σ z)
assoc-tail X rx Y gd σ (L.lim f) = l₂ (λ n → r₂ n (assoc-tail X rx Y gd σ (f n)))
assoc-tail X rx Y gd σ (L.limᵢ () f)
assoc-tail X rx Y gd σ (L.up () y)
```
