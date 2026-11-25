# YiXVCountableNormalize
> 验收文件。档位：编译定理。辅助提升在结构同值下保持后继、自然极限与有下标极限的展开。
> 推广 YiXVFiniteFamily/Level 的结构递归；共享映射证明供搬运与加法复用。未证明可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableNormalize where
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)
import OCF.Align.Level as L
import OCF.Align.Uniform as U
open import OCF.Lean.YiXVCountableBase using (Up; raise)

up-left : ∀ {i κ ℓ} (r : i L.◃₁ κ) {X : L.Ordᶜ i} {Y : L.Ordᶜ ℓ} → X L.≅ Y → Up r X L.≅ Y
up-left r e = L.upˡ (L.≅→R (L.◃₁→◃ r) e)
up-right : ∀ {i κ ℓ} (r : i L.◃₁ κ) {X : L.Ordᶜ ℓ} {Y : L.Ordᶜ i} → X L.≅ Y → X L.≅ Up r Y
up-right r {X} {Y} e = L.upʳ (subst (λ Z → X L.≅ Z) (sym (L.out-into (L.◃₁→◃ r) Y)) e)
suc : ∀ {i κ} (r : i L.◃₁ κ) {X : L.Ordᶜ i} → X L.≅ X → L.suc (Up r X) L.≅ Up r (L.suc X)
suc r ex = up-right r (L.s≅ (up-left r ex))
lim : ∀ {i κ} (r : i L.◃₁ κ) (f : _ → L.Ordᶜ i) → (∀ n → f n L.≅ f n) →
  Up r (L.lim f) L.≅ L.lim (λ n → Up r (f n))
lim r f ex = up-left r (L.l≅ (λ n → up-right r (ex n)))
node : ∀ {i j κ} (r : i L.◃₁ κ) (q : j L.<ᴵ i) (f : L.U j (L.<→◃ q) → L.Ordᶜ i) →
  L.limᵢ q f L.≅ L.limᵢ q f →
  Up r (L.limᵢ q f) L.≅ L.limᵢ (raise r q) (λ u → Up r (f (L.coe (L.<→◃ (raise r q)) (L.<→◃ q) u)))
node r q f ex = up-left r (L.lᵢ≅ (L.≅ᴵ-refl _) (λ X Y h → up-right r
  (subst (λ u → f (L.into (L.<→◃ q) X) L.≅ f u)
    (sym (cong (L.into (L.<→◃ q)) (L.out-into (L.<→◃ (raise r q)) Y)))
    (U.i-resp ex (L.R→≅ (L.<→◃ q) h)))))

actual : Up L.zero (L.Ω (L.suc L.zero)) L.≅
  L.limᵢ (L.suc L.zero) (λ u → Up L.zero (L.up L.zero u))
actual = node L.zero L.zero (L.up L.zero) (L.Ω-≅ (L.s≅ L.z≅))
```
