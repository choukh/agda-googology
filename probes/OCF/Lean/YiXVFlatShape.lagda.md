# YiXVFlatShape
> 验收文件。档位：编译定理。保留式折叠的原节点计算形状，保留原 tr⁻ 与点态回搬等式。
> 复用 Level、CountableFold/MapCompare 与 ReadOmega 的构造，完整实例见代码；未接实际源世界或原外层 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFlatShape where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableMapInput as V
import OCF.Lean.YiXVCountableRetain as R
open import OCF.Lean.YiXVRefLift using (embedded)
open import OCF.Lean.YiXVFlatInput using (flat)
reraw : ∀ {κ ν i} {q : i L.<ᴵ κ} (p : V.Pull {κ} {ν} q)
  (raw : L.U (V.Pull.index p) (L.<→◃ (V.Pull.bound p)) → L.U i (L.<→◃ q)) →
  (∀ X → raw (L.into (L.<→◃ (V.Pull.bound p)) X) ≡ L.into (L.<→◃ q) (V.Pull.back p X)) → V.Pull {κ} {ν} q
reraw p raw inp = record
  { index = V.Pull.index p ; bound = V.Pull.bound p ; same = V.Pull.same p
  ; raw = raw ; back = V.Pull.back p ; input = inp
  ; good = V.Pull.good p ; mono = V.Pull.mono p ; floor = V.Pull.floor p
  ; suc = V.Pull.suc p ; transparent = V.Pull.transparent p }
left : ∀ {κ a b i} (q : i L.<ᴵ κ) (ρ : L.Simᴵ a b) (ξ : L.Simᴵ κ a) → V.Pull {κ} {b} q
left {i = i} q ρ ξ = reraw (R.pull q (ρ (ξ q)) (L.≅ᴵ-refl i) refl)
  (λ u → L.into (L.<→◃ q) (L.tr⁻ (L.≅ᴵ-refl i)
    (L.out (L.<→◃ (ξ q)) (L.coe (L.<→◃ (ρ (ξ q))) (L.<→◃ (ξ q)) u))))
  (λ X → cong (λ Y → L.into (L.<→◃ q) (L.tr⁻ (L.≅ᴵ-refl i) Y))
    (trans (L.out-into (L.<→◃ (ξ q)) (L.out (L.<→◃ (ρ (ξ q))) (L.into (L.<→◃ (ρ (ξ q))) X)))
      (L.out-into (L.<→◃ (ρ (ξ q))) X)))
right : ∀ {κ b i} (q : i L.<ᴵ κ) (ζ : L.Simᴵ κ b) → V.Pull {κ} {b} q
right {i = i} q ζ = R.pull q (ζ q) (L.≅ᴵ-refl i) refl
node-left : ∀ {κ a b i} (q : i L.<ᴵ κ) (ρ : L.Simᴵ a b) (ξ : L.Simᴵ κ a)
  (f : L.U i (L.<→◃ q) → L.Ordᶜ κ) →
  embedded ρ (flat a ξ (L.limᵢ q f)) ≡
    L.limᵢ (V.Pull.bound (left q ρ ξ)) (λ u → embedded ρ (flat a ξ (f (V.Pull.raw (left q ρ ξ) u))))
node-left q ρ ξ f = refl
node-right : ∀ {κ b i} (q : i L.<ᴵ κ) (ζ : L.Simᴵ κ b)
  (f : L.U i (L.<→◃ q) → L.Ordᶜ κ) →
  flat b ζ (L.limᵢ q f) ≡ L.limᵢ (V.Pull.bound (right q ζ)) (λ u → flat b ζ (f (V.Pull.raw (right q ζ) u)))
node-right q ζ f = refl
actual : embedded (λ q → L.suc q) (flat (L.suc L.zero) (λ q → q) (L.Ω (L.suc L.zero))) ≡
  L.limᵢ (L.suc L.zero) (λ u → embedded (λ q → L.suc q)
    (flat (L.suc L.zero) (λ q → q) (L.up L.zero (L.tr⁻ L.z≅ u))))
actual = refl
```
