# YiXVNeutral
> 验收文件。档位：编译定理。与零结构同值的前缀在任意 Sim 加法下可消去，按原 PER 证据递归。
> 复用 Level、CountableFold/MapCompare 与 ReadOmega 的构造，完整实例见代码；未接实际源世界或原外层 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVNeutral where
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)
import OCF.Align.Level as L
neutral : ∀ {κ ν δ} {a : L.Ordᶜ ν} {σ : L.Simᴵ κ ν} {X : L.Ordᶜ κ} {Y : L.Ordᶜ δ} →
  a L.≅ L.zero {ℓ = ν} → X L.≅ Y → L.add a σ X L.≅ Y
neutral ea L.z≅ = L.≅-trans ea L.z≅
neutral ea (L.s≅ h) = L.s≅ (neutral ea h)
neutral ea (L.l≅ h) = L.l≅ (λ n → neutral ea (h n))
neutral {a = a} {σ = σ} ea (L.lᵢ≅ {p = q} {q = r} {f = f} {g = g} e h) = L.lᵢ≅ e
  (λ X Y d → subst (λ u → L.add a σ (f u) L.≅ g (L.into (L.<→◃ r) Y))
    (sym (cong (L.into (L.<→◃ q)) (L.out-into (L.<→◃ (σ q)) X)))
    (neutral ea (h X Y (L.R-conv (L.<→◃ (σ q)) (L.<→◃ q) d))))
neutral {σ = σ} ea (L.upˡ {r = L.zero} h) = neutral {σ = λ q → σ (L.suc q)} ea h
neutral {σ = σ} ea (L.upˡ {r = L.self n} h) = neutral {σ = λ q → σ (L.lim n q)} ea h
neutral ea (L.upʳ h) = L.upʳ (neutral ea h)
actual : L.add L.zero (λ q → q) (L.Ω (L.suc L.zero)) L.≅ L.Ω (L.suc L.zero)
actual = neutral L.z≅ (L.Ω-≅ (L.s≅ L.z≅))
```
