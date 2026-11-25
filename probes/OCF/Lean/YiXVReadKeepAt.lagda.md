# YiXVReadKeepAt
> 验收文件。档位：编译定理。指定有字面界的保留节点合法，并在辅助比较中不大于原折叠输出。
> 从 YiXVSourceAffine*、ReadFamily 与原 Level 推广，参照侧重用 CountableFold/Retain；未交完整世界 up/node 输出、外层 n≥2 界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadKeepAt where
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; subst₂)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
import OCF.Align.Level as L
import OCF.Align.Uniform as Uniform
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableLevels as Levels
import OCF.Lean.YiXVCountableFold as F
import OCF.Lean.YiXVCountableFoldStage as Stage
import OCF.Lean.YiXVCountableFoldNodeGood as Node
open import OCF.Lean.YiXVLvlSteps using (Strong)
import OCF.Lean.YiXVLiteralTri as Tri
import OCF.Lean.YiXVReadKeepAtModels as Model

module At {κ ν a i} (sκ : Strong κ) (sa : Strong a)
  (p : ν L.<ᴵ a) (σ : L.Simᴵ κ a) (q : i L.<ᴵ κ)
  (f : L.U i (L.<→◃ q) → L.Ordᶜ κ) where
  module S = Stage.Stage κ sκ (λ {j} r → F.ops j (Levels.child sκ r))
  act : ∀ {j} (r : j L.<ᴵ ν) → i L.≅ᴵ j → L.U j (L.<→◃ r) → L.Ordᶜ ν
  act r e u = L.ψ p σ (f (L.into (L.<→◃ q) (L.tr⁻ e (L.out (L.<→◃ r) u))))
  between : ∀ {j j′} (r : j L.<ᴵ ν) (e : i L.≅ᴵ j) (r′ : j′ L.<ᴵ ν) (e′ : i L.≅ᴵ j′) →
    L.limᵢ q f L.≅ L.limᵢ q f → L.limᵢ r (act r e) L.≅ L.limᵢ r′ (act r′ e′)
  between r e r′ e′ ex = L.lᵢ≅ (L.≅ᴵ-trans (L.≅ᴵ-sym e) e′) λ X Y d →
    subst₂ (λ U V → L.ψ p σ (f (L.into (L.<→◃ q) (L.tr⁻ e U)))
      L.≅ L.ψ p σ (f (L.into (L.<→◃ q) (L.tr⁻ e′ V))))
      (sym (L.out-into (L.<→◃ r) X)) (sym (L.out-into (L.<→◃ r′) Y))
      (L.ψ-≅ (L.≅ᴵ-refl ν) (Uniform.i-resp ex (L.≅-trans
        (L.tr⁻-≅ e (L.R→≅ (L.<→◃ r) d))
        (L.≅-sym (L.tr⁻-≅ e′ (L.≅-trans (L.≅-sym (L.R→≅ (L.<→◃ r) d))
          (L.R→≅ (L.<→◃ r) d)))))))
  good : ∀ {j} (r : j L.<ᴵ ν) (e : i L.≅ᴵ j) → i ≡ j →
    A.Gd (L.limᵢ q f) → A.Gd (L.limᵢ r (act r e))
  good r e same (A.Layer.gn ex law gb) =
    Node.Node.Keep.result sκ q f ex (S.body q f law gb) sa p σ r e same (between r e r e ex)
  against : ∀ {j} (r : j L.<ᴵ ν) (e : i L.≅ᴵ j) → i ≡ j → A.Gd (L.limᵢ q f) →
    L.limᵢ r (act r e) L.≅ L.ψ p σ (L.limᵢ q f)
  against r e same gx with L.<ᴵ-dec (σ q) p in eq | Tri.tri sa (σ q) p
  ... | injᵃ (L.via e′ r′) | same′ = between r e r′ e′ (A.self gx)
  ... | injᵇ back | same′ = ⊥-elim (L.clash₁ (L.≅ᴵ-refl i) (L.≅ᴵ-refl ν)
    (L.via (L.≅ᴵ-refl i) (subst (λ j → j L.<ᴵ ν) (sym same) r)) back)
  ... | injᶜ eqi | same′ = ⊥-elim (L.clash₂ (L.≅ᴵ-refl i) (L.≅ᴵ-refl ν)
    (L.via (L.≅ᴵ-refl i) (subst (λ j → j L.<ᴵ ν) (sym same) r)) eqi)
  bound : ∀ {j} (r : j L.<ᴵ ν) (e : i L.≅ᴵ j) → i ≡ j → A.Gd (L.limᵢ q f) →
    A.Le (L.limᵢ r (act r e)) (L.ψ p σ (L.limᵢ q f))
  bound r e same gx = A.Layer.pack (good r e same gx)
    (S.good sa p σ gx) (A.Layer.ce (against r e same gx))

module Actual = At F.ω-strong F.ω-strong (L.zero {a = L.ωᴵ}) (λ q → L.suc q) Model.q Model.f
actual : A.Le (L.limᵢ Model.r (Actual.act Model.r L.z≅))
  (L.ψ (L.zero {a = L.ωᴵ}) (λ q → L.suc q) (L.limᵢ Model.q Model.f))
actual = Actual.bound Model.r L.z≅ refl Model.actual
```
