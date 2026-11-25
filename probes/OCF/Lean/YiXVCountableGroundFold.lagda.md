# YiXVCountableGroundFold
> 验收文件。档位：编译定理。原零层折叠的完整接口实例，先于一般阶段构造实填。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableGroundFold where
open import Data.Product using (proj₁)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as O
import OCF.Lean.YiXVCountableIter as I
import OCF.Lean.YiXVCountableFloor as F
import OCF.Lean.YiXVCountableFoldInput as Q
open import OCF.Lean.YiXVLvlSteps using (Strong)
module Z = A.Layer L.zero A.Gd< A.Le<

good : ∀ {ν a} (p : ν L.<ᴵ a) (σ : L.Simᴵ L.zero a) (X : L.Ordᶜ L.zero) → A.Gd (L.ψ p σ X)
good {ν} p σ L.zero = proj₁ (O.model ν)
good p σ (L.suc X) = A.Layer.gl (I.good (L.ψ p σ X) (good p σ X))
good p σ (L.lim f) = A.Layer.gl (λ n → good p σ (f n))
good p σ (L.limᵢ () f)
good p σ (L.up () X)

module M (ν : L.Ordᴵ) where
  module D = A.Layer ν A.Gd< A.Le<
  proof : ∀ {X Y} → D.Le X Y → D.Step X Y
  proof (D.pack gx gy q) = q
  mutual
    mono : ∀ {a b} (p : ν L.<ᴵ a) (p′ : ν L.<ᴵ b)
      (σ : L.Simᴵ L.zero a) (τ : L.Simᴵ L.zero b) {X Y} →
      A.Le X Y → A.Le (L.ψ p σ X) (L.ψ p′ τ Y)
    mono p p′ σ τ (Z.pack gx gy q) = D.pack (good p σ _) (good p′ τ _) (step p p′ σ τ gx gy q)
    step : ∀ {a b} (p : ν L.<ᴵ a) (p′ : ν L.<ᴵ b)
      (σ : L.Simᴵ L.zero a) (τ : L.Simᴵ L.zero b) {X Y} →
      Z.Gd X → Z.Gd Y → Z.Step X Y → D.Step (L.ψ p σ X) (L.ψ p′ τ Y)
    step p p′ σ τ gx gy (Z.ce e) = D.ce (L.ψ-≅ (L.≅ᴵ-refl ν) e)
    step p p′ σ τ gx gy Z.rr = D.ce (L.ψ-≅ (L.≅ᴵ-refl ν) (A.self gx))
    step p p′ σ τ {Y = Y} gx gy Z.zz = proof (F.floor p′ τ Y (good p′ τ Y))
    step p p′ σ τ gx gy (Z.ss q) = proof (I.lim-mono (mono p p′ σ τ q))
    step p p′ σ τ gx gy (Z.ws q) = D.lr 1 (mono p p′ σ τ q)
    step p p′ σ τ gx gy (Z.ll h) = D.ll (λ n → mono p p′ σ τ (h n))
    step p p′ σ τ gx gy (Z.lr n q) = D.lr n (mono p p′ σ τ q)
    step p p′ σ τ gx gy (Z.nn {q = ()} h)
    step p p′ σ τ gx gy (Z.aa {q = ()} q)
    step p p′ σ τ gx gy (Z.uu () q)
    step p p′ σ τ gx gy (Z.uS () h)
    step p p′ σ τ gx gy (Z.uS⁻ () h)
    step p p′ σ τ gx gy (Z.uZ ())
    step p p′ σ τ gx gy (Z.uZ⁻ ())
    step p p′ σ τ gx gy (Z.uL () h)
    step p p′ σ τ gx gy (Z.uL⁻ () h)
    step p p′ σ τ gx gy (Z.uN () q h)
    step p p′ σ τ gx gy (Z.uN⁻ () q h)
    step p p′ σ τ gx gy (Z.tr q r) = D.tr (mono p p′ σ τ q) (mono p′ p′ τ τ r)

ops : Q.Ops L.zero
Q.Ops.good ops sa p σ {X} gx = good p σ X
Q.Ops.mono ops sa sb p p′ σ τ = M.mono _ p p′ σ τ

actual : A.Gd (L.ψ (L.zero {a = L.ωᴵ}) (λ ()) (L.suc (L.zero {ℓ = L.zero})))
actual = good L.zero (λ ()) (L.suc L.zero)
```
