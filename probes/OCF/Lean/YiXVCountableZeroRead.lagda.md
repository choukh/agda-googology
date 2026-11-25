# YiXVCountableZeroRead
> 验收文件。档位：编译定理。显式 Strong 公共上界内，辅助比较给原 ψ⁰ 的值上界。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableZeroRead where
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼)
open import OCF.Lean.YiXVLvlSteps using (Strong)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVZeroRead as Z
import OCF.Lean.YiXVCountableFoldInput as Q
import OCF.Lean.YiXVCountableFold as F
import OCF.Lean.YiXVCountableGroundValue as G
mono : ∀ {κ a} → Strong κ → Strong a → (p : L.zero L.<ᴵ a) (σ : L.Simᴵ κ a) →
  ∀ {X Y} → A.Le X Y → L.ψ⁰ X ≼ L.ψ⁰ Y
mono {κ} sκ sa p σ {X} {Y} t = ≼-trans (≅→≼ (L.≅-sym (Z.same p σ X)))
  (≼-trans (G.value (Q.Ops.mono (F.ops κ sκ) sa sa p p σ σ t)) (≅→≼ (Z.same p σ Y)))
actual : L.ψ⁰ (L.suc (L.zero {ℓ = L.ωᴵ})) ≼ L.ψ⁰ (L.Ω L.ωᴵ)
actual = mono F.ω-strong F.ω-strong (L.suc (L.lim 1 L.zero)) (λ q → L.suc q) A.omega-pos
```
