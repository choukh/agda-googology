# YiXVCountableGroundValue
> 验收文件。档位：编译定理。零层辅助比较与值序互相推出；零层每棵原树都有辅助合法性。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableGroundValue where
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼-refl; ≼-trans; ≼-suc; ≅→≼)
import OCF.Lean.YiXVCountableBase as A
module Z = A.Layer L.zero A.Gd< A.Le<
good : ∀ (X : L.Ordᶜ L.zero) → A.Gd X
good L.zero = Z.gz
good (L.suc X) = Z.gs (good X)
good (L.lim f) = Z.gl (λ n → good (f n))
good (L.limᵢ () f)
good (L.up () X)
mutual
  value : ∀ {X Y : L.Ordᶜ L.zero} → A.Le X Y → X ≼ Y
  value (Z.pack gx gy p) = step p
  step : ∀ {X Y : L.Ordᶜ L.zero} → Z.Step X Y → X ≼ Y
  step (Z.ce e) = ≅→≼ e
  step Z.rr = ≼-refl _
  step Z.zz = z≼
  step (Z.ss p) = s≼s (value p)
  step (Z.ws p) = ≼-suc (value p)
  step (Z.ll h) = l≼ (λ n → value (h n))
  step (Z.lr n p) = ≼l n (value p)
  step (Z.nn {q = ()} h)
  step (Z.aa {q = ()} p)
  step (Z.uu () p)
  step (Z.uS () h)
  step (Z.uS⁻ () h)
  step (Z.uZ ())
  step (Z.uZ⁻ ())
  step (Z.uL () h)
  step (Z.uL⁻ () h)
  step (Z.uN () q h)
  step (Z.uN⁻ () q h)
  step (Z.tr p q) = ≼-trans (value p) (value q)
native : ∀ {X Y : L.Ordᶜ L.zero} → X ≼ Y → A.Le X Y
native {Y = Y} z≼ = A.Basics.z≤ L.zero (good Y)
native (s≼s p) = A.Basics.s≤ L.zero (native p)
native {X} {L.lim f} (≼l n p) = Z.pack (good X) (good (L.lim f)) (Z.lr n (native p))
native {L.lim f} {Y} (l≼ h) = Z.pack (good (L.lim f)) (good Y) (Z.ll (λ n → native (h n)))
native (≼i {p = ()} X ex p)
native (i≼ {p = ()} h)
native (≼u {r = ()} p)
native (u≼ {r = ()} p)
actual : L.suc (L.zero {ℓ = L.zero}) ≼ L.suc L.zero
actual = value A.ground-pos
```
