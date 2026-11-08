# 实际γ₁到双重完成高度的旧包含失败

验收专用。针对当前NextValueActual的原height，不更换候选。
标准ω是原γ₁的一个旧前驱，但该height的遗传第2项界排除这个前驱。
只否定旧前驱包含这条输入桥，不否定ψΩ的序数值覆盖。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedNegOmegaCompletionActual where
open import Data.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num; omega)
open import OCF.Lean.GeneralOmegaCountableTypedNegOmegaCompletion
open import OCF.Lean.GeneralOmegaCountableRegularIf using (Reg)
open import OCF.Lean.GeneralOmegaCountableRegularClosure using (reg-same)
open import OCF.Lean.GeneralOmegaCountableRegularRun using (regular-stage)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; same-sym)
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.NoCumsum as N
open import OCF.Align.GeneralOmegaCountableNextValueActual using (height; reference-stage-shape)

reflect-read : ∀ {a b : Cd} → B.read a L.≅ B.read b → Same a b
reflect-read {a = hz} {b = hz} L.z≅ = zz
reflect-read {a = hs a} {b = hs b} (L.s≅ p) = ss (reflect-read p)
reflect-read {a = hl f} {b = hl g} (L.l≅ p) = ll (λ n → reflect-read (p n))

no-omega-predecessor : ∀ {a : Cd} → SecondThree a → B.read omega L.≺ B.read a → ⊥
no-omega-predecessor {a = hs a} good (L.≺z e) = no-omega-shape good (reflect-read e)
no-omega-predecessor {a = hs a} good (L.≺s p) = no-omega-predecessor good p
no-omega-predecessor {a = hl f} good (L.≺l n p) = no-omega-predecessor (proj₂ good n) p

completed-input-regular : Reg (leg (B.forget (N.γ 1)))
completed-input-regular = reg-same (same-sym reference-stage-shape) (regular-stage 1)
height-three : SecondThree height
height-three = completed-three completed-input-regular
no-omega-in-height : B.read omega L.≺ B.read height → ⊥
no-omega-in-height = no-omega-predecessor height-three

-- 原ψ⁰(1)的逐项1倍迭代就是标准ω，证明仅在可数层。
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.GeneralOmegaFiniteTypedObserveRun using (read-add)
one-old : L.Ordᶜ L.zero
one-old = L.suc L.zero
iter-one : ∀ n → iter (one-old L.+_) L.zero n L.≅ B.read (num n)
iter-one zero = L.z≅
iter-one (suc n) = L.≅-trans (L.add-≅ (L.s≅ L.z≅) (iter-one n))
  (L.≅-trans (L.≅-sym (read-add (hs hz) (num n))) (plus-one n))
  where
  plus-one : ∀ n → B.read (hs hz ⊞ num n) L.≅ B.read (num (suc n))
  plus-one zero = L.s≅ L.z≅
  plus-one (suc n) = L.s≅ (plus-one n)
omega-shape : B.read omega L.≅ L.ψ⁰ one-old
omega-shape = L.≅-sym (L.l≅ iter-one)

omega-in-gamma : B.read omega L.≺ N.γ 1
omega-in-gamma = L.≺l 1 (L.≺l 2 (L.≺l 2 (L.≺l 1 (L.≺z omega-shape))))
no-actual-input-inclusion : N.γ 1 L.⊑⁰ B.read height → ⊥
no-actual-input-inclusion p = no-omega-in-height (p omega-in-gamma)

height-legal : LgB height
height-legal = Lg-leg (leg (B.forget (N.γ 1)))
```

反例不是任取正则输入：height逐字是原NextValueActual的双重完成。
原输入证书、完整stage1同形桥与Γ生成正则性共同提供所需前提。
未证明γ₂到辅助输出的值界为假，也没有否定原全ψ观察接口。
