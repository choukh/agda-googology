# YiXVCountableFoldStage
> 验收文件。档位：编译定理。固定源层，低层接口与源证书递归给一般折叠阶段。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableFoldStage where
open import Data.Product using (proj₁)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as O
import OCF.Lean.YiXVCountableNormalize as N
open import OCF.Lean.YiXVLvlSteps using (Strong)
import OCF.Lean.YiXVCountableLevels as Levels
import OCF.Lean.YiXVCountableFoldInput as Q
import OCF.Lean.YiXVCountableFoldBody as H
import OCF.Lean.YiXVCountableFoldCross as C
import OCF.Lean.YiXVCountableFoldBound as B
import OCF.Lean.YiXVCountableFoldNodeGood as NG
import OCF.Lean.YiXVCountableFoldNodeMono as NM
import OCF.Lean.YiXVCountableFoldNodeAA as NA
import OCF.Lean.YiXVCountableIter as It
import OCF.Lean.YiXVCountableFloor as Floor

module Stage (κ : L.Ordᴵ) (sκ : Strong κ) (lower : Levels.Lower κ) where
  module S = A.Layer κ A.Gd< A.Le<
  proof : ∀ {ν X Y} → A.Le {ν} X Y → A.Layer.Step ν A.Gd< A.Le< X Y
  proof (A.Layer.pack gx gy p) = p
  mutual
    good : ∀ {ν a} → Strong a → (p : ν L.<ᴵ a) (σ : L.Simᴵ κ a) → ∀ {X} → S.Gd X → A.Gd (L.ψ p σ X)
    good {ν} sa p σ S.gz = proj₁ (O.model ν)
    good sa p σ (S.gs {X} gx) = A.Layer.gl (It.good (L.ψ p σ X) (good sa p σ gx))
    good sa p σ (S.gl gf) = A.Layer.gl (λ n → good sa p σ (gf n))
    good sa p σ (S.gn {q = q} {f = f} ex law gb) = NG.Node.result sκ q f ex (body q f law gb) sa p σ
    good sa p σ (S.gu L.zero {X} gx) = Q.Ops.good (lower L.zero) sa p (λ q → σ (L.suc q)) gx
    good sa p σ (S.gu (L.self n) {X} gx) = Q.Ops.good (lower (L.self n)) sa p (λ q → σ (L.lim n q)) gx

    body : ∀ {i} (q : i L.<ᴵ κ) (f : L.U i (L.<→◃ q) → L.Ordᶜ κ) →
      S.SC q f → (∀ X → S.GU q X → S.Floor q X → S.Gd (f (L.into (L.<→◃ q) X))) → H.Body q f
    H.Body.good (body q f law gb) sa p σ X gx o = good sa p σ (gb X (A.good-in (L.<→◃ q) gx) (A.le-in (L.<→◃ q) o))
    H.Body.mono (body q f law gb) sa sb p p′ σ τ X Y gx gy o t = mono sa sb p p′ σ τ
      (S.SC.mo law X Y (A.good-in (L.<→◃ q) gx) (A.good-in (L.<→◃ q) gy) (A.le-in (L.<→◃ q) o) (A.le-in (L.<→◃ q) t))
    H.Body.step (body q f law gb) sa p σ X gx o = mono sa sa p p σ σ
      (S.SC.db law X (A.good-in (L.<→◃ q) gx) (A.le-in (L.<→◃ q) o))

    cross : ∀ {i} (q r : i L.<ᴵ κ) (f : L.U i (L.<→◃ q) → L.Ordᶜ κ) (g : L.U i (L.<→◃ r) → L.Ordᶜ κ) →
      (∀ X Y → S.GU q X → S.GU r Y → S.Floor q X → S.RU q X Y →
        S.Le (f (L.into (L.<→◃ q) X)) (g (L.into (L.<→◃ r) Y))) → C.Cross q r f g
    C.Cross.mono (cross q r f g h) sa sb p p′ σ τ X Y gx gy o t = mono sa sb p p′ σ τ
      (h X Y (A.good-in (L.<→◃ q) gx) (A.good-in (L.<→◃ r) gy) (A.le-in (L.<→◃ q) o) (A.le-in (L.<→◃ q) t))

    bound : ∀ {i} (q : i L.<ᴵ κ) X (g : L.U i (L.<→◃ q) → L.Ordᶜ κ) →
      S.Le X (g (L.into (L.<→◃ q) (L.Ω i))) → B.Bound q X g
    B.Bound.at (bound q X g h) sa sb p p′ σ τ = mono sa sb p p′ σ τ h

    mono : ∀ {ν a b} → Strong a → Strong b → (p : ν L.<ᴵ a) (p′ : ν L.<ᴵ b)
      (σ : L.Simᴵ κ a) (τ : L.Simᴵ κ b) → ∀ {X Y} → S.Le X Y → A.Le (L.ψ p σ X) (L.ψ p′ τ Y)
    mono sa sb p p′ σ τ (S.pack gx gy t) = A.Layer.pack (good sa p σ gx) (good sb p′ τ gy) (step sa sb p p′ σ τ gx gy t)

    step : ∀ {ν a b} → Strong a → Strong b → (p : ν L.<ᴵ a) (p′ : ν L.<ᴵ b)
      (σ : L.Simᴵ κ a) (τ : L.Simᴵ κ b) → ∀ {X Y} → S.Gd X → S.Gd Y → S.Step X Y →
      A.Layer.Step ν A.Gd< A.Le< (L.ψ p σ X) (L.ψ p′ τ Y)
    step {ν} sa sb p p′ σ τ gx gy (S.ce e) = A.Layer.ce (L.ψ-≅ (L.≅ᴵ-refl ν) e)
    step {ν} sa sb p p′ σ τ gx gy S.rr = A.Layer.ce (L.ψ-≅ (L.≅ᴵ-refl ν) (A.self gx))
    step sa sb p p′ σ τ {Y = Y} gx gy S.zz = proof (Floor.floor p′ τ Y (good sb p′ τ gy))
    step sa sb p p′ σ τ gx gy (S.ss t) = proof (It.lim-mono (mono sa sb p p′ σ τ t))
    step sa sb p p′ σ τ gx gy (S.ws t) = A.Layer.lr 1 (mono sa sb p p′ σ τ t)
    step sa sb p p′ σ τ gx gy (S.ll h) = A.Layer.ll (λ n → mono sa sb p p′ σ τ (h n))
    step sa sb p p′ σ τ gx gy (S.lr n t) = A.Layer.lr n (mono sa sb p p′ σ τ t)
    step sa sb p p′ σ τ (S.gn ef lf bf) (S.gn eg lg bg) (S.nn {q = q} {r = r} {f = f} {g = g} h) =
      proof (NM.Node.Run.result sκ q r f g ef eg (body q f lf bf) (body r g lg bg) (cross q r f g h) sa sb p p′ σ τ)
    step sa sb p p′ σ τ {X} gx (S.gn eg lg bg) (S.aa {q = q} {f = g} h) =
      proof (NA.Node.Run.result sκ q X g eg (body q g lg bg) (bound q X g h) sa sb p p′ σ τ (good sa p σ gx))
    step sa sb p p′ σ τ gx gy (S.uu L.zero t) =
      proof (Q.Ops.mono (lower L.zero) sa sb p p′ (λ q → σ (L.suc q)) (λ q → τ (L.suc q)) t)
    step sa sb p p′ σ τ gx gy (S.uu (L.self n) t) =
      proof (Q.Ops.mono (lower (L.self n)) sa sb p p′ (λ q → σ (L.lim n q)) (λ q → τ (L.lim n q)) t)
    step {ν} sa sb p p′ σ τ gx gy (S.uS r hx) = A.Layer.ce
      (L.ψ-≅ (L.≅ᴵ-refl ν) (N.suc r (A.self (A.good-out (L.◃₁→◃ r) hx))))
    step {ν} sa sb p p′ σ τ gx gy (S.uS⁻ r hx) = A.Layer.ce
      (L.ψ-≅ (L.≅ᴵ-refl ν) (L.≅-sym (N.suc r (A.self (A.good-out (L.◃₁→◃ r) hx)))))
    step {ν} sa sb p p′ σ τ gx gy (S.uZ r) = A.Layer.ce (L.ψ-≅ (L.≅ᴵ-refl ν) (N.up-left r L.z≅))
    step {ν} sa sb p p′ σ τ gx gy (S.uZ⁻ r) = A.Layer.ce (L.ψ-≅ (L.≅ᴵ-refl ν) (N.up-right r L.z≅))
    step {ν} sa sb p p′ σ τ gx gy (S.uL {f = f} r hf) = A.Layer.ce
      (L.ψ-≅ (L.≅ᴵ-refl ν) (N.lim r f (λ n → A.self (A.good-out (L.◃₁→◃ r) (hf n)))))
    step {ν} sa sb p p′ σ τ gx gy (S.uL⁻ {f = f} r hf) = A.Layer.ce
      (L.ψ-≅ (L.≅ᴵ-refl ν) (L.≅-sym (N.lim r f (λ n → A.self (A.good-out (L.◃₁→◃ r) (hf n))))))
    step {ν} sa sb p p′ σ τ gx gy (S.uN r q {f} hf) = A.Layer.ce
      (L.ψ-≅ (L.≅ᴵ-refl ν) (N.node r q f (A.self (A.good-out (L.◃₁→◃ r) hf))))
    step {ν} sa sb p p′ σ τ gx gy (S.uN⁻ r q {f} hf) = A.Layer.ce
      (L.ψ-≅ (L.≅ᴵ-refl ν) (L.≅-sym (N.node r q f (A.self (A.good-out (L.◃₁→◃ r) hf)))))
    step sa sb p p′ σ τ gx gy (S.tr t u) =
      A.Layer.tr (mono sa sb p p′ σ τ t) (mono sb sb p′ p′ τ τ u)
  result : Q.Ops κ
  Q.Ops.good result = good
  Q.Ops.mono result = mono

open import Data.Unit using (tt)
module Model = Stage (L.suc L.zero) tt Levels.one
actual : A.Gd (L.ψ (L.zero {a = L.suc L.zero}) (λ q → L.suc q) (L.Ω (L.suc L.zero)))
actual = Q.Ops.good Model.result tt L.zero (λ q → L.suc q) A.oneΩ
```
