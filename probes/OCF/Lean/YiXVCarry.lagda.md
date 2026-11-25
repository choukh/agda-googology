# YiXV：实际回灌底的上界
> 验收文件。编译定理：`γ₁` 的形状，计入前缀底后的折叠上界 `γ₁-upper`。
> `Lift.upc-comp` 把第 0 层上折搬到参照；复用 `YiXVPlus`、`YiOverOps`，不改上折或折叠。
> 没有 `pre 1`、`Need1` 或全塔上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCarry where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (self; ins)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (T₀; read)
open import OCF.Lean.YiXVStart using (B2)
open import OCF.Lean.YiXVLocal using (D1; ΩU)
import OCF.Align.Level as L
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVSim as S
import OCF.Lean.YiXVPlus as P
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼)

γ₁ : Tr (suc zero)
γ₁ = bs B2 (suc zero) (ins self)

γ₁-form : γ₁ ≡ ψs (suc zero) tt tt (B₀ (suc zero)) (suc zero) self (Ωt (suc zero)) (Ωt-nz (suc zero)) (Ωt (suc zero))
γ₁-form = refl

module Lift (B : Base (suc zero)) where
  module A = S.Sim B
  module C = P.Closure B

  upc-comp : ∀ {x X} (nx : suc zero ⊢ zero ◃ x) → (gd : O.Gd X) → A.U x (O.ψ₁ X) →
    (σ : L.Simᴵ L.zero (L.suc L.zero)) → (z : Tr zero) →
    A.U (Upc (suc zero) tt x nx z) (O.ψ₁ (L.add X σ (read z)))
  upc-comp nx gd hx σ zero = hx
  upc-comp {X = X} nx gd hx σ (suc z) = C.next-comp (Upc-nz (suc zero) tt _ nx z)
    (O.Gd-ψ₁ (O.Gd-add⁰ gd (read z))) (upc-comp nx gd hx σ z)
  upc-comp {X = X} nx gd hx σ (lim f a) = A.ul (λ n → A.uw (O.Gd-ψ₁ (O.Gd-add⁰ gd (read (f n))))
    (upc-comp nx gd hx σ (f n)) (R.≤l n (O.reflₚ (O.Gd-ψ₁ (O.Gd-add⁰ gd (read (f n)))))))
  upc-comp nx gd hx σ (Ω () g)
  upc-comp nx gd hx σ (up y () z e)

ΩΩ≤ψ : (O.Ω₁ L.+ O.Ω₁) R.≤ₚ O.ψ₁ O.Ω₁
ΩΩ≤ψ = R.trans (O.+ₚ O.Ω≤Ω (O.ψ₁-mono (O.z≤ O.Ω₁))) O.O2ref

module A = S.Sim D1

ΩψU : A.U (Ωt (suc zero)) (O.ψ₁ O.Ω₁)
ΩψU = A.uw (O.Gd-+ O.Gd-Ω O.Gd-Ω) ΩU ΩΩ≤ψ

γ₁U : A.U γ₁ (O.ψ₁ (O.Ω₁ L.+ O.Ω₁))
γ₁U = A.un (λ a y q → A.uw
  (O.Gd-ψ₁ (O.Gd-add⁰ O.Gd-Ω (L.suc (read a))))
  (Lift.upc-comp D1 (Ωt-nz (suc zero)) O.Gd-Ω ΩψU (λ r → L.suc r) (suc a))
  (O.ψ₁-mono (O.add-mono⁰ (O.reflₚ O.Gd-Ω) (≼-trans q (proj₂ (O.tr⁻≈ y))))))

γ₁-upper : read (ψ⊥ (suc zero) tt tt D1 γ₁) ≼ L.ψ⁰ (O.ψ₁ (O.ψ₁ O.Ω₁))
γ₁-upper = ≼-trans (proj₁ (A.upper (O.Gd-ψ₁ (O.Gd-+ O.Gd-Ω O.Gd-Ω)) γ₁U))
  (R.mono⁰ (O.ψ₁-mono ΩΩ≤ψ))
```
