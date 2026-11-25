# 既有取支与右加推导的出口证据
验收文件；编译定理：`QEx` 要求指定保持推导可出口，`ex-upL0` 与 `ex-right` 传递该证据。
来源：对 `YiLTLift.upL` 的第 0 支展开出口；右加沿 `YiHCRel.G⁰.m-right` 的推导递归。
不要求底的证明或起点推导自身可出口，不给出一般 `Lift₁`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiS1Exit where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps using (Tr⁺)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb)
open import OCF.Lean.YiRBFam using (OKB)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiLTLift as LL
import OCF.Align.EboLeanDef as E

QEx : ∀ {t ℓ} → LL.Q t ℓ → Set
QEx {t} {ℓ} q = (o : Ok ℓ) (r : Rb ℓ) (v : zero ≤ ℓ) (zv : LL.ZP ℓ v)
  (B : Base ℓ) (ok : OKB B) (β : Tr⁺ zero) (hβ : H.M⁰ (E.natT 1) (proj₁ β))
  → H.Exᴴ (q o r v zv B ok β hβ)

ex-upL0 : ∀ {t} {g : ℕ → L} {q : LL.Q t (g 0)} → QEx q → QEx (LL.upL {g = g} 0 q)
ex-upL0 {g = g} ex o r (inu ws) (LL.zu zw) B ok β hβ = ex
  (proj₂ o 0) (proj₂ r 0) (ws 0) (zw 0)
  (λ i u → B i (inc 0 u)) (λ i u → ok i (inc 0 u)) β hβ

ex-right : ∀ {t y} (a : Tr zero) (m : H.M⁰ t y) → H.Exᴴ m → H.Exᴴ (H.G⁰.m-right a m)
ex-right a H.mz ex = tt
ex-right a (H.m1 e m) ex = ex-right a m ex
ex-right a (H.mL e h) ex = λ n → ex-right a (h n) (ex n)
ex-right a (H.mΩ {p = ()} _ _ _)
ex-right a (H.mU {c = ()} _ _)
ex-right a (H.mw m d) ex = ex-right a m ex
ex-right a (H.mc le m) (ns , nt , ct , ex) = ns , nt , ct , ex-right a m ex
```
