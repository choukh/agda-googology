# 变量环境与封装折叠
验收工程底座；环境投影、变量计算律与原出口接线为编译定理。
来源：YiE3Base、YiLBActual.out-child；入口见 YiE4Default。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiE4Base where
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiLBActual as LA
Ctx : Set
Ctx = Σ B.L λ h → P.Ok h × TB.Rb h × F.Base h
level : Ctx → B.L
level = proj₁
okay : (d : Ctx) → P.Ok (level d)
okay d = proj₁ (proj₂ d)
table : (d : Ctx) → TB.Rb (level d)
table d = proj₁ (proj₂ (proj₂ d))
base : (d : Ctx) → F.Base (level d)
base d = proj₂ (proj₂ (proj₂ d))
-- perf: S-1，封装变量上的折叠；避免变量实例化后重走函数体。
opaque
  collapse : Ctx → O.Tr⁺ B.zero → O.Tr⁺ B.zero
  collapse (h , o , r , bs) β = TB.ψ h o r bs B.zero (P.z≤ h) β (proj₁ (O.Ωt h))
  collapse-eq : ∀ h o r bs β → collapse (h , o , r , bs) β ≡ TB.ψ h o r bs B.zero (P.z≤ h) β (proj₁ (O.Ωt h))
  collapse-eq h o r bs β = refl
make : B.Tr (B.tw 2) → Ctx
make c = FR.Step.child 2 c , proj₂ (P.Ok-tw 3) c , MT.rbᶻ (FR.Step.child 2 c) , (λ i u → GI.baseᴱ 3 i (P.inc c u))
-- perf: C-9/C-24，复用 YiLBActual.out-child 的变量计算律。
opaque
  unfolding collapse
  raw-wire : ∀ q → collapse (make (FR.Step.chain 2 q)) (GI.betaᴱ 3) ≡ FR.Step.out 2 (FR.Step.chain 2 q)
  raw-wire q = sym (LA.out-child q)
```
