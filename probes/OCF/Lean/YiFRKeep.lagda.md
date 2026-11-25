# V173 的后继分支复查
验收文件；Fin.Keep 对 m1 构造子封闭，并给标准底、非零左项 suc zero 的无前提实例。
未证完整 Keep 或 Shift，不声称已覆盖塔的实际 Ω 分支。
来源：复用 YiSPInst.Fin 的接口；后继证明照 YiLTFold.LF 的 m1 行，有限底直接复用 YiKPInst.Std.gb₀c。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFRKeep where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁)
open import Data.List using ([]; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiHCRel using (mz; m1)
open import OCF.Lean.YiHCFam using (nextJ)
import OCF.Lean.YiKPInst as KP
import OCF.Lean.YiRBSib as RS
open import OCF.Lean.YiCLFam using (nat; fn)
open import OCF.Lean.YiCLLow using (pth)
open import OCF.Lean.YiLTKid using (ℓ¹; o¹)
open import OCF.Lean.YiSPInst using (module Fin)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cof++1; pred++)
import OCF.Align.EboLeanDef as E
module Recheck (r : Rb ℓ¹) where
  open Fin r
  keep-suc : ∀ B t {a x} (e : E.cof a ≡ E.c1) (m : M¹ (E.pred a) x)
    → Keep B t m → Keep B t (m1 e m)
  keep-suc B t {a} {x} e m ih n {i} si =
    nextJ i (ψ ℓ¹ o¹ r B (fn i) (inc (nat (suc n)) (inc tt (pth si)))
      (B (fn i) (inc (nat (suc n)) (inc tt (pth si)))) x)
      (cofψ1 (E.natT i) (t ++ a) (cof++1 t a e))
      (λ q → trans (fsnψ1 (E.natT i) (t ++ a) q (cof++1 t a e))
        (cong (λ v → replicate q (E.ψ (E.natT i) v)) (pred++ t a e))) (ih n si)
  gb0c : ∀ n → GBf n [] (B₀ (fn n))
  gb0c zero = KP.Std.gb₀c (RS.rb-no ℓ¹) zero
  gb0c (suc n) = KP.Std.gb₀c (RS.rb-no ℓ¹) (suc n)
  gb0 : GB¹ (B₀ ℓ¹) []
  gb0 = mkGB¹ (m1 refl mz) (λ { _ n refl → gb0c n })
  oneM : M¹ (E.natT 1) (suc zero)
  oneM = m1 refl mz
  keep-one : Keep (B₀ ℓ¹) [] oneM
  keep-one = keep-suc (B₀ ℓ¹) [] refl mz (keep-mz (B₀ ℓ¹) [] gb0 zero)
```
