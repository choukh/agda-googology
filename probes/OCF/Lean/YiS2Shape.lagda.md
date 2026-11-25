# 第 2 站的实际参数
验收文件；编译等式展开 row、闭树、继承底、起点、路径与前两个实际链点；LowAt 2 的输入有实例。
来源：展开 YiGIInst.keelᴱ 与 YiFRStep.Step；输入实例用 YiNLKeel.leaf-keel 和 YiCNAccept.rd2。
所有参数仍为实际底；零层构造见 YiS2Low。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiS2Shape where
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiTBRow as T
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiMTValue as MV
import OCF.Lean.YiCNKeel as CN
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; keelᴱ; baseᴱ; betaᴱ; FΛ)
open import OCF.Lean.YiExSuff using (module ExSuff)
import OCF.Lean.YiFRStep as FR
open import OCF.Lean.YiNLKeel using (leaf-keel)
open import OCF.Lean.YiCNAccept using (rd2)
open ExSuff gradedᵍ domsᵍ using (Keel⁻)
row2 : Keel⁻.row keelᴱ 2 ≡ (E.ψ [] (E.Ωt (E.Ωt (E.natT 1))) ∷ [])
row2 = refl
base2 : ∀ i u → baseᴱ 2 i u ≡ T.ψ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) i (P.inc 2 u) (O.Ωt i) (O.cum FΛ 1)
base2 i u = refl
beta2 : betaᴱ 2 ≡ T.ψ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero) (O.cum FΛ 1)
beta2 = refl
path2 : Keel⁻.w₀ keelᴱ 2 ≡ P.z≤ (B.tw 2)
path2 = refl
closed2 : Keel⁻.twc keelᴱ 2 ≡ MV.brᶻ 2
closed2 = refl
actual2 : Keel⁻.twc keelᴱ 2 ≡ proj₁ (T.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2)) (baseᴱ 2) B.zero (P.z≤ (B.tw 2)) (betaᴱ 2) (proj₁ (O.Ωt (B.tw 2))))
actual2 = refl
low2-type : CN.LowAt 2 ≡ (GR.R (B.tw 2) (E.Ωt (E.Ωt (E.natT 1))) (proj₁ (O.Ωt (B.tw 2))) → Σ (H.M⁰ (E.ψ [] (E.Ωt (E.Ωt (E.natT 1))) ∷ []) (Keel⁻.twc keelᴱ 2)) H.Exᴴ)
low2-type = refl
input2 : GR.R (B.tw 2) (E.Ωt (E.Ωt (E.natT 1))) (proj₁ (O.Ωt (B.tw 2)))
input2 = leaf-keel 2 rd2
chain0 : FR.Step.chain 1 0 ≡ B.zero
chain0 = refl
chain1 : FR.Step.chain 1 1 ≡ proj₁ (T.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2)) (baseᴱ 2) (B.tw 1) (P.ink P.self) (baseᴱ 2 (B.tw 1) (P.ink P.self)) (proj₁ (O.upz {s = B.sΩ (B.tw 1)} {h = FR.Step.child 1} B.zero (O.Ωt (FR.Step.child 1 B.zero)))))
chain1 = refl
chain1-child : FR.Step.chain 1 1 ≡ proj₁ (T.ψ (B.tw 1) (P.Ok-tw 1) (MT.rbᶻ (B.tw 1)) (λ i u → baseᴱ 2 i (P.inc B.zero u)) (B.tw 1) P.self (baseᴱ 2 (B.tw 1) (P.ink P.self)) (proj₁ (O.Ωt (B.tw 1))))
chain1-child = refl
```
