# 第 1 站的实际参数
验收文件；编译定理：第 1 站正是终点第 1 支，实际底和起点与 `YiMTValue` 的该支参数相同。
`actual≢standard` 区分实际闭树与标准底的 `twᶻ 1`，不比较两者的序数值。
来源：展开 `YiGIInst.keelᴱ`；参数名引用 `YiMTValue`，不改定义。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiS1Shape where
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
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; keelᴱ; baseᴱ; betaᴱ)
open import OCF.Lean.YiExSuff using (module ExSuff)
open ExSuff gradedᵍ domsᵍ using (Keel⁻)
row1 : Keel⁻.row keelᴱ 1 ≡ (E.ψ [] (E.Ωt (E.natT 1)) ∷ [])
row1 = refl
base1 : baseᴱ 1 ≡ MV.B1ᶻ
base1 = refl
beta1 : betaᴱ 1 ≡ MV.β1ᶻ
beta1 = refl
path1 : Keel⁻.w₀ keelᴱ 1 ≡ P.z≤ (B.tw 1)
path1 = refl
closed1 : Keel⁻.twc keelᴱ 1 ≡ MV.brᶻ 1
closed1 = refl
actual1 : Keel⁻.twc keelᴱ 1 ≡ proj₁ (T.ψ (B.tw 1) (P.Ok-tw 1) (MT.rbᶻ (B.tw 1)) (baseᴱ 1) B.zero (P.z≤ (B.tw 1)) (betaᴱ 1) (proj₁ (O.Ωt (B.tw 1))))
actual1 = refl
standard1 : MT.twᶻ 1 ≡ proj₁ (T.ψ (B.tw 1) (P.Ok-tw 1) (MT.rbᶻ (B.tw 1)) (F.B₀ (B.tw 1)) B.zero (P.z≤ (B.tw 1)) (O.Ωt B.zero) (proj₁ (O.Ωt (B.tw 1))))
standard1 = refl
low1-type : CN.LowAt 1 ≡ (GR.R (B.tw 1) (E.Ωt (E.natT 1)) (proj₁ (O.Ωt (B.tw 1))) → Σ (H.M⁰ (E.ψ [] (E.Ωt (E.natT 1)) ∷ []) (Keel⁻.twc keelᴱ 1)) H.Exᴴ)
low1-type = refl

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)
branch0 : B.Tr B.zero → B.Tr B.zero
branch0 (B.lim f _) = f 0
branch0 x = x
suc? : B.Tr B.zero → Bool
suc? (B.suc _) = true
suc? _ = false
shape-probe : B.Tr B.zero → Bool
shape-probe x = suc? (branch0 (branch0 x))
actual-probe : shape-probe (Keel⁻.twc keelᴱ 1) ≡ false
actual-probe = refl
standard-probe : shape-probe (MT.twᶻ 1) ≡ true
standard-probe = refl
false≢true : false ≡ true → ⊥
false≢true ()
actual≢standard : Keel⁻.twc keelᴱ 1 ≡ MT.twᶻ 1 → ⊥
actual≢standard e = false≢true (cong shape-probe e)
```
