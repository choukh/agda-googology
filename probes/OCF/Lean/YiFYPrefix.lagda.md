# 终点实际前缀的 ω 次累加放大
验收文件；编译定理 prefix-next、iterate-bound：实际外层前缀每步支配前项的 ω 次累加，故任意有限迭代均在 EBOᶻ 之下。
prefix-actual 接 Keel⁻.twc 原实例；未更换原表、底或链，不断言第3站的全参照下界。
来源：YiFYTop.top-next、YiKidGen.next-mono，两种读回桥及 YiFRStations.branch-form、YiGIEnd.upperᴱ。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFYPrefix where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; trans)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiFRStations as FS
import OCF.Lean.YiGIEnd as GE
import OCF.Lean.YiOLBoost as OL
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiKQSuff as QS
import OCF.Lean.YiKidGen as KG
import OCF.Lean.YiExSuff as EX
open EX.ExSuff GI.gradedᵍ GI.domsᵍ using (Keel⁻)
open import OCF.Lean.YiFYTop using (top-next)
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; l≼)
next-mono : (u v : O.Tr⁺ B.zero) → K.readRW (proj₁ u) ≼ K.readRW (proj₁ v)
  → K.readRW (proj₁ (O.next⁺ u)) ≼ K.readRW (proj₁ (O.next⁺ v))
next-mono u v low = ≼-trans (QS.read≤ (proj₁ (O.next⁺ u)))
  (≼-trans (KG.next-mono u v (≼-trans (CS.rr≼ (proj₁ u))
    (≼-trans low (QS.read≤ (proj₁ v))))) (CS.rr≼ (proj₁ (O.next⁺ v))))
append-next : (g : ℕ → B.L) (o : P.Ok (B.nd B.sL g))
  (r : TB.Rb (B.nd B.sL g)) (bs : F.Base (B.nd B.sL g))
  (β : O.Tr⁺ B.zero) (x : B.Tr (B.nd B.sL g)) (n : ℕ)
  → K.readRW (proj₁ (O.next⁺ (TB.ψ (B.nd B.sL g) o r bs B.zero (P.z≤ (B.nd B.sL g)) β x)))
  ≼ K.readRW (proj₁ (TB.ψ (B.nd B.sL g) o r bs B.zero (P.z≤ (B.nd B.sL g)) β
    (x O.+ proj₁ (O.upz n (O.Ωt (g n))))))
append-next g o r bs β x n = top-next (g n) (proj₂ o n) (proj₂ r n)
  (λ i u → TB.ψ (B.nd B.sL g) o r bs i (P.inc n u) (bs i (P.inc n u)) x)
  (TB.ψ (B.nd B.sL g) o r bs B.zero (P.z≤ (B.nd B.sL g)) β x)
opaque
  prefix : ℕ → O.Tr⁺ B.zero
  prefix n = TB.ψ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) B.zero (P.z≤ B.Λ)
    (O.Ωt B.zero) (O.cum GI.FΛ n)
  prefix-eq : ∀ n → prefix n ≡ TB.ψ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) B.zero (P.z≤ B.Λ)
    (O.Ωt B.zero) (O.cum GI.FΛ n)
  prefix-eq n = refl
  prefix-next : ∀ n → K.readRW (proj₁ (O.next⁺ (prefix n))) ≼ K.readRW (proj₁ (prefix (suc n)))
  prefix-next n = append-next B.tw P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) (O.Ωt B.zero) (O.cum GI.FΛ n) (suc n)
  prefix-beta : prefix 2 ≡ GI.betaᴱ 3
  prefix-beta = refl
prefix-actual : ∀ n → proj₁ (prefix n) ≡ Keel⁻.twc GI.keelᴱ n
prefix-actual n = trans (cong proj₁ (prefix-eq n)) (sym (FS.branch-form n))
prefix-upper : ∀ n → K.readRW (proj₁ (prefix n)) ≼ K.readRW MT.EBOᶻ
prefix-upper n = subst (λ x → K.readRW x ≼ K.readRW MT.EBOᶻ) (sym (prefix-actual n)) (GE.upperᴱ n)
index : ℕ → ℕ
index zero = 2
index (suc n) = suc (index n)
iterate-bound : ∀ n → K.readRW (proj₁ (O.iter O.next⁺ (prefix 2) n)) ≼ K.readRW (proj₁ (prefix (index n)))
iterate-bound zero = ≼-refl _
iterate-bound (suc n) = ≼-trans (next-mono (O.iter O.next⁺ (prefix 2) n) (prefix (index n)) (iterate-bound n))
  (prefix-next (index n))
```
