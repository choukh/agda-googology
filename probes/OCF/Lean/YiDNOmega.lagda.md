# 非有限偏移的可满足性检查
验收文件；编译定理：偏移读回为 ω，具有 NoΩ、来源证据及合法的指定请求。
结点 padding 为 2、tail 为后继，延用已知 neck 的字段形状；不是实际深颈结点的等式。
未证明此请求的值律，也不把 ω 证据当作 slot 证据；来源：YiSQOmega.read-ω、YiHCCheck.of⁰、YiLMCheck.hΩω。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDNOmega where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiNIDomain as D
import OCF.Lean.YiNIIface as NI
import OCF.Lean.YiCNDomain as CN
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCCheck as HC
import OCF.Lean.YiLLCheck as LL
import OCF.Lean.YiSQOmega as W
import OCF.Lean.YiCLPhi as Phi
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiVRRel as VR
import OCF.Lean.YiLMCheck as LM
import OCF.Lean.YiDNRequests as R

offsetω : B.L
offsetω = B.↑ B.zero W.ω

ok-nat : ∀ n → P.Ok (B.↑ B.zero (H.nat n))
ok-nat zero = tt
ok-nat (suc n) = tt , λ _ → ok-nat n

okω : P.Ok offsetω
okω = (λ n → P.wk (P.◃→⊑ B.zero B.◃s)) , ok-nat

no-nat : ∀ n → VR.NoΩ (B.↑ B.zero (H.nat n))
no-nat zero = tt
no-nat (suc n) = no-nat n

noω : VR.NoΩ offsetω
noω = no-nat

nonfinite : ∀ n → offsetω ≡ H.fn n → ⊥
nonfinite zero ()
nonfinite (suc n) ()

readbackω : D.Readback offsetω
readbackω = record
  { source = B.zero ; canonical = CN.cz ; code = W.ω ; reads = refl }

readsω : GR.Rd offsetω Phi.ωᵀ
readsω = LL.read0 (HC.of⁰ W.read-ω)

-- 零前缀保留原字段写法，不用函数外延将它删除。
ok-zeros : ∀ a n b → P.OkO a b → P.OkO a (D.zeros n b)
ok-zeros a zero b ob = ob
ok-zeros a (suc n) b ob = P.OkO⊕ a B.zero (D.zeros n b) tt (ok-zeros a n b ob)

nodeω : D.Node
nodeω = record
  { offset = offsetω ; readback = readbackω ; padding = 2 ; tail = B.suc
  ; okay = (tt , (λ c → P.z≤ (offsetω B.⊕ D.zeros 2 (B.↑ B.zero (B.suc c))))) , λ c →
      P.Ok⊕ offsetω (D.zeros 2 (B.↑ B.zero (B.suc c))) okω
        (ok-zeros offsetω 2 (B.↑ B.zero (B.suc c))
          (P.OkO↑ offsetω B.zero tt (P.z≤ offsetω) (B.suc c))) }

omega-request : NI.Request
omega-request = R.request nodeω Phi.ωᵀ readsω LM.hΩω

omega-index : NI.Request.index omega-request ≡ Phi.ωᵀ
omega-index = refl

OmegaLaw : Set
OmegaLaw = NI.Law (R.single omega-request)
```
