# 旧表固定缺口的基本列检查
验收文件；编译定理：目标基本列的ρ公式、全项HC实例及旧表接线；逐项值支配未证。
内链与整行直接取YiE4参数实例，未改具体对象；不判定FirstMissing或终点丢值。
来源：YiE4Default双向接线；HC分支反演用YiRefTw2.hω-inv，NF保持用EboLeanClosure.cl-fsn-NF。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAZStart where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanBase as EB
import OCF.Align.EboLeanClosure as EC
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiE4Param as R
import OCF.Lean.YiE4ParamFrame as V
import OCF.Lean.YiE4ParamInner as I
import OCF.Lean.YiE4Default as Df
import OCF.Lean.YiE4Instances as C
import OCF.Lean.YiE4Objects as A
import OCF.Lean.YiLBStart as LS
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiRefTw2 as RT
import OCF.Lean.YiExInst as XI
module D = R.At (MT.rbᶻ B.Λ)
module U = V.For (MT.rbᶻ B.Λ)
module N = I.At (MT.rbᶻ B.Λ)
Missing : Set
Missing = U.Missing
from-original : Df.OriginalAtOne → Missing
from-original = Df.from-original
to-original : Missing → Df.OriginalAtOne
to-original = Df.to-original
canonical-environment = C.Original.environment
canonical-hc : SI.E.HC A.target
canonical-hc = C.Original.hc
ρ : ℕ → E.T
ρ zero = E.natT 1
ρ (suc n) = E.ψ [] (E.Ωt (ρ n)) ∷ []
γ-ρ : ∀ n → E.γT (E.ΩTower 2) [] n ≡ ρ n
γ-ρ zero = refl
γ-ρ (suc n) = cong (λ t → E.ψ [] (E.Ωt t) ∷ []) (γ-ρ n)
A-fsn : ∀ n → E.fsn (E.EBOψ 2) n ≡ ρ (suc n)
A-fsn n = cong (λ t → E.ψ [] (E.Ωt t) ∷ []) (γ-ρ n)
T : ℕ → E.T
T n = E.fsn LS.target n
T-form : ∀ n → T n ≡ E.ψ [] (E.Ωt (E.Ωt (ρ (suc n)))) ∷ []
T-form n = cong (λ t → E.ψ [] (E.Ωt (E.Ωt t)) ∷ []) (A-fsn n)
T0 : T 0 ≡ E.ψ [] (E.Ωt (E.Ωt (ρ 1))) ∷ []
T0 = T-form 0
T1 : T 1 ≡ E.ψ [] (E.Ωt (E.Ωt (ρ 2))) ∷ []
T1 = T-form 1
nf-T : ∀ n → EB.NF (T n)
nf-T n = EC.cl-fsn-NF LS.nf-target refl n
-- perf: S-1/S-3，沿证书算出的具体参照不在消费端展开。
opaque
  hc-T : ∀ n → SI.E.HC (T n)
  hc-T n = SI.conv (RT.hω-inv (XI.back LS.hc-target) refl n)
  hc-T-form : ∀ n → SI.E.HC (E.ψ [] (E.Ωt (E.Ωt (ρ (suc n)))) ∷ [])
  hc-T-form n = subst SI.E.HC (T-form n) (hc-T n)
inner0 : N.Inner.chain 0 ≡ B.zero
inner0 = refl
inner1 : N.Inner.chain 1 ≡ N.Inner.feed B.zero
inner1 = refl
G : ℕ → O.Tr⁺ B.zero
G n = N.Inner.out (N.Inner.chain n)
P : ℕ → B.Tr B.zero
P = O.cum (λ n → proj₁ (G n))
P0 : P 0 ≡ proj₁ (G 0)
P0 = refl
P1 : P 1 ≡ (proj₁ (G 0) O.+ proj₁ (G 1))
P1 = refl
whole-row : D.output ≡ O.limc⁺ G
whole-row = N.first-row
```
