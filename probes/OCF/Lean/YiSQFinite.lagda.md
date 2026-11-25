# d = 1 的有限 LF 对照
验收文件，读记号；编译定理：Step 的 η = 1 实例和 Rows 4、SecondRow 4 的有限实例。
Rows 4 不满足同一 d 的 Step 读回前提，否定证据见 YiSQPremise.no-domain4。
来源：YiQLCheck.step-at-one；Rows 按 YiQLPremise.Fin 的 chain/LF 证明换到 d = 1。
不声称一般 Rows、Step、MinimalGoal 或实际 BranchNeed。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSQFinite where
open import Data.Nat using (suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiCLLow as L
import OCF.Lean.YiRBFam as RF
import OCF.Lean.YiANFam as AF
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiQLRead as Q
import OCF.Lean.YiQLCheck as C
import OCF.Lean.YiQLSuccessor as QS
import OCF.Align.EboLeanDef as E
premise : K.M⁰ [] (B.suc B.zero)
premise = K.mz
input : Q.Need [] (B.suc B.zero)
input = Q.zero (B.suc B.zero)
step-at-d1 : Q.Need [] (B.suc B.zero) → Q.Need (E.natT 1) (B.suc (B.suc B.zero))
step-at-d1 = C.step-at-one (B.suc B.zero)
result : Q.Need (E.natT 1) (B.suc (B.suc B.zero))
result = step-at-d1 input
source-shape : S.child (B.suc (B.suc B.zero)) ≡ H.fn 5
source-shape = refl
inner-shape : S.child (B.suc B.zero) ≡ H.fn 4
inner-shape = refl
module Fin (o : P.Ok (S.child (B.suc (B.suc B.zero)))) (r : TB.Rb (S.child (B.suc (B.suc B.zero))))
  (base : F.Base (S.child (B.suc (B.suc B.zero)))) (beta : O.Tr⁺ K.one)
  (ok : RF.OKB base) (hb : H.M 1 (E.Ωt (E.natT 1)) (proj₁ beta)) where
  module R = QS.Row (B.suc B.zero) o r base beta ok hb
  gb : RF.GB 4 base []
  gb = RF.mkGB (λ {i} si → ok (H.fn i) (P.inc tt (L.pth si)))
    (λ {i} si → L.ΩJ i (base (H.fn i) (P.inc tt (L.pth si))) (ok (H.fn i) (P.inc tt (L.pth si))))
  g : B.Tr (H.fn 4) → B.Tr (H.fn 5)
  g c = B.up B.zero tt (B.suc c) (O.z◃ c B.◃s)
  branches : ∀ η c → H.M 4 η c → H.M 5 (E.fsT (AF.Ωᴺ 5) η) (g c)
  branches η c l = subst (λ t → H.M 5 t (g c)) (sym (AF.fsTΩ 4 η)) (K.mU K.mz (H.mwN 4 l B.◃s))
  chain : ∀ n → H.M 4 (E.γT (AF.Ωᴺ 5) (E.natT 4) n) (R.chain (suc n))
  chain n = TF.chain o r L.s0 [] base gb (AF.cofΩ 4) refl branches n
  cb-good : RF.GB 3 R.cb []
  cb-good = RF.mkGB (λ {i} si → ok (H.fn i) (P.inc tt (P.inc tt (L.pth si))))
    (λ {i} si → L.ΩJ i (R.cb (H.fn i) (P.inc tt (L.pth si))) (ok (H.fn i) (P.inc tt (P.inc tt (L.pth si)))))
  rows : R.Rows (E.natT 4)
  rows n = H.mwN 1 (TF.LF (proj₂ o tt) (proj₂ r tt) (RF.tu (RF.pu (RF.can (L.ss L.s0)))) [] R.cb cb-good beta hb (chain n)) (B.◃l 0)
  second : R.SecondRow (E.natT 4)
  second = rows 1
```
