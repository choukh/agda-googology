# γ 行前提的有限层居民
验收文件，读记号；编译定理：Rows 在 d = zero、μ = 3 上有居民，表、底及起点仍取变量。
这是 from-rows 的可满足性检查；此实例不提供 m1 所需的 M⁰ 3 zero，不是 Step 的居民。
来源：直接实填 YiTBFam.chain/LF，有限层底证据复用其 sΩ-LF 的构造。
一般后继步骤仍未填；本件不声称最小目标或实际 BranchNeed。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQLPremise where
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)
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
import OCF.Lean.YiQLSuccessor as C
import OCF.Align.EboLeanDef as E
module Fin (o : P.Ok (S.child (B.suc B.zero))) (r : TB.Rb (S.child (B.suc B.zero)))
  (base : F.Base (S.child (B.suc B.zero))) (beta : O.Tr⁺ K.one)
  (ok : RF.OKB base) (hb : H.M 1 (E.Ωt (E.natT 1)) (proj₁ beta)) where
  module R = C.Row B.zero o r base beta ok hb
  gb : RF.GB 3 base []
  gb = RF.mkGB (λ {i} si → ok (H.fn i) (P.inc tt (L.pth si)))
    (λ {i} si → L.ΩJ i (base (H.fn i) (P.inc tt (L.pth si))) (ok (H.fn i) (P.inc tt (L.pth si))))
  g : B.Tr (H.fn 3) → B.Tr (H.fn 4)
  g c = B.up B.zero tt (B.suc c) (O.z◃ c B.◃s)
  branches : ∀ η c → H.M 3 η c → H.M 4 (E.fsT (AF.Ωᴺ 4) η) (g c)
  branches η c l = subst (λ t → H.M 4 t (g c)) (sym (AF.fsTΩ 3 η)) (K.mU K.mz (H.mwN 3 l B.◃s))
  chain : ∀ n → H.M 3 (E.γT (AF.Ωᴺ 4) (E.natT 3) n) (R.chain (suc n))
  chain n = TF.chain o r L.s0 [] base gb (AF.cofΩ 3) refl branches n
  cb-good : RF.GB 2 R.cb []
  cb-good = RF.mkGB (λ {i} si → ok (H.fn i) (P.inc tt (P.inc tt (L.pth si))))
    (λ {i} si → L.ΩJ i (R.cb (H.fn i) (P.inc tt (L.pth si))) (ok (H.fn i) (P.inc tt (P.inc tt (L.pth si)))))
  rows : R.Rows (E.natT 3)
  rows n = H.mwN 1 (TF.LF (proj₂ o tt) (proj₂ r tt) (RF.tu (RF.can (L.ss L.s0))) [] R.cb cb-good beta hb (chain n)) (B.◃l 0)
```
