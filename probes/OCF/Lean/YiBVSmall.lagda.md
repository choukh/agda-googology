# 最小规范输入与第 0 分支
验收文件，读记号；编译定理：变量前提有居民，最小 Ω 行保留，第 0 分支满足所需关系。
MinimalGoal 只是类型，未构造；不声称全证据域的分支关系、NextSlot 或 RowOneAtTwo。
有限层关系证明复用 YiTBFam.Self.PF/liftC/liftU；没有更换最小表或标准底。
入口：YiBVDomain；一般 Ω 行规格在 YiBVRows。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBVSmall where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiANFam as AF
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiBVDomain as D
import OCF.Lean.YiBVRows as Rows
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiCNDomain as CN
open import Data.Maybe using (just)
child : B.Tr B.zero → B.L
child d = K.two B.⊕ B.↑ B.zero (B.suc d)
layer : B.L
layer = B.nd (B.sΩ B.zero) child
okay : P.Ok layer
okay = (tt , (λ d → P.z≤ (child d))) , λ d →
  P.Ok⊕ K.two (B.↑ B.zero (B.suc d)) (tt , λ _ → tt , λ _ → tt)
    (P.OkO↑ K.two B.zero tt (P.z≤ K.two) (B.suc d))
lower : ∀ d → P._≤_ K.one (child d)
lower d = P.inc tt P.self P.∙ P.lift K.two (B.↑ B.zero (B.suc d))
minimal : D.Input
minimal = record
  { layer = layer ; offset = K.two
  ; readback = record { source = B.zero ; canonical = CN.cz
    ; code = B.suc (B.suc B.zero) ; reads = refl }
  ; floor = P.inc tt P.self ; padding = 0 ; tail = B.suc ; tail-eq = λ d → refl
  ; child = child ; child-eq = λ d → refl ; layer-eq = refl
  ; okay = okay ; table = MT.rbᶻ layer ; base = F.B₀ layer
  ; base-ok = λ i u → K.⊴r ; lower = lower ; lower-eq = λ d → refl
  ; path = P.inu lower ; path-eq = refl
  ; beta = O.Ωt K.one ; beta-ok = H.Mβ 0
  ; source = proj₁ (O.Ωt layer) ; source-eq = refl }
MinimalGoal : Set
MinimalGoal = D.Input.Goal minimal
module Small = Rows.Node child okay (MT.rbᶻ layer) (F.B₀ layer) lower (O.Ωt K.one)
small-keep : Small.keep ≡ just (K.q1 , (λ d → d) , refl)
small-keep = refl
small-index : E.T
small-index = E.ψ (E.natT 1) (E.natT 1) ∷ []
one-source : H.M 1 (E.natT 1) (proj₁ (O.Ωt K.one))
one-source = K.mw (K.mU K.mz (K.m1 refl K.mz)) B.◃w
at-one : (o : P.Ok K.one) (r : TB.Rb K.one) → TF.SΩ small-index 1 1 o r P.self
at-one o r base beta ok hbeta = TF.Self.PF 0 o r base beta hbeta one-source
at-two : (o : P.Ok K.two) (r : TB.Rb K.two)
  → TF.SΩ small-index 2 1 o r (P.inc tt P.self)
at-two o r = TF.liftC {t = small-index} {m = 1} {j = 1} o r P.self
  (at-one (proj₂ o tt) (proj₂ r tt))
at-three : (o : P.Ok (H.fn 3)) (r : TB.Rb (H.fn 3))
  → TF.SΩ small-index 3 1 o r (P.inu (λ _ → P.inc tt P.self))
at-three o r = TF.liftU {t = small-index} {m = 2} {j = 1} o r (P.inc tt P.self)
  (at-two (proj₂ o tt) (proj₂ r tt))
branch-zero : H.M 1 small-index (proj₁ (Small.child-out B.zero))
branch-zero = at-three (proj₂ okay B.zero) (proj₂ (D.Input.table minimal) B.zero)
  (Small.child-base B.zero) (O.Ωt K.one) (λ i u → K.⊴r) (H.Mβ 0)
branch-zero-target : small-index ≡ E.fsT D.slot []
branch-zero-target = refl
```
