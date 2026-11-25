# 第 3 站实际第 2 链点的目标参数证书
验收文件；seed、Ωseed 与 source 为闭证书，未给出零层折叠后的值下界。
source 的参照参数是 FirstMissing 外层 ψ 的实际参数；不声称 FirstMissing 或 Kᴱ3。
来源：YiTBFam.ψ-⊵ 给实际底与链点的结构上界，YiNLCanonical.canon-top 及 YiNLRaise.raiseR 构造关系。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMSSeed where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (proj₁)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiFRStep as S
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiLLCheck as LL
import OCF.Lean.YiNLCanonical as NL
import OCF.Lean.YiNLRaise as NR
import OCF.Lean.YiNLCtx as NC
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiKVRel using (_⊴_)
open import OCF.Lean.YiKCStep using (⊴-trans)
k = B.tw 2
h = S.Step.child 1
module G = LL.G (B.sΩ (B.tw 1)) h
γ = E.EBOψ 2
base = GI.baseᴱ 3 k (P.ink P.self)
base-above : proj₁ (O.Ωt k) ⊴ proj₁ base
base-above = TF.ψ-⊵ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) k (P.inc 3 (P.ink P.self)) (O.Ωt k) (GI.pre 3)
chain-above : proj₁ base ⊴ S.Step.chain 2 2
chain-above = TF.ψ-⊵ (B.tw 3) (P.Ok-tw 3) (MT.rbᶻ (B.tw 3)) (GI.baseᴱ 3) k (P.ink P.self) base (S.Step.g 2 (S.Step.chain 2 1))
γ-bound : γ E.<ᵀ E.Ωt (NL.κ 2)
γ-bound = E.hd< (E.lv< E.[]<)
seed : GR.R k γ (S.Step.chain 2 2)
seed = G.m⊴ (LL.rdown k (inj₁ γ-bound) (NL.canon-top 2)) (⊴-trans base-above chain-above)
Ωγ-bound : E.Ωt γ E.<ᵀ E.Ωt (NL.κ 2)
Ωγ-bound = E.hd< (E.lv< (E.hd< (E.lv< E.[]<)))
Ωseed : GR.R k (E.Ωt γ) (S.Step.chain 2 2)
Ωseed = G.m⊴ (LL.rdown k (inj₁ Ωγ-bound) (NL.canon-top 2)) (⊴-trans base-above chain-above)
source : GR.R (S.Step.child 2 (S.Step.chain 2 2)) (E.Ωt (E.Ωt γ)) (proj₁ (O.Ωt (S.Step.child 2 (S.Step.chain 2 2))))
source = NR.raiseR k (NC.prefix k) [] (GR.c0 refl) (NL.one-top k) Ωseed

γ-ref : E.γT (E.ΩTower 3) [] 1 ≡ γ
γ-ref = refl
```
