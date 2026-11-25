# 第 0 层孩子结点的变量请求
验收文件，读记号；本件给变量陈述及证据域，不声称目标关系有居民。
层号、偏移、孩子、表、底与源树都是变量；定义等式与实际路径作为数据保留。
最小输入及其第 0 分支的实填见 YiBVSmall；Ω 行的变量等式见 YiBVRows。
来源：读回证据与零前缀复用 YiNIDomain，不扩大到全合法域。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBVDomain where
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiRBFam as RF
import OCF.Lean.YiNIDomain as D
import OCF.Align.EboLeanDef as E
slot : E.T
slot = E.ψ (E.natT 1) (E.ΩTower 2) ∷ []
record Input : Set where
  field
    layer offset : B.L
    readback : D.Readback offset
    floor : P._≤_ K.one offset
    padding : ℕ
    tail : B.Tr B.zero → B.Tr B.zero
    tail-eq : ∀ d → tail d ≡ B.suc d
    child : B.Tr B.zero → B.L
    child-eq : ∀ d → child d ≡ offset B.⊕ D.zeros padding (B.↑ B.zero (tail d))
    layer-eq : layer ≡ B.nd (B.sΩ B.zero) child
    okay : P.Ok layer
    table : TB.Rb layer
    base : F.Base layer
    base-ok : RF.OKB base
    lower : ∀ d → P._≤_ K.one (child d)
    lower-eq : ∀ d → lower d ≡ subst (P._≤_ K.one) (sym (child-eq d))
      (floor P.∙ P.lift offset (D.zeros padding (B.↑ B.zero (tail d))))
    path : P._≤_ K.one layer
    path-eq : path ≡ subst (P._≤_ K.one) (sym layer-eq) (P.inu lower)
    beta : O.Tr⁺ K.one
    beta-ok : H.M 1 (E.Ωt (E.natT 1)) (proj₁ beta)
    source : B.Tr layer
    source-eq : source ≡ proj₁ (O.Ωt layer)
  Goal : Set
  Goal = H.M 1 slot (proj₁ (TB.ψ layer okay table base K.one path beta source))
domain₀ : K.M⁰ [] B.zero
domain₀ = K.mz
domain₁ : K.M⁰ (E.natT 1) (B.suc B.zero)
domain₁ = K.m1 refl K.mz
```
