# 干净对象的首个值界义务
验收文件；编译的条件定理把实际第 1 链点的关系证书送到 ψ₀(Ω_Ω) 下界。
`FirstChild` 尚无构造，本文件不宣称无条件值界，也不判定 ψ₀(Ω_{Ω₂})。
来源：`YiUTTwo.row` 的累计行；证书拼接沿 `YiUTTwoLocal.small-value` 与 `YiOLMilestone.assemble2`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFXFirst where
open import Data.Nat using (suc; zero)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (sym; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiAZLocal as AL
import OCF.Lean.YiOLMilestone as OL
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiExInst as XI
import OCF.Align.EboLeanDef as E
open import OCF.Align.Value using (_≼_; ≼-trans)

FirstChild : Set
FirstChild = K.M⁰ (E.fsn (AL.S 2) 0)
  (proj₁ (U.Inner.out (U.Inner.chain 1)))

first-output-rel : FirstChild → K.M⁰ (E.fsn (AL.S 2) 0) (proj₁ U.output)
first-output-rel m = subst (λ z → K.M⁰ (E.fsn (AL.S 2) 0) (proj₁ z))
  (sym U.row) (K.G⁰.m-cum (λ n → U.Inner.out (U.Inner.chain n)) 1 m)

first-value : FirstChild → (h : SI.E.HC (AL.S 1)) →
  SI.E.tree h ≼ K.readRW (proj₁ U.output)
first-value m h = ≼-trans (XI.tree-back h)
  (K.lower⁰ (subst (λ t → K.M⁰ t (proj₁ U.output)) OL.fs0
    (first-output-rel m)) (XI.back h))
```
