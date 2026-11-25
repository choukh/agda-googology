# 干净候选的初项与未填目标
验收文件（读记号）；编译定理：首链点有 ψ₁(Ω₃) 关系，输出有 ψ₀(Ω₃) 的全 HC 下界。
来源：YiUTTwoLocal 的有限层实例，折叠改用 YiBSFam；出口复用 YiKVRel.lower⁰。
RowGoal、Value0、Value1 只是待证类型，nonempty 证明参照 HC 域非空；未证里程碑的基本列第 0、1 项。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBSAccept where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiBSFam as LF
import OCF.Lean.YiBSClean as U
open import OCF.Lean.YiRBFam using (tu; can; pu)
open import OCF.Lean.YiCLLow using (s0; ss)
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiExInst as XI
import OCF.Lean.YiAZLocal as AL
import OCF.Lean.YiRefTw2 as RT
import OCF.Lean.YiUTTwoLocal as UL
open import OCF.Align.Value using (_≼_; ≼-trans)
first : H.M 1 (E.ψ (E.natT 1) (E.Ωt (E.natT 3)) ∷ []) (U.Inner.chain 1)
first = subst (H.M 1 (E.ψ (E.natT 1) (E.Ωt (E.natT 3)) ∷ [])) (sym (U.feed-child B.zero))
  (LF.sΩ-LF {n = 2} {j = 1} (proj₂ U.o₂ B.zero) (proj₂ U.r₂ B.zero) (LF.tu (LF.can (ss s0)))
    (F.B₀ (U.a B.zero)) (O.Ωt U.one) (λ i u → K.⊴r) (H.Mβ 0))
small : E.T
small = E.ψ [] (E.Ωt (E.natT 3)) ∷ []
zero-rel : K.M⁰ small (proj₁ (U.Inner.out B.zero))
zero-rel = subst (λ z → K.M⁰ small (proj₁ z)) (sym (U.out-child B.zero))
  (LF.sΩ-LF {n = 2} {j = 0} (proj₂ U.o₂ B.zero) (proj₂ U.r₂ B.zero) (LF.tu (LF.pu (LF.pu (LF.can s0))))
    (F.B₀ (U.a B.zero)) (O.Ωt B.zero) (λ i u → K.⊴r) (K.m1 refl K.mz))
small-rel : K.M⁰ small (proj₁ U.output)
small-rel = subst (λ z → K.M⁰ small (proj₁ z)) (sym U.row)
  (K.G⁰.m-cum (λ n → U.Inner.out (U.Inner.chain n)) 0 zero-rel)
small-value : (h : SI.E.HC small) → SI.E.tree h ≼ K.readRW (proj₁ U.output)
small-value h = ≼-trans (XI.tree-back h) (K.lower⁰ small-rel (XI.back h))
small-hc : SI.E.HC small
small-hc = UL.small-hc
Target : ℕ → E.T
Target n = E.fsn (AL.S 2) n
RowGoal : ℕ → Set
RowGoal n = K.M⁰ (Target n) (proj₁ U.output)
Value0 Value1 : Set
Value0 = (h : SI.E.HC (Target 0)) → SI.E.tree h ≼ K.readRW (proj₁ U.output)
Value1 = (h : SI.E.HC (Target 1)) → SI.E.tree h ≼ K.readRW (proj₁ U.output)
nonempty : ∀ n → SI.E.HC (Target n)
nonempty n = SI.conv (RT.hω-inv (XI.back (AL.hc-S 2)) refl n)
```
