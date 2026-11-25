# Ω₂里程碑的实际部分和拼接义务
验收文件；只对实际YiE4部分和P陈述，assemble2保留逐项前提，未完成Ω₂值界。
第0项已实填；fs1给第1项的具体形状，FirstRow未实填，不作否定。
来源：旧ValLabPos.Chain.vv-chain的错位拼接；证明直接复用当前K.mL/mw/lower⁰与YiAZLocal.S1-low。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOLMilestone where
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Lean.YiAZStart as AZ
import OCF.Lean.YiAZLocal as AL
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiExInst as XI
import OCF.Align.EboLeanDef as E
open import OCF.Align.Value using (_≼_; ≼-trans)
Rows2 : Set
Rows2 = ∀ n → Σ ℕ λ q → K.M⁰ (E.fsn (AL.S 2) n) (AZ.P q)
assemble2 : Rows2 → (h : SI.E.HC (AL.S 2)) → SI.E.tree h ≼ K.readRW (proj₁ AZ.D.output)
assemble2 rows h = subst (λ x → SI.E.tree h ≼ K.readRW (proj₁ x)) (sym AZ.whole-row)
  (≼-trans (XI.tree-back h) (K.lower⁰ (K.mL refl (λ n → K.mw (proj₂ (rows n)) (B.◃l (proj₁ (rows n))))) (XI.back h)))
fs0 : E.fsn (AL.S 2) 0 ≡ AL.S 1
fs0 = refl
zero-row : Σ ℕ λ q → K.M⁰ (E.fsn (AL.S 2) 0) (AZ.P q)
zero-row = 0 , CS.sem→M⁰ (XI.back (AL.hc-S 1)) (AZ.P 0)
  (≼-trans (SI.toL-tree (XI.back (AL.hc-S 1))) (AL.S1-low (SI.conv (XI.back (AL.hc-S 1)))))
fs1 : E.fsn (AL.S 2) 1 ≡ E.ψ [] (E.Ωt (E.ψ (E.natT 1) (E.ΩTower 2) ∷ [])) ∷ []
fs1 = refl

FirstRow : Set
FirstRow = Σ ℕ λ q → K.M⁰ (E.fsn (AL.S 2) 1) (AZ.P q)
```
