# 换基干净对象的里程碑两项目标
验收文件；编译目标类型与参照域非空，不宣称两项值界。
FirstRow 取自 YiUTTwoLocal，RowOneAtTwo 取自 YiC0Next，输出改为已接收的 YiBSClean。
目标基本列与 HC 证书复用 YiBSAccept；基本列公式复用 YiOLMilestone。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBTGoals where
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiBSClean as U
import OCF.Lean.YiBSAccept as A
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiOLMilestone as OM
import OCF.Align.EboLeanDef as E
open import OCF.Align.Value using (_≼_)
P : ℕ → B.Tr B.zero
P = O.cum (λ n → proj₁ (U.Inner.out (U.Inner.chain n)))
row₀ row₁ : E.T
row₀ = A.Target 0
row₁ = A.Target 1
row₁-shape : row₁ ≡ E.ψ [] (E.Ωt (E.ψ (E.natT 1) (E.ΩTower 2) ∷ [])) ∷ []
row₁-shape = OM.fs1
FirstRow : Set
FirstRow = Σ ℕ λ q → K.M⁰ row₀ (P q)
RowOneAtTwo : Set
RowOneAtTwo = K.M⁰ row₁ (P 2)
RowOne : Set
RowOne = Σ ℕ λ q → K.M⁰ row₁ (P q)
Value0 Value1 : Set
Value0 = (h : SI.E.HC row₀) → SI.E.tree h ≼ K.readRW (proj₁ U.output)
Value1 = (h : SI.E.HC row₁) → SI.E.tree h ≼ K.readRW (proj₁ U.output)
nonempty₀ : SI.E.HC row₀
nonempty₀ = A.nonempty 0
nonempty₁ : SI.E.HC row₁
nonempty₁ = A.nonempty 1
```
