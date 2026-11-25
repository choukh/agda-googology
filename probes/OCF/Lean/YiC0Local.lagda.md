# 干净对象内链第 1 点的零层孩子结点
验收文件；编译定理：指定输出接回实际孩子折叠，孩子层沿三个第 0 支到达 neck。
neck 的 Ω 结点以第 0 层树为孩子，孩子层是 two 上方的读回；候选累计编号为 1。
neck-shape 是指定闭项计算测试；公共第 0 项出口见 YiC0Accept，不提供否定。
来源：对象与 out-child 只读复用 YiUTTwo/YiUTTwoLocal，下降路径复用 YiKSDesc。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiC0Local where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiKSDesc as D
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiUTTwoLocal as UL
import OCF.Lean.YiAZLocal as AL
import OCF.Align.EboLeanDef as E
open U using (module Inner)
-- perf: S-1/C-10，实际链点封装后，孩子层只在这个原子上计算。
opaque
  c₁ : B.Tr K.one
  c₁ = Inner.chain 1
  c₁-eq : c₁ ≡ Inner.chain 1
  c₁-eq = refl
ℓ₁ : B.L
ℓ₁ = U.a c₁
child-output : Inner.out c₁ ≡ MT.ψ₀ᶻ ℓ₁ (proj₂ U.o₂ c₁) (proj₁ (O.Ωt ℓ₁))
child-output = UL.out-child c₁
first : B.L → B.L
first B.zero = B.zero
first (B.nd B.sS h) = h tt
first (B.nd B.sL h) = h 0
first (B.nd (B.sΩ k) h) = h B.zero
neck : B.L
neck = B.nd (B.sΩ B.zero)
  (λ d → K.two B.⊕ (B.zero B.⊕ (B.zero B.⊕ B.↑ B.zero (B.suc d))))
-- perf: C-24，只展开到指定 Ω 形状，不展开它的分支函数。
opaque
  unfolding c₁ Inner.feed Inner.g
  neck-shape : first (first (first ℓ₁)) ≡ neck
  neck-shape = refl
  neck-path : D._⊑¹_ neck ℓ₁
  neck-path = D.n¹ (D.n¹ (D.n¹ D.r¹))
candidate : ℕ
candidate = 1
Need : Set
Need = K.M⁰ (E.fsn (AL.S 2) 0) (proj₁ (Inner.out c₁))
CandidateRelation : Set
CandidateRelation = K.M⁰ (E.fsn (AL.S 2) 0) (UL.P candidate)
```
