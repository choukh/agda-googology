# 实际孩子的槽位与保持目标
验收文件；第零步的类型、实际输入与内槽链步进已编译，零层保持目标未实填。
只量化实际内链点；继承底取 YiE4ParamInner 的原实例，不换标准底。
来源：YiM2Local 的实际输入、地板与内链关系；槽位类型据 YiGIRel。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVLActual where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Lean.YiAZStart as A
import OCF.Lean.YiAZLocal as Z
import OCF.Lean.YiM2Local as M
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGTGen as GT
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiCNAccept as CN
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLean3Base using (Ωt-mono)

p : B.Pos A.N.h
p = inj₁ (inj₁ tt)
slot-level : B.at A.N.h p ≡ B.tw 1
slot-level = refl
slot-path : P.posW A.N.h p ≡ P.ink P.self
slot-path = refl
cofinality : E.cof M.arg ≡ E.cΩ M.ν
cofinality = refl
slot-nu : GR.Nu A.N.h p M.ν
slot-nu = CN.rd1

Input : Set
Input = GR.R A.N.h M.arg (proj₁ (O.Ωt A.N.h))
input : Input
input = M.shaped-input
Zero : Set
Zero = Σ (H.M⁰ (Z.S 2) (proj₁ A.D.output)) H.Exᴴ
KeepActual : Set
KeepActual = Input → Zero

start : GR.Low A.N.h p (M.γ 0) (A.N.Inner.chain 1)
start = M.inner-chain-r 0 0
step : ∀ n → GR.Low A.N.h p (M.γ n) (A.N.Inner.chain (suc n))
  → GR.R A.N.h (E.fsT M.arg (M.γ n)) (A.N.Inner.g (A.N.Inner.chain (suc n)))
  → GR.Low A.N.h p (M.γ (suc n)) (A.N.Inner.chain (suc (suc n)))
step n r child = M.inner-chain-r (suc n) (suc n)

child-source : ∀ n q → GR.R (A.N.a (A.N.Inner.chain q)) (E.fsT M.arg (M.γ n))
  (proj₁ (O.Ωt (A.N.a (A.N.Inner.chain q))))
child-source n q = GT.closeᴿ (A.N.a (A.N.Inner.chain q)) (Ωt-mono (M.γ-bound n)) (M.inner-input (A.N.Inner.chain q))
source : ∀ n q → GR.R A.N.h (E.fsT M.arg (M.γ n)) (A.N.Inner.g (A.N.Inner.chain q))
source n q = subst (λ g → GR.R A.N.h (E.fsT M.arg (M.γ n)) (g (A.N.Inner.chain q)))
  (sym A.N.Inner.g-eq) (H.mU H.mz (child-source n q))
actual-chain : ∀ n → GR.Low A.N.h p (M.γ n) (A.N.Inner.chain (suc n))
actual-chain zero = start
actual-chain (suc n) = step n (actual-chain n) (source n (suc n))
```
