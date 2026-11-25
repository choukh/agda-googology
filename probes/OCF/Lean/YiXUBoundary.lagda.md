# 旧读回坐标不能覆盖下一实际孩子
验收文件；编译否定：a (Inner.chain 1) 不满足 NoΩ，也不与任一旧 h₁ x 层号保持 RelL。
此否定只限制 YiMTRel 与 YiXVReadIndex 的直接坐标接线；不否定值上界、里程碑或研究路线。
来源：YiC0Local.neck-shape 给实际 Ω 形状；readback-NoΩ 对旧零层源递归；入口 no-readback-coordinate。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXUBoundary where
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiC0Local as C
open import OCF.Lean.YiNRHit using (NoΩ)
open import OCF.Lean.YiBRRel using (RelL; lz; lS; lL)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLSTw1 as T

first-NoΩ : (ℓ : B.L) → NoΩ ℓ → NoΩ (C.first ℓ)
first-NoΩ B.zero h = h
first-NoΩ (B.nd B.sS a) h = h tt
first-NoΩ (B.nd B.sL a) h = h 0
first-NoΩ (B.nd (B.sΩ k) a) ()

no-next-NoΩ : NoΩ (U.a (U.Inner.chain 1)) → ⊥
no-next-NoΩ h = subst NoΩ C.neck-shape
  (first-NoΩ (C.first (C.first C.ℓ₁))
    (first-NoΩ (C.first C.ℓ₁)
      (first-NoΩ C.ℓ₁ (subst (λ c → NoΩ (U.a c)) (sym C.c₁-eq) h))))

readback-NoΩ : (x : S.Tr S.zero) {ℓ : B.L} → RelL ℓ (T.h₁ x) → NoΩ ℓ
readback-NoΩ S.zero lz = tt
readback-NoΩ (S.suc x) (lS r) tt = readback-NoΩ x r
readback-NoΩ (S.lim f a) (lL r) n = readback-NoΩ (f n) (r n)
readback-NoΩ (S.Ω () g) r
readback-NoΩ (S.up x () y e) r

no-readback-coordinate : (x : S.Tr S.zero) → RelL (U.a (U.Inner.chain 1)) (T.h₁ x) → ⊥
no-readback-coordinate x r = no-next-NoΩ (readback-NoΩ x r)
```
