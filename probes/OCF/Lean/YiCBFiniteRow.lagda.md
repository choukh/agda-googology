# 实际首分支的有限层累计行
验收文件；row 是公共 Inner.out zero 的完整等式；feed-zero/out-zero 是内部首项计算测试。
未给这些累计部分和的独立可数参照上界，不判定公共 output 的值。
来源：YiCBActual.out0 接原对象；零层结点行复用 YiE4Cut20.row0；函数出生处封装并给定义等式。
```agda
{-# OPTIONS --safe --without-K --lossy-unification  #-}
module OCF.Lean.YiCBFiniteRow where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiCBActual as CB
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiE4Cut20 as C

opaque
  branch : B.Tr K.two → B.Tr (H.fn 3)
  branch c = B.up B.zero tt (B.suc c) (O.z◃ c B.◃s)
  branch-eq : branch ≡ (λ c → B.up B.zero tt (B.suc c) (O.z◃ c B.◃s))
  branch-eq = refl
  feed : B.Tr K.two → B.Tr K.two
  feed c = proj₁ (TB.ψ (H.fn 3) (proj₂ U.o₂ B.zero) (MT.rbᶻ (H.fn 3)) (F.B₀ (H.fn 3))
    K.two (P.inc tt P.self) (O.Ωt K.two) (branch c))
  feed-eq : feed ≡ (λ c → proj₁ (TB.ψ (H.fn 3) (proj₂ U.o₂ B.zero) (MT.rbᶻ (H.fn 3)) (F.B₀ (H.fn 3))
    K.two (P.inc tt P.self) (O.Ωt K.two) (branch c)))
  feed-eq = refl
  out : B.Tr K.two → O.Tr⁺ B.zero
  out c = MT.ψ₀ᶻ (H.fn 3) (proj₂ U.o₂ B.zero) (branch c)
  out-eq : out ≡ (λ c → MT.ψ₀ᶻ (H.fn 3) (proj₂ U.o₂ B.zero) (branch c))
  out-eq = refl
chain : ℕ → B.Tr K.two
chain = O.iter feed B.zero
opaque
  unfolding branch feed out
  row : U.Inner.out B.zero ≡ O.limc⁺ (λ n → out (chain n))
  row = trans CB.out0
    (C.row0 {X = B.Tr K.two} {z = B.zero}
      (F.kp (H.fn 3) (proj₂ U.o₂ B.zero) (inj₂ (tt , inj₁ tt)) (P.z≤ (H.fn 3))) out feed)
opaque
  unfolding branch feed out
  feed-zero : feed B.zero ≡ proj₁ (O.next⁺ (O.Ωt K.two))
  feed-zero = refl
  out-zero : proj₁ (out B.zero) ≡ proj₁ (O.next⁺ (O.Ωt B.zero))
  out-zero = refl
```
