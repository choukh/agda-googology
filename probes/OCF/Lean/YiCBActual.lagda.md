# 干净对象的实际孩子计算与链点粗界
验收文件；编译定理：回灌进入同一标准底孩子，chain 1 的树侧后继值不高于独立 Ω₂ 树。
此界只界第1层链点；未给零层分支的可数记号上界，未判定第0项 ψ₀(Ω_Ω) 或完整目标 ψ₀(Ω_{Ω₂})。
来源：计算复用 YiUTTwoLocal.feed0/out-child；上界用 YiVWVal.≼-emb 与值序构造子。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCBActual where
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiUTTwoLocal as UL
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiVWVal as V

child0 : U.a B.zero ≡ H.fn 3
child0 = refl
out0 : U.Inner.out B.zero ≡ MT.ψ₀ᶻ (H.fn 3) (proj₂ U.o₂ B.zero) (proj₁ (O.Ωt (H.fn 3)))
out0 = UL.out-child B.zero
chain1 : U.Inner.chain 1 ≡ proj₁ (TB.ψ (H.fn 3) (proj₂ U.o₂ B.zero) (MT.rbᶻ (H.fn 3))
  (F.B₀ (H.fn 3)) K.one (P.inu (λ _ → P.inc tt P.self)) (O.Ωt K.one) (proj₁ (O.Ωt (H.fn 3))))
chain1 = UL.feed0

opaque
  unfolding U.Inner.feed U.Inner.g
  feed-child : ∀ d → U.Inner.feed d ≡ proj₁ (TB.ψ (U.a d) (proj₂ U.o₂ d) (MT.rbᶻ (U.a d))
    (F.B₀ (U.a d)) K.one (P.self P.∙ proj₂ (proj₁ U.o₂) d) (O.Ωt K.one) (proj₁ (O.Ωt (U.a d))))
  feed-child d = refl
child1 : U.a (U.Inner.chain 1) ≡ B.nd B.sS (λ _ → K.two B.⊕ (B.zero B.⊕ B.↑ K.one (U.Inner.chain 1)))
child1 = refl

private
  zero-left : ∀ {ℓ} (v : V.V ℓ) → v V.≼ V.zero V.⊹ v
  zero-left V.zero = V.z≼
  zero-left (V.suc v) = V.s≼s (zero-left v)
  zero-left (V.lim f) = V.l≼ (λ n → V.≼l n (zero-left (f n)))
  zero-left (V.Ω p g) = V.Ω≼ (λ z → V.≼Ω z (zero-left (g z)))
  -- perf: C-9，证明在变量上进行，实际链点只在最后实例化。
  below-two : (x : B.Tr K.one) → V.suc (V.val K.one x) V.≼ V.val K.two (proj₁ (O.Ωt K.two))
  below-two x = V.≼Ω x (V.≼-trans
    (V.≼-emb K.two tt (V.suc (V.val K.one x)))
    (zero-left (V.emb K.two tt (V.suc (V.val K.one x)))))

chain1-upper : V.suc (V.val K.one (U.Inner.chain 1)) V.≼ V.val K.two (proj₁ (O.Ωt K.two))
chain1-upper = below-two (U.Inner.chain 1)
```
