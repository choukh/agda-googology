# 新表的实际闭项接线
验收文件；Missing 与新表实际 q1 的全 HC 值界互推；值界未填。
来源：YiE4Default 的变量接线证明，改为 YiCWActual；仅复用其 Bound/move-bound 通用输运。
FirstAtNew 的链与输出均为 YiCWActual，不接旧 FR.Step。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiATWire where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
import OCF.Lean.YiCWTable as CW
import OCF.Lean.YiCWActual as C
import OCF.Lean.YiE4Param as R
import OCF.Lean.YiE4ParamFrame as V
import OCF.Lean.YiE4Objects as A
import OCF.Lean.YiE4Base as Q
import OCF.Lean.YiE4Frame as W
import OCF.Lean.YiE4Default as DF
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiLBStart as LS
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiKVRel as K
open import OCF.Align.Value using (_≼_)
module D = R.At CW.rbΛ
module U = V.For CW.rbΛ
opaque
  unfolding D.FΛ D.pre D.baseᴱ D.betaᴱ D.Step.g D.Step.feed D.Step.out
  pre-eq : ∀ n → D.pre n ≡ C.pre n
  pre-eq zero = refl
  pre-eq (suc n) = refl
  base-eq : ∀ n → D.baseᴱ n ≡ C.baseᴱ n
  base-eq n = cong (λ x → λ i u → TB.ψ B.Λ P.Ok-Λ CW.rbΛ (F.B₀ B.Λ) i (P.inc n u) (O.Ωt i) x) (pre-eq n)
  beta-eq : ∀ n → D.betaᴱ n ≡ C.betaᴱ n
  beta-eq n = cong (λ x → TB.ψ B.Λ P.Ok-Λ CW.rbΛ (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero) x) (pre-eq n)
  g-eq : ∀ n → D.Step.g n ≡ C.Step.g n
  g-eq n = refl
  feed-eq : ∀ n → D.Step.feed n ≡ C.Step.feed n
  feed-eq n = refl
  out-eq : ∀ n → D.Step.out n ≡ C.Step.out n
  out-eq n = refl
chain-eq : ∀ n q → D.Step.chain n q ≡ C.Step.chain n q
chain-eq n q = cong (λ f → O.iter f B.zero q) (feed-eq n)
opaque
  output-new : D.output ≡ C.Step.out 2 (C.Step.chain 2 1)
  output-new = trans U.output-chain (trans (cong (λ f → f (D.Step.chain 2 1)) (out-eq 2))
    (cong (C.Step.out 2) (chain-eq 2 1)))
OriginalAtOne : Set
OriginalAtOne = DF.Bound LS.target (C.Step.out 2 (C.Step.chain 2 1))
from-original : OriginalAtOne → U.Missing
from-original low h = subst (λ x → x ≼ K.readRW (proj₁ (Q.collapse D.ctx D.β)))
  (sym (A.reference-eq h))
  (DF.move-bound (sym A.target-eq) (trans (sym output-new) D.output-eq) low h)
to-original : U.Missing → OriginalAtOne
to-original low = DF.move-bound A.target-eq (trans (sym D.output-eq) output-new)
  (λ h → subst (λ x → x ≼ K.readRW (proj₁ (Q.collapse D.ctx D.β))) (A.reference-eq h) (low h))
FirstAtNew : Set
FirstAtNew = Data.Product.Σ ℕ λ q → (h : SI.E.HC LS.target) → SI.E.tree h ≼ K.readRW (proj₁ (C.Step.out 2 (C.Step.chain 2 q)))
module Use (low : U.Missing) where
  module I = U.Use low
  first-at-one : FirstAtNew
  first-at-one = W.at-one LS.target (λ q → C.Step.out 2 (C.Step.chain 2 q)) D.output output-new I.target-low
```
