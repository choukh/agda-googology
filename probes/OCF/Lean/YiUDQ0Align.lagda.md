# 原 q=0 的内链与参照配对
验收文件；编译否定：实际第 n 个部分和不能配给 ψ₀(Ω_{Ω+1}) 的第 n 个基本列项，首项已失败。
未证或否定原 q=0 的独立记号上界；不判定 FirstMissing，不改变底、起点、折叠或表。
来源：内链直接展开 YiTBRow 配 rbᶻ；严格值桥用 YiKDStep/YiKQSuff/YiKCSem，起点界用 YiFRStations.k2，参照用 YiRefTw2。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUDQ0Align where
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Empty using (⊥)
import OCF.Align.EboLeanDef as E
import OCF.Align.Level as L
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiFRStations as FS
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiKQSuff as Q
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiKDStep as KD
import OCF.Lean.YiNFO as NF
import OCF.Lean.YiRefTw2 as R
open import OCF.Align.Value using (_≼_; s≼s; ≼-trans)

module Rows (A : F.Base (B.tw 2)) (β : O.Tr⁺ B.zero) where
  child : B.Tr (B.tw 1) → B.L
  child c = B.tw 1 B.⊕ B.↑ (B.tw 1) c
  feed : B.Tr (B.tw 1) → B.Tr (B.tw 1)
  feed c = proj₁ (TB.ψ (child c) (proj₂ (P.Ok-tw 2) c) (MT.rbᶻ (child c))
    (λ i u → A i (P.inc c u)) (B.tw 1) (P.self P.∙ P.lift (B.tw 1) (B.↑ (B.tw 1) c))
    (A (B.tw 1) (P.ink P.self)) (proj₁ (O.Ωt (child c))))
  chain : ℕ → B.Tr (B.tw 1)
  chain = O.iter feed B.zero
  row : ℕ → O.Tr⁺ B.zero
  row n = TB.ψ (child (chain n)) (proj₂ (P.Ok-tw 2) (chain n)) (MT.rbᶻ (child (chain n)))
    (λ i u → A i (P.inc (chain n) u)) B.zero (P.z≤ (child (chain n))) β
    (proj₁ (O.Ωt (child (chain n))))
  raw : O.Tr⁺ B.zero
  raw = TB.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2)) A B.zero (P.z≤ (B.tw 2)) β (proj₁ (O.Ωt (B.tw 2)))
  raw-form : proj₁ raw ≡ proj₁ (O.limc⁺ row)
  raw-form = refl

A₀ : F.Base (B.tw 2)
A₀ i u = GI.baseᴱ 3 i (P.inc B.zero u)
module Actual = Rows A₀ (GI.betaᴱ 3)

actual-form : proj₁ (FR.Step.out 2 (FR.Step.chain 2 0)) ≡ proj₁ Actual.raw
actual-form = refl

row₀-strict : (A : F.Base (B.tw 2)) (β : O.Tr⁺ B.zero) →
  L.suc (K.readRW (proj₁ β)) ≼ K.readRW (proj₁ (Rows.row A β 0))
row₀-strict A β = ≼-trans (s≼s (Q.read≤ (proj₁ β)))
  (≼-trans (KD.◃s≼ (TB.mono (B.tw 1) (P.Ok-tw 1) (MT.rbᶻ (B.tw 1))
    (λ i u → A i (P.inc B.zero u)) B.zero (P.z≤ (B.tw 1)) β (proj₂ (O.Ωt (B.tw 1)))))
    (CS.rr≼ (proj₁ (Rows.row A β 0))))

beta3-ref2-lower : (h : E.HC (E.EBOψ 2)) → R.Rt h ≼ K.readRW (proj₁ (GI.betaᴱ 3))
beta3-ref2-lower h = ≼-trans (SI.toL-tree h) (FS.k2 (SI.conv h))

ref-start : E.fsn R.t₊ 0 ≡ E.EBOψ 2
ref-start = refl

start-lower : (h : E.HC R.t₊) → R.Rt (R.hω-inv h refl 0) ≼ K.readRW (proj₁ (GI.betaᴱ 3))
start-lower h = ≼-trans (R.tree-≼ ref-start (R.hω-inv h refl 0)
  (subst E.HC ref-start (R.hω-inv h refl 0)))
  (beta3-ref2-lower (subst E.HC ref-start (R.hω-inv h refl 0)))

no-same-index : (h : E.HC R.t₊) →
  (∀ n → K.readRW (O.cum (λ j → proj₁ (Actual.row j)) n)
      ≼ R.Rt (R.hω-inv h refl n)) → ⊥
no-same-index h mt = NF.s≼-irrefl (R.Rt (R.hω-inv h refl 0))
  (≼-trans (s≼s (start-lower h))
    (≼-trans (row₀-strict A₀ (GI.betaᴱ 3)) (mt 0)))

reference-inhabited : E.HC R.t₊
reference-inhabited = R.h₊
```
