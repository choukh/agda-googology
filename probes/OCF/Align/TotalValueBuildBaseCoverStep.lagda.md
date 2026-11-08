# 真实 base 全轨道的输入嵌入消费及完整输出包含

本篇固定原 rowB 的真实私有轨道。已知某旧 NC 层号嵌入第 k 个实际
坐标时，整个下一旧反馈输出进入实际输出及下一坐标；也进入原节点
完整部分和极限。所有 n/k 均量化，尚需另一条定理产生这些嵌入。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildBaseCoverStep (S : HtB) where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Floor using (Ev; iF)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.TotalValueBuildIf using (BoundedEmbedding)
open import OCF.Align.TotalValueBuildStrict using (module N)
open import OCF.Align.TotalValueBuildBaseConsumer S using (base-callback)
open import OCF.Align.TotalValueBaseLower S using (omega-lower)
open import OCF.Align.TotalValueBuildTypedValue using (1≼ψ⁰)
open import OCF.Align.TotalValuePureLower using (right-add; part)
open import OCF.Align.ValueJudgeBase
import OCF.Align.OrdLabZLevel as P
import OCF.Align.TotalValueBuildBaseOrbit S as Orbit
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A

module Actual {m w ℓ} (ok : Ok w) (env : Eh h₀ m w (κ Fl))
  (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) where
  module B = Orbit.Actual ok env ev p

  initial : N.γ zero ≼ A.read (B.η zero)
  initial = subst (λ a → N.γ zero ≼ A.read a) (sym B.start)
    (≼-trans (≼-trans (1≼ψ⁰ (P.Ω (suc zero)))
      (omega-lower proj₂ ok env ev p)) (right-add B.c (R.run (toZ B.seed))))

  emitted : ∀ n k → BoundedEmbedding (N.L n) (B.η k) →
    N.γ (suc n) ≼ A.read (R.run (toZ (B.next (B.η k) (B.bound k))))
  emitted n k e = base-callback e ok env
    (evη _ B.F (B.η k) (B.bound k)) (lim 0 (iF B.F))

  next-coordinate : ∀ n k → BoundedEmbedding (N.L n) (B.η k) →
    N.γ (suc n) ≼ A.read (B.η (suc k))
  next-coordinate n k e = subst (λ a → N.γ (suc n) ≼ A.read a)
    (sym (B.step k)) (≼-trans (emitted n k e) (right-add B.c _))

  whole : ∀ n k → BoundedEmbedding (N.L n) (B.η k) →
    N.γ (suc n) ≼ A.read (R.run (toZ (ψ̄ᵠ ok env (rowB {m = m}) ev p)))
  whole n k e = ≼-trans (emitted n k e)
    (≼-trans (part B.Full.outputs (suc k))
      (≼-trans (≼l (suc k) (≼-refl _))
        (≅→≼ (A.read-cong (≅ᴵ-sym B.Full.Actual.shape)))))
```
