# 原 rowB 整条实际反馈与完整输出均有 SV

本篇是原运行器的生成性定理。所有 HtB、源高度、实际环境与外目标
共同界均保留；没有另造闭项或重设初始坐标。轨道直接来自原 run 的
ActualTrace。它还不等于旧 NC 与新轨道的逐步嵌入或最终高值下界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildBaseOrbit (S : HtB) where
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ordˢ; Ωˢ; toZ)
open import OCF.Free.Floor using (Ev; fz; fk; _⊔_; Bd; Fc; FB; iF; bound)
open import OCF.Free.Tree using (Fl)
open import OCF.Free.Aux using (Mlev)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.TotalValueBuildStrict using (SV; svz; svs; Pos; ps)
open import OCF.Align.TotalValueBuildBaseStrict S using (callback-sv)
open import OCF.Align.TotalValueBuildRunStrict using (positive)
open import OCF.Align.TotalValueBaseLower S using (omega-lower)
open import OCF.Align.TotalValueBuildTypedValue using (1≼ψ⁰)
open import OCF.Align.TotalValueNegBound using (bound-one)
open import OCF.Align.ValueJudgeBase using (≼-trans)
import OCF.Align.OrdLabZLevel as P
import OCF.Align.TotalValueBuildTraceStrict as T
import OCF.Free.TotalOrbitRun as R

module Actual {m w ℓ} (ok : Ok w) (env : Eh h₀ m w (κ Fl))
  (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) where

  F = bound (fz ⊔ fk zero) ev p
  c : Ordᴵ
  c = Bd F
  seed : Ordˢ zero
  seed = ψ̄ᵠ ok env (tl {m = m} {c = zero} {χ = κ Fl}
    (fz ⊔ fk zero) proj₂ (Ωˢ (suc zero))) ev p
  next : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero
  next η e = ψ̄ᵠ ok env
    (tl {m = m} {c = zero} {χ = κ Fl} (fz ⊔ fk η)
      (λ v q → proj₂ v (suc q)) (Ωˢ η))
    (evη fz F η e) (lim 0 (iF F))

  c-sv : SV c
  c-sv = subst SV (sym (bound-one ev p)) (svs svz)
  c-pos : Pos c
  c-pos = subst Pos (sym (bound-one ev p)) ps
  seed-sv : SV (R.run (toZ seed))
  seed-sv = callback-sv (svs svz) ps proj₂ ok env ev p
  next-sv : ∀ η e → SV η → Pos η → SV (R.run (toZ (next η e)))
  next-sv η e s pos = callback-sv s pos (λ v q → proj₂ v (suc q))
    ok env (evη fz F η e) (lim 0 (iF F))
  next-positive : ∀ η e → Σ Ordᴵ (λ d → d ≺ᴵ R.run (toZ (next η e)))
  next-positive η e = positive (≼-trans (1≼ψ⁰ (P.Ω η))
    (omega-lower (λ v q → proj₂ v (suc q)) ok env
      (evη fz F η e) (lim 0 (iF F))))

  module Full = T.Whole c (toZ seed) (λ η e → toZ (next η e))
    (toZ seed) (λ η e → toZ (next η e)) c-sv c-pos seed-sv
    next-sv seed-sv next-sv (λ η e s pos → next-positive η e)

  open Full public using (η; bound; start; step; coordinate-sv; coordinate-pos; computation)

  actual-whole : SV (R.run (toZ (ψ̄ᵠ ok env (rowB {m = m}) ev p)))
  actual-whole = Full.whole-sv

-- 默认实际环境亦全高度填写；非仅某一有限源。
module Default (m : Ht) = Actual {m = m} ok₀ (λ i h r → ok₀ i)
  (tt , (λ { zero → zero })) zero
```
