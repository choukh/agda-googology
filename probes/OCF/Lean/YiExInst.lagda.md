# 验收一侧: 封闭的关系上的带条件出口

> 验收文件 (读记号), 不进成品. 判决: 编译定理, 无前提. [YiDCExit](YiDCExit.lagda.md) 的 `exitᴰ` 填出 [YiExSuff](YiExSuff.lagda.md) 的 `Exit₀` (`exitᶠ`, 实例 `gradedᴰ`): 条件是参照项与见证项是标准形、见证项可数.
> 抽象推导读回记号推导, 值不升 (`back`, `tree-back`; 与 `YiAbsSimInst.conv`, `toL-tree` 方向相反).
> 不给出什么: 有限层号上没有塔, 所以这里不给 `Keel⁻` 的实例, 也不给 `ex`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}

module OCF.Lean.YiExInst where

open import Data.Product using (_×_; _,_; proj₁)
open import OCF.Align.EboLeanDef using (HC; h0; h1; hω)
open import OCF.Align.EboLeanTree using (tree)
open import OCF.Align.EboLeanBase using (NF; Ctbl)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-trans)
open import OCF.Lean.YiMonoExit using (toL)
import OCF.Lean.YiAbsSimInst as SI
open import OCF.Lean.YiASIface using (domsᴬ)
open import OCF.Lean.YiDCRel using (gradedᴰ)
open import OCF.Lean.YiDCExit using (exitᴰ)
open import OCF.Lean.YiExSuff

back : ∀ {t} → SI.E.HC t → HC t
back (SI.E.h0 e)   = h0 e
back (SI.E.h1 e h) = h1 e (back h)
back (SI.E.hω e h) = hω e (λ n → back (h n))

tree-back : ∀ {t} (h : SI.E.HC t) → SI.E.tree h ≼ toL (tree (back h))
tree-back (SI.E.h0 e)   = z≼
tree-back (SI.E.h1 e h) = s≼s (tree-back h)
tree-back (SI.E.hω e h) = l≼ (λ n → ≼l n (tree-back (h n)))

open ExSuff gradedᴰ domsᴬ

exitᶠ : Exit₀
exitᶠ = record
  { Ex   = λ {t} r → NF t × NF (proj₁ r) × Ctbl (proj₁ r)
  ; exit = λ r (ns , nt , ct) h → ≼-trans (tree-back h) (exitᴰ r ns nt ct (back h))
  }
```
