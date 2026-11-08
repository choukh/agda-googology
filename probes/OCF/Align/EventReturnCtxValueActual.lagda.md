# 原动作及含事件闭包的运行生成实例

对任意原最高层 Λ 及其第 1、2 层路径，原 Run 的 n1 分支就是
Act/Stp。其第二层输出的关系只需状态在同一目标的输出关系。
下面还把这个真正 Run 调用作为 κ₀ 回调，给同时含 nε 与 ni 的
无条件实例；它不声称等于先前那个 κ₁ 首格或整个运行的闭包。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnCtxValueActual where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Align.CumReadCF using (Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead
open import OCF.Align.EventReturnCodeIf using (Shape)
open import OCF.Align.EventReturnCodeBuild using (shape-self)
open import OCF.Align.EventReturnCtxValueIf
open import OCF.Align.EventReturnCtxValueRun
import OCF.Align.EvFoldClosed as Closed

floor₂ : ∀ {a H H′} → R₂ a H H′ (Ωd (hs (hs hz))) (Ωd (hs (hs hz)))
floor₂ = ra ro (ri₁ (λ _ _ _ _ _ _ → ro))

module At (Λ : Ht) (lΛ : LgB Λ)
  (o₁ : ∀ {w} → hs hz ⊲[ w ] Λ) (o₂ : ∀ {w} → hs (hs hz) ⊲[ w ] Λ) where
  module R = Closed.At Λ lΛ o₁ o₂
  open R

  step-related : ∀ {a H H′} (la : Lg a) {Y : St (a , H)} {Y′ : St (a , H′)} →
    R₂ a H H′ (yc (d Y) (τ₂ (la , tt))) (yc (d Y′) (τ₂ (la , tt))) →
    R₂ a H H′ (yc (Stp Y) (τ₂ (la , tt))) (yc (Stp Y′) (τ₂ (la , tt)))
  step-related la r = rl (λ _ → ra floor₂ r)

  run-one : ∀ {a H H′ ly} (ac ac′ : AccY ly) (la : Lg a)
    (ll : LW ly (a , H)) (ll′ : LW ly (a , H′))
    (w : D ly (a , H)) (w′ : D ly (a , H′))
    {Y : St (a , H)} {Y′ : St (a , H′)} →
    R₂ a H H′ (yc (d Y) (τ₂ (la , tt))) (yc (d Y′) (τ₂ (la , tt))) →
    R₂ a H H′
      (yc (Run ac n1 ≤rf (la , tt) ll Act w Y) (τ₂ (la , tt)))
      (yc (Run ac′ n1 ≤rf (la , tt) ll′ Act w′ Y′) (τ₂ (la , tt)))
  run-one ac ac′ la ll ll′ w w′ {Y} {Y′} r = step-related la {Y} {Y′} r

  -- 不读历史或坐标的任意性前提：原运行定义在这个实际生成族中给出。
  generated : ∀ {W} → D₂ W
  generated = nε κ₀ tt (λ q l →
    yc (Run (accᴸ {L = Λ}) n1 ≤rf l hself Act n0 Y₀) (τ₂ l))

  generated-related : ∀ {a H H′} → R₂ a H H′ generated generated
  generated-related = re (λ p s s′ sr la →
    run-one accᴸ accᴸ la hself hself n0 n0 {Y = Y₀} {Y′ = Y₀} rz)

  generated-return : ∀ {a H H′} (la : Lg a) b →
    Shape (rd₂ {a , H′} (la , tt) b (drp₂ (generated {a , H})))
          (rd₂ {a , H} (la , tt) b (generated {a , H}))
  generated-return la b = returned la generated-related b

module Concrete = At Closed.three tt (hsuc (hsuc hself)) (hsuc hself)
```

还缺把真实任意 Run/WalkE 状态递归证明为相关状态。本篇已交的
状态前提有 Y₀ 实例，生成闭包确执行原 Run，未以它替换最终闭项。
