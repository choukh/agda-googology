# 输出驱动：同类型全槽运行的最小合同

这里不把一个固定源的有界目标族补成全目标族。对于每个塔 `V`，
把它作为底种类结构，运行其完整 `XSof V` 地板；原比较仍只在
`V` 内同一个合法界中进行。这样输出逐字属于 `HB V`，可写回该塔的界槽。

合同的源保留原 `gtX` 全部组件。零高度只是跨底运行的目标，
不是把源替换为零树或单后继样本。仍使用原 `Er` 及 `ΦX` 的代表分支；
这两项原有信息损失没有被世界增长消除，也不在这里声称 EBO 值界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.OutputDrivenIf where

open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdTw using (XSof; ιK; gtX)
open import OCF.Lean.ThirdPS using (PH)
import OCF.Lean.ThirdSan as San
import OCF.Lean.ThirdX as Cross

module Whole (V : KS) (w : Wd V) (lw : LgW V w)
  (fb : HB V) (normal : HB V → HB V)
  (normal-legal : ∀ a → LgB (normal a)) where
  module S = San V w lw fb
  module X = Cross V w lw S.Er normal normal-legal
    (bot V) (λ κ → botBd V κ w)

  source : HB (XSof V)
  source = hΩ ιK (gtX V fb)

  record WholeRun : Set where
    field
      source-path : ∀ B → hs hz ⊲[ w ] B → PH X.PSX B source

    output : HB V
    output = proj₁ (X.ΦX hz (hs hz) tt (hsuc hself)
      (fb , S.gd-z fb) source (source-path (hs hz) hself))
```

`source-path` 必须由原全地板实填；`output` 没有任意常值字段。
下一文件将对任意底、世界与种子实填，再把 `V=Tw(Sb n)m`
逐槽实例化。尚未给出完整下降或值验收。
