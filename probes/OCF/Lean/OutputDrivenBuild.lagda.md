# 全高源实际运行：不补目标，不裁源

对任意底 `V` 实填共享全源证书。这里的 `pk` 是显式参数，
之后取当前世界中每个种类的实际最大可入坐标；共享接口的 `bot`
版本只作最小校准，不规定最终选择。源路径不依赖这一选择。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.OutputDrivenBuild where

open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf
open import OCF.Lean.ThirdTw using (XSof; Ix; FX; ιK; gtX; topT)
open import OCF.Lean.ThirdPS
import OCF.Lean.ThirdSan as San
import OCF.Lean.ThirdX as Cross
import OCF.Lean.ThirdFold as Fold
import OCF.Lean.OutputDrivenIf as If

module Whole (V : KS) (w : Wd V) (lw : LgW V w)
  (fb : HB V) (normal : HB V → HB V)
  (normal-legal : ∀ a → LgB (normal a))
  (pk : (κ : K V) → E V κ) (pk-bd : ∀ κ → Bd V κ (pk κ) w) where
  module I = If.Whole V w lw fb normal normal-legal
  module S = San V w lw fb
  module F = Fold V w lw
  module X = Cross V w lw S.Er normal normal-legal pk pk-bd

  component : ∀ c W → hs c ⊲[ w ] W → ∀ x → F.Gd (hs c) x →
    PH X.PSX W (ι {Ix V} {FX V} (inj₂ c) x)
  component c W q hz p = tt
  component c W q (hs x) p = component c W q x p
  component c W q (hl f) p = λ k → component c W q (f k) (p k)
  component c W q (hΩ κ g) (pos , pg) = (q , pos) , λ e a → component c W q (g e) (pg e a)

  tower-floor : ∀ c → F.Gd (hs c) (topT V fb (hs c))
  tower-floor c = tt , λ e a → S.Gd-up c e a

  source-branches : ∀ y W → y ⊲[ w ] W → PH X.PSX W (gtX V fb y)
  source-branches hz W q = tt
  source-branches (hs c) W q = PH-⊞ X.PSX (gtX V fb c)
    (ι {Ix V} {FX V} (inj₂ c) (topT V fb (hs c)))
    (source-branches c W (⊲ᴮ-tr {V} (hsuc hself) q))
    (component c W q _ (tower-floor c))
  source-branches (hl f) W q = λ k → source-branches (f k) W
    (⊲ᴮ-tr {V} (hlim k hself) q)
  source-branches (hΩ κ h) W q = tt , λ e a → source-branches (h e) W
    (⊲ᴮ-tr {V} (hLim a hself) q)

  source-path : ∀ B → hs hz ⊲[ w ] B → PH X.PSX B I.source
  source-path B o = o , λ y a → source-branches y (hs y) (hsuc hself)

  output : HB V
  output = proj₁ (X.ΦX hz (hs hz) tt (hsuc hself)
    (fb , S.gd-z fb) I.source (source-path (hs hz) hself))

whole : ∀ V w lw fb normal normal-legal → If.Whole.WholeRun V w lw fb normal normal-legal
whole V w lw fb normal normal-legal = record
  { source-path = Whole.source-path V w lw fb normal normal-legal (bot V) (λ κ → botBd V κ w) }
```

`output` 的输入不是地板常量替身，而是 `source` 的完整原回调；
全 `gtX` 证书覆盖后继、可数极限和全部原 Ω 分支。
合法世界和代表坐标是运行环境；它们不改源，也没有假设源树处处合法。
