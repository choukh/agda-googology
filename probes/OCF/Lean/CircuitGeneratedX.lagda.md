# 原跨底 ΦX 的全部输出带全分支位置

复用共享 `Full`，证明对象是原 `ThirdX.ΦX`，不改运行器。
对全部底结构、合法世界、洗法、合法化及取枝参数成立；输入只携原 PH，
种子只携原 GT，不额外要求它们 Full。指标旧种类仍按原程序取 `pk`，
所以本结果不表示分支无损，也不给序数值增长。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CircuitGeneratedX where

open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
import OCF.Lean.ThirdFold as TF
import OCF.Lean.ThirdX as TX
import OCF.Lean.CircuitGeneratedBuild as Build
import OCF.Lean.CircuitGeneratedIf as Shared

module At (U : KS) (w : Wd U) (lw : LgW U w) (Sn : TF.San U w lw)
  (leg : HB U → HB U) (Lg-leg : ∀ a → LgB (leg a))
  (pk : (κ : K U) → E U κ) (pk-bd : ∀ κ → Bd U κ (pk κ) w) where
  open TF U w lw
  open F Sn
  open TX U w lw Sn leg Lg-leg pk pk-bd
  module B = Build.At U w lw Sn
  open Shared.At U w lw using (Full)

  outputs : ∀ t M lM pt b h nd → Full t (proj₁ (ΦX t M lM pt b h nd))
  outputs t M lM pt b hz nd = tt
  outputs t M lM pt b (hs h) nd = B.mul _ (outputs t M lM pt b h nd)
  outputs t M lM pt b (hl f) nd = B.sums _
    (λ n → outputs t M lM pt b (f n) (nd n))
  outputs t M lM pt b (hΩ (inj₁ _ , inj₂ _) g) (o , pg) =
    B.node (dcI lM pt o) pt b _ _
      (λ t′ pt′ b′ c _ → outputs t′ (hs (sh₀ M c)) (proj₂ (aS c lM))
        (⊲tr pt′ (↑S c)) b′ (g (sh₀ M c)) (pg _ (aS c lM)))
      (λ i u q x → B.outputs i (wfC i) (lg↓ u lM) t q b (proj₁ x) (proj₂ x))
  outputs t M lM pt b (hΩ (inj₁ _ , inj₁ κ) g) (_ , pg) =
    outputs t M lM pt b (g (pk κ)) (pg _ (pk-bd κ))
  outputs t M lM pt b (hΩ (inj₂ c , κ) g) ((ev , pos) , pg) =
    B.node (dcx lM pt ev (cg (hs c) κ pos)) pt b _ _
      (λ t′ pt′ b′ e pe → outputs t′ M lM pt′ b′ (g e) (pg e pe))
      (λ i u q x → B.outputs i (wfC i) (lg↓ u lM) t q b (proj₁ x) (proj₂ x))
```

`Full` 描述的是每一个实际输出根及全部裸分支，而不是只沿当前可入枝。
它并不取代 `desc` 原本要求的 QL/PH：原 `PH-ΦX↓` 仍负责那条路径链。
未来重用需要另消费 Full 的搬运定理；不能从本结果直接声称终点 EBO 覆盖。

## 原逐底下降的实际入口

所有 `c₀`、所有底号 `n` 的原 `stp` 直接消费上面的统一定理。
`desc` 递归调用的每个 `stp` 都落在此量化域，不限制成某一高度样例。

```agda
open import Data.Nat using (ℕ)
open import OCF.Lean.ThirdTw using (Sb)
open import OCF.Lean.ThirdPS using (PH)
import OCF.Lean.ThirdLeg as Leg
import OCF.Lean.ThirdTm as Tm

module Original (c₀ : Cd) (lc₀ : LgB c₀) where
  module C = Tm.Cn c₀ lc₀
  module W = Leg.W c₀ lc₀

  stp-full : ∀ n (h : HB (Sb (Data.Nat.suc n)))
    (p : PH (C.St.PSX n) (hs hz) h) →
    Shared.At.Full (Sb n) (W.wS n) (W.lwS n) hz (C.stp n h p)
  stp-full n h p = At.outputs (Sb n) (W.wS n) (W.lwS n) (C.St.Er n)
    (Leg.legS n) (Leg.Lg-legS n) (W.pkS n) (W.pk-bd n)
    hz (hs hz) tt (hsuc hself) (C.b₀ n) h p
```
