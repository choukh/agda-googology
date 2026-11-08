# 原全地板不能填这份遗传未来合同

复用已经编译的旧 Gd 非单调输入；不否定原 topT 合法性、Third 整条路线，
也不说明任意未来证书均不可能。否定的正是 CircuitKernelStableIf 的强合同。
高度和世界全部明确合法；AdT 的合同没有要求坐标 LgB，故这里不擅加。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CircuitKernelStableBoundary where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (topT)
import OCF.Lean.ThirdFold as F
import OCF.Lean.CircuitBoundaryGd as N
import OCF.Lean.CircuitKernelStableBuild as B

module Unup (U : KS) (w : Wd U) (lw : LgW U w) where
  open F U w lw using (Gd)
  unup : ∀ m (a : HB (Tw U m)) → Gd (hs m) (up a) → Gd m a
  unup m hz p = tt
  unup m (hs a) p = unup m a p
  unup m (hl f) p = λ n → unup m (f n) (p n)
  unup m (hΩ κ g) p = proj₁ p , λ e a → unup m (g e) (proj₂ p e a)

open B.For N.U

height : HB N.U
height = hs (hs N.m)

legal-height : LgB height
legal-height = N.legal-m

common : HB N.U
common = hs height

legal-common : LgB common
legal-common = legal-height

height-in-common : ∀ {w} → height ⊲[ w ] common
height-in-common = hsuc hself

no-floor : ∀ fb → ¬ Stable height N.w₀ (topT N.U fb height)
no-floor fb p = N.no-new-input
  (Unup.unup N.U N.w₁ N.lw₁ (hs N.m) N.input
    (current height N.lw₁ (up N.input)
      (rebase height (up N.input) (grow N.grow)
        (proj₂ p stay N.lw₀ N.input N.old-input))))
```

topT height 的原最高分支在当前世界接受 N.input，因为其实际 AdT 就是
N.old-input。若给它 Stable，分支 up N.input 可迁到 N.w₁，再投影和
去掉 up 得到原反例已经否定的新 Gd。全过程没有比较裸高度，也没有
给输入假造合法性。此结果说明：这份 Stable 不能直接替代原全地板证书；
不能把高度 1 的正面实例扩读为完整原生成域或 Φ 反馈闭包。
