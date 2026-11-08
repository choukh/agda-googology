# 原生零层直接接已有可数折叠

Native0 字面为 step S⊥；这里实际调用 Fold1 的已有折叠，不另设假想函数。
输入合法条件明确为 Lg*，并给非恒定 Ω 分支实例。一般 LgB 不能擅自换成 Lg*。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedDescentValueBridgeTerminal where
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (top; _≤ᵛ_)
open import OCF.Lean.Fold1Base using (Lg*; ℓT; Wi; lgWi; lg-top*; lgB⊥)
import OCF.Lean.Fold1Fold as F
import OCF.Lean.Fold1 as Closed
import OCF.Lean.NegFold1If as V
open import OCF.Align.BoundedDescentValueBridge using (Native)

terminal : HB (Native hz) → Cd
terminal = F.Φ (hs hz) tt hz (hsuc hself) (Wi (hs hz))

terminal-legal : ∀ x → Lg* (ℓT (hs hz)) x → LgB (terminal x)
terminal-legal x lx = lgB⊥ (terminal x) (F.Φ-lg (hs hz) tt hz (hsuc hself) (lgWi (hs hz)) x lx)

module Inflation = V.Infl terminal refl (λ a → refl) (λ f → refl)
terminal-up-lower : ∀ c → c ≤ᵛ terminal (up c)
terminal-up-lower = Inflation.infl

actual-input : HB (Native hz)
actual-input = top (hs hz)
actual-input-legal : Lg* (ℓT (hs hz)) actual-input
actual-input-legal = lg-top* (hs hz)
actual-terminal : terminal actual-input ≡ Closed.TΩ1
actual-terminal = refl
actual-terminal-legal : LgB (terminal actual-input)
actual-terminal-legal = terminal-legal actual-input actual-input-legal
```

从当前 Source 真正降到 Native0 的跨底运行器尚未写；其输出还须满足本篇
Lg* 条件。`terminal-up-lower` 只针对实际 up 嵌入，不是一般高层值单调。
终点 reference≤ᵛcandidate 要在最终 Cd 候选上另证，不能从本实例的名称推出。
