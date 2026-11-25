# YiUni 否定：结点层不为 0 的 Ω 结点层号上，链的第一步的派发完全推出 LPO

**非验收文件。判决：编译定理，无前提。** `tw 3` 的第 `ηα α` 支是 Ω 结点层号 `Lα α = lc (Tα α) (up (Tα α))` (`branch-tw3`)，结点层 `Tα α`。
把这一支的 `top` 折到 `Tα α` 的任何派发族若在能保留处保留，就推出 LPO (`step-full→lpo`，前提的族如 `step-fold` 总有)；接口形式：第 0 个链点上的 `stp` (`stp-full→lpo`, `stp-full→lpo-dom`)。
`tw 2` 上结点层是 0，`stp` 一律折叠就是完全的 (`tw2-stp-full`)。所以这条只在越过 `tw 2` 后出现。接口 [YiUniIf](YiUniIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUniNegStep where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; Way; fold; Ext; Lv; vΩ)
open import OCF.Lean.YiUniIf using (Uni; Dom; At; IsKeep; Full; StpFull)
open import OCF.Lean.YiUniNegBase
open import OCF.Lean.YiUniNegCmp using (ηα)
open import OCF.Lean.YiUniTw2 using (Tw2)
```

## 1 层号与位置

第 `top` 支是 `upT (Tα α)`，它的第 0 支定义性地是 `tw 2` (因为 `fα α 0` 是 1)；`r₀` 是其中第 `two` 支的根，层号 1。

```agda
Lα : (ℕ → Bool) → LF
Lα α = lc (Tα α) (up (Tα α))

branch-tw3 : ∀ α → upT (up zero (ηα α)) ≡ Lα α
branch-tw3 α = refl

r₀ : ∀ α → Pre (up (Tα α) G.top)
r₀ α = 0 , (two , tt , inj₁ tt)

r₀-lev : ∀ α → lev (up (Tα α) G.top) (r₀ α) ≡ suc zero
r₀-lev α = refl
```

## 2 否定

核心形式不用接口；接口形式的完全性只要求在第 0 个链点 (`cpt V 0`，接口的 `cpt-zero` 说它是 `top`)。

```agda
step-fold : ∀ α → Ext (Tα α) (up (Tα α) G.top)
step-fold α r = fold

step-full→lpo : (s : ∀ α → Ext (Tα α) (up (Tα α) G.top)) → (∀ α → Full (Tα α) (up (Tα α) G.top) (s α)) → LPO
step-full→lpo s full α = decide α (s α (r₀ α)) (λ fd → full α (r₀ α) (found→at α fd))

at-top : (U : Uni) {k : LF} {g : Raw k → LF} (V : Uni.Bd U (lc k g)) {η : Raw k} →
  η ≡ G.top → (l : Lgl k η) → StpFull U V η l → StpFull U V G.top tt
at-top U V refl l f = f

stp-full→lpo : (U : Uni) (Vα : ∀ α → Uni.Bd U (Lα α)) →
  (∀ α → StpFull U {k = Tα α} {g = up (Tα α)} (Vα α) (Uni.cpt U (Vα α) 0) (Uni.cpt-lgl U (Vα α) 0)) → LPO
stp-full→lpo U Vα full = step-full→lpo (λ α → Uni.stp U (Vα α) G.top tt)
  (λ α → at-top U (Vα α) (Uni.cpt-zero U (Vα α)) (Uni.cpt-lgl U (Vα α) 0) (full α))

stp-full→lpo-dom : (U : Uni) (D : Dom U) →
  (∀ α → StpFull U {k = Tα α} {g = up (Tα α)} (Uni.bC U (Dom.bd-tw D 3) (ηα α) (lim-lgl α))
    (Uni.cpt U {k = Tα α} {g = up (Tα α)} (Uni.bC U (Dom.bd-tw D 3) (ηα α) (lim-lgl α)) 0)
    (Uni.cpt-lgl U {k = Tα α} {g = up (Tα α)} (Uni.bC U (Dom.bd-tw D 3) (ηα α) (lim-lgl α)) 0)) → LPO
stp-full→lpo-dom U D = stp-full→lpo U (λ α → Uni.bC U (Dom.bd-tw D 3) (ηα α) (lim-lgl α))
```

## 3 `tw 2` 上没有这个问题

```agda
tw2-stp-full : ∀ {k g} (V : Lv (lc k g)) η l → StpFull Tw2 V η l
tw2-stp-full (vΩ V u) η l r (() , _)
```
