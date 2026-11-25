# YiNext 验收：`tw 2` 上一律折叠的派发丢掉的一对 (有限测试)

**验收文件，档位：有限测试 (闭实例，`refl`)。** `Φ₂` (目标 `tw 2` 自己) 在 `top` 上保留层号 0 的结点 (`Ω-keep`)，在坐标 `suc top` 的那一支
造出层号 1 的结点 `Ω₂`，它的 `top` 支是同一支里层号 0 的结点。折到第 0 层时，这个结点的分支折到层号 1，`cmp V₂` 对这一对给折叠，
而层号 1 里有槽位可以保留 (`could`)。这一对是否被 `T⁺` 的链问到是判断 (见回报)，这里只陈述派发的值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNextAccTest where

open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
open import OCF.Lean.YiNextFold
open import OCF.Lean.YiNextTop using (lv; V₂)

s₂ s₂′ : Pre (tw 2)
s₂ = G.suc G.top , tt , inj₁ tt
s₂′ = G.suc G.top , tt , inj₂ (inj₁ tt)

Ω₂ : Raw (tw 2)
Ω₂ = Ψ (tw 2) (lv (G.suc G.top) tt) (λ r → keep (G.suc G.top , tt , r) refl) G.top

Ω₂-form : Ω₂ ≡ G.lc s₂ (λ η → Ψ (tw 2) (vs v0) (λ r → keep (G.suc G.top , tt , inj₂ r) refl) η)
Ω₂-form = refl

Ω₂-top : Ψ (tw 2) (vs v0) (λ r → keep (G.suc G.top , tt , inj₂ r) refl) G.top ≡
  G.lc s₂′ (λ η → Ψ (tw 2) v0 (λ r → keep (G.suc G.top , tt , inj₂ (inj₂ r)) refl) η)
Ω₂-top = refl

lost : cmp V₂ s₂ s₂′ ≡ fold
lost = refl

could : Way (lev (tw 2) s₂) (lev (tw 2) s₂′)
could = keep (inj₁ tt) refl
```
