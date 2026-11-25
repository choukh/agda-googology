# YiGenFold：第 1、2 个链点上问到的两对

**档位：编译的闭实例，说明 [YiGenFoldFin](YiGenFoldFin.lagda.md) 的 `chain-honest` 的量化域里有上一轮两路判断会出问题的那两种对。**
第 1 个链点：目标在第 2 支的根 (层号 1)，结点在第 1 支的根 (层号 0)，是别的支上的结点。第 2 个链点：目标同上，被折的树是整个第 1 个链点 (根槽位上的结点，带全部分支)。
两对都被问到 (`step₁`, `step₂`)，输出都是保留结点 (`kept₁`, `kept₂`)；第二对的各支在同一目标下逐支折叠 (`row₂`)。最底下的 `top` 也被问到 (`step-top`)。不是值定理。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGenFoldSteps where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1)
open import OCF.Align.YiIrrIf using (R; one)
open import OCF.Align.YiLvIf using (lev; Kept)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; br)
open import OCF.Align.YiOmFoldBase
open import OCF.Align.YiOmFold using (t₀)
open import OCF.Align.YiOmFoldNorm using (γ)
open import OCF.Align.YiGenFold
open import OCF.Align.YiGenFoldDom
open import OCF.Align.YiGenFoldFin
```

## 1 目标：第 2 支的根

```agda
ξ₁ ξ₂ : RΩ
ξ₁ = atᶜ (pointsᶜ 1)
ξ₂ = atᶜ (pointsᶜ 2)

two : R
two = G.suc one

e₂ : Gd zero raw1 two
e₂ = inj₂ (inj₁ refl) , tt , tt

τ₂ : Tg
τ₂ = at two (γ one) (inj₁ tt)

τ₂-level : tl τ₂ ≡ suc zero
τ₂-level = refl
```

## 2 第 1 个链点：别的支上的结点

路径：根的第 2 支 (层号 1 的结点，目标换成它自己那一层)，沿各支的第一支走到加数的零叶，那里是前缀 `top + Gᶜ 1`，根在第 1 支的根槽位上。

```agda
here₁ : Ask base ξ₁ base ξ₁
here₁ = here

step₁ : Ask base ξ₁ τ₂ (plusΩ G.top (Gᶜ one))
step₁ =
  let a₁ = obs here₁ two e₂
      a₂ = drive a₁ G.top (inj₁ refl , tt , tt)
      a₃ = first a₂
      a₄ = term a₃ 0
      a₅ = first a₄
      a₆ = first a₅
  in pred a₆

l₁ : Lgl K₂ω (plusΩ G.top (Gᶜ one))
l₁ = plus-lgl G.top (Gᶜ one) tt (Gᶜ-legal one tt)

n₁ : Nested K₂ω (plusΩ G.top (Gᶜ one))
n₁ = plus-ns G.top (Gᶜ one) tt (Gᶜ-nested one)

kept₁ : Kept (suc zero) zero
  (Ψᶠ τ₂ (plusΩ G.top (Gᶜ one)) (proj₂ (chain-dom 1 step₁)) l₁ n₁)
kept₁ = chain-kept 1 step₁ l₁ n₁ (inj₁ tt , refl)
```

## 3 第 2 个链点：整个第 1 个链点在分支目标下

第 2 个链点是 `ξ₁ + Φˢᶜ ξ₁`。路径同上，再穿过 `Φˢᶜ` 的像一直走到最底下的 `top` 的像 `topᶜ`，它的零叶上是前缀 `ξ₁`。

```agda
here₂ : Ask base ξ₂ base ξ₂
here₂ = here

step₂ : Ask base ξ₂ τ₂ ξ₁
step₂ =
  let a₁ = obs here₂ two e₂
      a₂ = drive a₁ G.top (inj₁ refl , tt , tt)
      a₃ = first a₂
      a₄ = term a₃ 0
      a₅ = first a₄
      a₆ = first a₅
      a₇ = term a₆ 0
      a₈ = first a₇
      a₉ = term a₈ 0
      b₀ = first a₉
      b₁ = first b₀
      b₂ = term b₁ 0
      b₃ = first b₂
      b₄ = term b₃ 0
      b₅ = first b₄
      b₆ = first b₅
      b₇ = term b₆ 0
      b₈ = first b₇
      b₉ = first b₈
      c₀ = term b₉ 0
      c₁ = first c₀
      c₂ = first c₁
  in pred c₂

kept₂ : Kept (suc zero) zero (Ψᶠ τ₂ ξ₁ (proj₂ (chain-dom 2 step₂)) (lgʳ 1) (nsʳ 1))
kept₂ = chain-kept 2 step₂ (lgʳ 1) (nsʳ 1) (inj₁ tt , refl)
```

保留结点落在目标层 (层号 1) 的根槽位上；它的第一支与第 `η` 支 (对一切 `η`) 是同一目标下的折叠。分支里的结点都在有限坐标的支上，所以每一支里问到的派发仍在 `chain-honest` 的量化域里。

```agda
row₂ : Ψᶠ τ₂ ξ₁ (dmʳ 1) (lgʳ 1) (nsʳ 1) ≡
  G.lc (inj₁ tt) raw1
    (Ψᶠ τ₂ (plusΩ G.top t₀) (proj₁ (dmʳ 1))
      (proj₁ (proj₂ (proj₂ (proj₂ (lgʳ 1))))) (proj₁ (proj₂ (proj₂ (nsʳ 1)))))
    (λ η e → Ψᶠ τ₂ (plusΩ G.top (Gᶜ η)) (proj₂ (dmʳ 1) η e)
      (proj₂ (proj₂ (proj₂ (proj₂ (lgʳ 1)))) η e) (proj₂ (proj₂ (proj₂ (nsʳ 1))) η e))
row₂ = refl
```

## 4 最底下的 `top` 在这个目标下

第 1 个链点里，沿同一条路径再往下就是字面的 `top`。它在目标 `τ₂` 下取 `rowᶠ`：根保留在层号 0 的槽位上，第 1 支 (层号 0 的结点) 的像也是保留结点。

```agda
step-top : Ask base ξ₁ τ₂ G.top
step-top =
  let a₁ = first step₁
      a₂ = term a₁ 0
      a₃ = first a₂
      a₄ = first a₃
      a₅ = pred a₄
      a₆ = first a₅
      a₇ = term a₆ 0
      a₈ = first a₇
      a₉ = first a₈
  in pred a₉

top₂-root : Kept (suc zero) zero (Ψᶠ τ₂ G.top tt tt tt)
top₂-root = topS-kept two (γ one) (inj₁ tt) (inj₁ tt , refl)

e₁ : Gd zero raw1 one
e₁ = inj₁ refl , tt , tt

top₂-branch : Kept (suc zero) zero (TopRow.Row.S two (γ one) (inj₁ tt) (inj₁ tt) refl one)
top₂-branch = top-keep two (γ one) (inj₁ tt) tt (inj₁ tt) refl G.zero e₁ (inj₁ tt , refl)
```
