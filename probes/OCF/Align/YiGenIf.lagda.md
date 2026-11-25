# YiGen 接口：规范的链是否必然要求被禁止的派发 (判定题)

**档位：定义与规范对象的核对。没有折叠，没有值，没有否定。** 构造路 (`YiGenFold*`) 与否定路 (`YiGenNeg*`) 共用本文件；定稿后只增不改。
公共上界 `tw 2`。上一轮：自目标的折叠 `Φˢ⁺` 与归一链 `pointsᴺ` 对一切 n 合法 ([YiOmFoldChain](YiOmFoldChain.lagda.md))，但链点从第 1 个起不在目标层 0 折叠的定义域里 (`point₁ᴺ-not-dom`)；
缺的是分支槽位结点处 "目标在这个位置上" 的折叠。本文件把这个折叠与 "在一个结点上派发完全且不多保留" 写成类型，供两路对同一个陈述构造或否定。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGenIf where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.YiLvIf using (lev; Kept)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiRawIf using (IsLim)
open import OCF.Align.YiRawNegOmega using (K₂ω)
open import OCF.Align.YiOmFoldBase using (RΩ; plusΩ)
open import OCF.Align.YiOmFoldChain using (Φˢ⁺; pointsᴺ)
```

## 1 目标在一个位置上的折叠

`OwnFold q`：把 `Raw (tw 2)` 的树折到位置 `q` 的层号上。树的证书无关。链行在位置 `q` 的结点处用它推进。

```agda
OwnFold : Pre K₂ω → Set
OwnFold q = (ξ : RΩ) → .(Lgl K₂ω ξ) → .(Nested K₂ω ξ) → Raw (lev K₂ω q)
```

`Honest q F ξ`：`F` 在树 `ξ` 的根上派发完全且不多保留。根是位置 `r` 上的结点时：`r` 的层号在 `q` 的层号的某个位置上，则输出是那个层号的保留结点；
否则输出是 ℕ 极限。根不是结点时不要求。只说根；对子树的要求由两路按自己的折叠去遗传，并写明遗传的范围。

```agda
Honest : ∀ q → OwnFold q → RΩ → Set
Honest q F (G.lc r c t g) =
  (l : Lgl K₂ω (G.lc r c t g)) (nb : Nested K₂ω (G.lc r c t g)) →
  (At (lev K₂ω q) (lev K₂ω r) → Kept (lev K₂ω q) (lev K₂ω r) (F (G.lc r c t g) l nb)) ×
  ((At (lev K₂ω q) (lev K₂ω r) → ⊥) → IsLim (F (G.lc r c t g) l nb))
Honest q F G.zero = ⊤
Honest q F (G.suc a) = ⊤
Honest q F (G.lim f) = ⊤
Honest q F (G.em i T) = ⊤
Honest q F G.top = ⊤
```

## 2 规范对象

两路在同一条链上说话：上一轮的归一链。起点是 `top`，下一点是这一点加上自目标折叠在这一点上的输出。

```agda
point₀ : pointsᴺ 0 ≡ G.top
point₀ = refl

point-step : ∀ n → pointsᴺ (suc n) ≡ plusΩ (pointsᴺ n) (Φˢ⁺ (pointsᴺ n))
point-step n = refl
```

要判定的陈述 (两路各取一头，陈述里的量化域由各自写明并说明为什么是链实际走到的)：把链点 `pointsᴺ n` 折到第 0 层时，
折叠问到的每一对 (目标位置 `q`，根在位置 `r` 的子树) 上，是否都能有 `Honest` 的 `OwnFold`。
构造路可以换一条链 (例如写在生成数据上、坐标取相对的)，但要说明它与本链的关系，并且自目标的折叠仍保留一切结点。
