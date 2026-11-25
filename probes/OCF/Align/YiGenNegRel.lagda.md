# YiGenNeg 第 5 项：相对坐标的行在根上诚实，在各支上不诚实

**判决 (编译定理)：构造路的相对坐标的行 `rowᴿ` (规范实例 `row₃`：目标在第 3 支的根上，树是 `top`) 合法，根保留 (已有的 `rowᴿ-legal`, `rowᴿ-kept`)；
但它的第 1 支不是 `top` 的第 1 支的保留像：那一支的根层号是 0，在目标层的位置上，而行里的第 1 支是 ℕ 极限 (`row₃-branch-not-kept`)。所以它不满足 "各支诚实" (`BranchKeep`)。**
"各支诚实" 就是 `top-branch→lpo` 的前提去掉目标的变动，也是 [YiGenNegWall](YiGenNegWall.lagda.md) 的 `KeepRowAt` 在 `top` 上的同形。只在根上诚实是便宜的 (`cheap-root`)。
两路的分歧落在这一条上：保留结点的各支要不要是原来各支的折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGenNegRel where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1)
open import OCF.Align.YiIrrIf using (R; one; read0)
open import OCF.Align.YiLvIf using (lev; Kept)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiLvNegKeep using (kept-node)
open import OCF.Align.YiRawIf using (IsLim)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; br)
open import OCF.Align.YiOmFoldBase using (RΩ)
open import OCF.Align.YiOmFoldNorm using (nrm)
open import OCF.Align.YiOmFoldRel using (module Rel; three; e₃; slot₃; slot₃-level)
open import OCF.Align.YiGenNegShape using (B₁)
open import OCF.Align.YiGenNegWall using (HonestAt; r*; L*)
```

## 1 各支诚实的陈述 (树是 `top`)

`top` 的第 `suc s` 支的根是层号 `read0 s` 的结点。`BranchKeep m β`：目标层 `m`，分支族 `β`；这个层号在目标层的位置上时，`β (suc s)` 是那个层号的保留结点。
这是 `YiOmNegBranch.TopBranch.branch-keep` 在一个固定目标上的形式，去掉了 `Link` 前提 (加上前提只会更弱；下面的反例在根的第 1 支上，与目标所在的第 3 支有字面路径)。

```agda
BranchKeep : (m : LF) → ((η : R) → .(Gd zero raw1 η) → Raw m) → Set
BranchKeep m β = ∀ s (e : Gd zero raw1 (G.suc s)) →
  At m (read0 s) → Kept m (read0 s) (β (G.suc s) e)
```

## 2 规范实例 `row₃`

`S` 是 `rowᴿ` 的分支族。坐标 1 (`s = 0`)：`top` 的第 1 支的根层号是 0，目标层 2 里有层号 0 的槽位，所以各支诚实要求 `S 1` 是保留结点。
`S 1 = t₁ + F 0`，`F 0` 是相对坐标 `3 + 0` 那一支的 `top` 折到目标：那一支的根层号 2 与目标相等，折叠，是 ℕ 极限；加法逐项，`S 1` 也是 ℕ 极限。

```agda
open Rel three e₃ (inj₁ tt)
open Row slot₃ slot₃-level

e-one : Gd zero raw1 one
e-one = inj₁ refl , tt , tt

target-has-zero : At j (read0 G.zero)
target-has-zero = slot₃ , refl

row₃-root-kept : Kept j zero rowᴿ
row₃-root-kept = rowᴿ-kept

row₃-branch-lim : IsLim (S one)
row₃-branch-lim = tt

row₃-branch-not-kept : Kept j (read0 G.zero) (S one) → ⊥
row₃-branch-not-kept k = kept-node j (read0 G.zero) (S one) k

row₃-not-branch-keep : BranchKeep j (λ η e → S η) → ⊥
row₃-not-branch-keep bk = row₃-branch-not-kept (bk G.zero e-one target-has-zero)
```

## 3 只在根上诚实是便宜的

`Honest` 只说根。在第 4 项的那一对 (目标 `r*`，树 `P₁`) 上：槽位取目标层里层号 0 的位置，下界、第一支、各支都取零，就是一个根上诚实的输出；
它的分支族处处不诚实 (`P₁` 的每一支的根都是结点，零既不是保留结点也不是 ℕ 极限)。所以强度在各支上。

```agda
cheap : Raw L*
cheap = G.lc (inj₂ (0 , inj₁ tt)) G.zero G.zero (λ _ _ → G.zero)

cheap-root : Kept L* zero cheap
cheap-root = inj₂ (0 , inj₁ tt) , refl , G.zero , G.zero , (λ _ _ → G.zero) , refl

cheap-lgl : Lgl L* cheap
cheap-lgl = (λ η e → inj₁ refl) , (λ η e η′ e′ d → inj₁ refl) , (λ η e e′ → refl) , tt , (λ η e → tt)

cheap-not-branch : ∀ s (e : Gd zero raw1 (G.suc s)) → HonestAt r* G.zero (B₁ (G.suc s)) → ⊥
cheap-not-branch s e (kl , fl) = fl (λ a → kept-node L* (read0 (nrm s)) G.zero (kl a))
```
