# 跨高度, 不用外延性 (五): 与旧文件的前提逐字相同

> 不含记号. 入口 [HtCrossV](HtCrossV.lagda.md). **对照文件**: 只为核对新旧两版的前提与闭项是同一个命题, 用 `refl`. 主线 (`HtCrossVSim`, `HtCrossVRun`, `HtCrossVInst`, `HtCrossVNeg`) 不导入它, 也不导入任何 `HtCross*` 旧文件. 本文件导入旧的 [HtCrossInst](HtCrossInst.lagda.md), 只读其中的定义 (`TΛ-in`, `MonoStep`, `MonoL`, `X`, `X′`), 不用其中以外延性为前提的定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtCrossVBridge where

open import Data.Nat using (ℕ)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtFeedTree using (H; LgH; hs; hl; _⊲[_]_; D₀)
open import OCF.Align.HtFeedClosed using (one)
import OCF.Align.HtCrossInst as Old
import OCF.Align.HtCrossVInst as New

TΛ-in≡ : ∀ Λ′ l′ Λ (e : Λ ⊲[ one ] Λ′) → Old.TΛ-in Λ′ l′ Λ e ≡ New.TΛ-in Λ′ l′ Λ e
TΛ-in≡ Λ′ l′ Λ e = refl

X≡ : ∀ Λ (l : LgH Λ) → Old.Hs.X Λ l ≡ New.Hs.X Λ l
X≡ Λ l = refl

X′≡ : ∀ Λ (l : LgH Λ) → Old.Hs.X′ Λ l ≡ New.Hs.X′ Λ l
X′≡ Λ l = refl

MonoStep≡ : ∀ Λ (l : LgH Λ) → Old.Hs.MonoStep Λ l ≡ New.Hs.MonoStep Λ l
MonoStep≡ Λ l = refl

MonoL≡ : ∀ (f : ℕ → H) (l : LgH (hl f)) n → Old.Hl.N.MonoL f l n ≡ New.Hl.N.MonoL f l n
MonoL≡ f l n = refl
```

## `EndLowAccept.ToLimit` 不在本族的范围内

`ToLimit` 用 `hl-reduce` 于 `Λω = hl (n ↦ Λs n)` 的第 $1$ 段. `Λs 1` 是 $\Omega$-极限 (`HtOutGrow.Λ₁-form`), 不是 `Free`, 所以 `hl-reduce′` 不适用 (`fb1-not-free`). 第 $0$ 段适用 (`fb0≤ω`), 但那一段是 $\Lambda=0$, 没有内容.

```agda
open import Data.Product using (proj₁)
open import Relation.Nullary using (¬_)
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.HtOutFeed using (Λs; Λω; lΛω; T-fb; T-fbω)
open import OCF.Align.HtCrossVSim using (Free)

fb1-not-free : ¬ Free (proj₁ (Λs 1))
fb1-not-free ()

fb0≤ω : New.Hl.N.MonoL (λ n → proj₁ (Λs n)) lΛω 0 → T-fb 0 ≤ T-fbω
fb0≤ω m = New.Hl.N.hl-reduce′ (λ n → proj₁ (Λs n)) lΛω 0 _ m
```
