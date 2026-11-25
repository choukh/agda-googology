# 原嵌套反馈必须先使原第零行可求值

> **未编译草稿（2026-11-07）。下面的必要条件和值包含尚未由检查器确认，不能作定理引用；共享 CrossNestedIf 也未通过。本组停止于历史审查，不继续修补。**

这里不换链、不换起点。对共享接口的实际 `first M`，取外闭包的
初值证书，再取该初值重复列的第 1 项，得到原 `Tᵀ M zero` 的证书。
这是必要条件，不是否定；已有 `T̂ᵀ` 等修法不能替代右端原项。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossNestedBuildNecessary where

open import Data.Nat using (ℕ)
open import OCF.Free.Level using (zero)
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Force using (Goodᴺ; gc; gl; forceᴺ)
open import OCF.Align.LadderOrdPos using (Code)
open import OCF.Align.LadderOrdCert using (ev₀)
open import OCF.Align.CrossMTop using (Tᵀ)
open import OCF.Align.CrossNestedIf using (first)

initial : ∀ {c t g} → Goodᴺ (Z.ĉᴸ c t g t g) → Goodᴺ t
initial (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = Go₀

branch : ∀ {f} → Goodᴺ (Z.lim f) → (n : ℕ) → Goodᴺ (f n)
branch (gl G st) n = G n

requires-original-zero : ∀ M → Goodᴺ (first M) →
  Goodᴺ (toZ (Tᵀ M zero ev₀ zero))
requires-original-zero M good = branch (initial good) 1
```

取的是同一原初值在输出槽的证书 `Go₀`，故下面的值包含不需把
不同证书当作字面相等。它仍然只是相对于给定原 `first` 证书的
必要子结果，既没有构造该证书，也没有填 `HighFirst.inherits`。

```agda
open import OCF.Align.ValueJudgeBase using (_≼_; ≼l; ≼-refl)

original-zero-below : ∀ M (good : Goodᴺ (first M)) →
  forceᴺ _ (requires-original-zero M good) ≼ forceᴺ _ good
original-zero-below M (gc ys hy dy G₀ l₀ Gg lE (gl Go₀ st) Go mo₀ mo) =
  ≼l 0 (≼l 1 (≼-refl _))
```
