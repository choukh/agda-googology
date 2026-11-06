# Cubical 验证实验 (三): 一般种类结构上 UIP 不成立

> **验证实验, 作者 2026-11-05 准许, 不进成品, 不改规则.** `--cubical --safe` 模块 (库文件另加 `--cubical-compatible --guardedness --hidden-argument-puns`), 不开 K. 不改任何已有文件. 无公设, 无洞, 无停机或正性编译指示. 不含记号. 入口 [CubXFe](CubXFe.lagda.md), 正面在 [CubXSet](CubXSet.lagda.md).
>
> [CubXSet](CubXSet.lagda.md) 的 `isSetHB` 要 `K S` 是集合. 本篇说明这个前提不能去掉: 取种类为圆周 `S¹` 的种类结构 `Sc` (其余字段平凡), `HB Sc` 上的 UIP 推出圆周的环 `loop` 等于 `refl`, 与 winding 数矛盾 (`¬uip-S¹`, 定理, 在 `--cubical` 下).
>
> **只否定什么.** 只否定 "对**一切** `S`, `HB S` 上有 UIP" (即 [NegColimALoop](NegColimALoop.lagda.md) 的 `UIPˢ` 对任意 `S` 一致地成立). `Sc` 只在立方类型论里写得出 (要高阶归纳类型); 主线 (`--without-K`, 无高阶归纳类型) 里没有这样的 `K`, 那里的种类结构都由 `S₀`, `step`, `sup`, `Lev` 搭成, 都满足 `CubXSet.SetKS`. 不否定任何 `SetKS` 的 `S` 上的 UIP. 前提可满足: `Sc` 是具体的记录, 每个字段都写出.

```agda
{-# OPTIONS --cubical --safe --lossy-unification #-}
module OCF.Align.CubXSetNeg where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Cubical.Foundations.Prelude as P using () renaming (_≡_ to _≡ₚ_)
open import Cubical.HITs.S1 using (S¹; base; loop; winding)
open import Cubical.Data.Int using (pos; injPos)
open import Cubical.Data.Nat using (snotz)
import Cubical.Data.Empty as E
open import Cubical.Data.Equality.Conversion using (pathToEq; eqToPath; eqToPath-pathToEq)

open import OCF.Align.HtTowerTy
```

## §1 种类是圆周的种类结构

```agda
Sc : KS
Sc = record
  { K = S¹ ; E = λ _ → ⊤ ; Wd = ⊤ ; LgW = λ _ → ⊤ ; _≤w_ = λ _ _ → ⊤ ; ≤w-rf = tt ; ≤w-tr = λ _ _ → tt
  ; Bd = λ _ _ _ → ⊤ ; Pr = λ _ _ _ _ → ⊤ ; Bd↑ = λ _ _ → tt ; cmpK = λ _ _ _ → inj₁ tt
  ; LgE = λ _ _ → ⊤ ; lgBd = λ _ _ → tt ; bot = λ _ → tt ; botBd = λ _ _ → tt }

kOf : HB Sc → S¹
kOf (hΩ κ _) = κ
kOf _ = base
```

## §2 否定

环 `λ i → hΩ (loop i) (λ _ → hz)` 译成 `_≡_` 的环 `e`. UIP 说 `e ≡ refl`; 译回路径, 用 `kOf` 投到种类上, 得 `loop ≡ refl`; winding 数给 $1 = 0$.

```agda
¬uip-S¹ : ¬ (∀ {a b : HB Sc} (e e′ : a ≡ b) → e ≡ e′)
¬uip-S¹ u = E.rec (snotz (injPos w))
  where
  p : hΩ base (λ _ → hz) ≡ₚ hΩ base (λ _ → hz)
  p i = hΩ (loop i) (λ _ → hz)

  -- e ≡ refl, 译成路径之间的路径
  q : eqToPath (pathToEq p) ≡ₚ P.refl
  q = P.cong eqToPath (eqToPath (u (pathToEq p) refl))

  p≡refl : p ≡ₚ P.refl
  p≡refl = P.sym (eqToPath-pathToEq p) P.∙ q

  loop≡refl : loop ≡ₚ P.refl
  loop≡refl = P.cong (P.cong kOf) p≡refl

  w : pos 1 ≡ₚ pos 0
  w = P.cong winding loop≡refl
```
