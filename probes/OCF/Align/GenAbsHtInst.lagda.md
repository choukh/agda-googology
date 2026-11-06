# 规范形论证对树类型抽象 (四): 高度树与塔的第 0 层是签名的实例

> 不含记号. 入口 [GenAbs](GenAbs.lagda.md). `HtFeedTree.D hz` 与 `HtTowerFTree.D hz` 各给一个签名实例 (`σH`, `σT`). 每个实例是归纳原理 (对构造子的模式匹配, 节点种类空) 加一个记录, 方程都是 `refl`. 实例上得到通用的 `smono` (`sum` 对底与树的值单调), 不经翻译.
>
> `HtTowerFTree` 的世界是一对, `nw` 用世界序 `≤`, 第 0 层多一个空的 `nμ`; 签名把世界与世界序作参数, 所以不需要别的改动.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GenAbsHtInst where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.CumReadCF using (A; _⊲_)
open import OCF.Align.GenAbsSig using (Sig; module Ops)
import OCF.Align.HtFeedTree as HF
import OCF.Align.HtTowerFTree as HT
```

## §1 `HtFeedTree.D hz`

```agda
module _ where
  open HF using (D; hz; n0; n1; _⨾_; nl; ni; nκ; nw)

  indH : (P : ∀ {W} → D hz W → Set) →
         (∀ {W} → P (n0 {W = W})) → (∀ {W} → P (n1 {W = W})) →
         (∀ {W} {x y : D hz W} → P x → P y → P (x ⨾ y)) →
         (∀ {W} {d : ℕ → D hz W} → (∀ n → P (d n)) → P (nl d)) →
         (∀ {W₀ W} {p : W₀ ⊲ W} {x : D hz W₀} → P x → P (nw p x)) →
         ∀ {W} (z : D hz W) → P z
  indH P c0 c1 c⨾ cl cw n0 = c0
  indH P c0 c1 c⨾ cl cw n1 = c1
  indH P c0 c1 c⨾ cl cw (x ⨾ y) = c⨾ (indH P c0 c1 c⨾ cl cw x) (indH P c0 c1 c⨾ cl cw y)
  indH P c0 c1 c⨾ cl cw (nl d) = cl (λ n → indH P c0 c1 c⨾ cl cw (d n))
  indH P c0 c1 c⨾ cl cw (ni () u)
  indH P c0 c1 c⨾ cl cw (nκ () u)
  indH P c0 c1 c⨾ cl cw (nw p x) = cw (indH P c0 c1 c⨾ cl cw x)

  σH : Sig
  σH = record
    { Wd = A ; _≺_ = _⊲_ ; T = D hz
    ; n0 = n0 ; n1 = n1 ; _⨾_ = _⨾_ ; nl = nl ; nw = nw ; ind = indH
    ; sum = HF.sum ; pt = HF.pt
    ; pt-z = λ _ _ → refl ; pt-s = λ _ _ _ → refl
    ; sum-n0 = λ _ → refl ; sum-n1 = λ _ → refl ; sum-⨾ = λ _ _ _ → refl
    ; sum-nl = λ _ _ → refl ; sum-nw = λ _ _ _ → refl
    ; sum-fst = HF.sum-fst ; Lg-sum = HF.Lg-sum }

  open Ops σH public using () renaming (smono to smonoᴴ; pre to preᴴ; val to valᴴ)
```

## §2 `HtTowerFTree.D₀` (即 `D hz`)

```agda
module _ where
  open HT using (D₀; Wd₂; n0; n1; _⨾_; nl; ni; nκ; nμ; nw) renaming (_≤_ to _≤w_)

  indT : (P : ∀ {W} → D₀ W → Set) →
         (∀ {W} → P (n0 {W = W})) → (∀ {W} → P (n1 {W = W})) →
         (∀ {W} {x y : D₀ W} → P x → P y → P (x ⨾ y)) →
         (∀ {W} {d : ℕ → D₀ W} → (∀ n → P (d n)) → P (nl d)) →
         (∀ {W₀ W} {p : W₀ ≤w W} {x : D₀ W₀} → P x → P (nw p x)) →
         ∀ {W} (z : D₀ W) → P z
  indT P c0 c1 c⨾ cl cw n0 = c0
  indT P c0 c1 c⨾ cl cw n1 = c1
  indT P c0 c1 c⨾ cl cw (x ⨾ y) = c⨾ (indT P c0 c1 c⨾ cl cw x) (indT P c0 c1 c⨾ cl cw y)
  indT P c0 c1 c⨾ cl cw (nl d) = cl (λ n → indT P c0 c1 c⨾ cl cw (d n))
  indT P c0 c1 c⨾ cl cw (ni () u)
  indT P c0 c1 c⨾ cl cw (nκ () u)
  indT P c0 c1 c⨾ cl cw (nμ () u)
  indT P c0 c1 c⨾ cl cw (nw p x) = cw (indT P c0 c1 c⨾ cl cw x)

  σT : Sig
  σT = record
    { Wd = Wd₂ ; _≺_ = _≤w_ ; T = D₀
    ; n0 = n0 ; n1 = n1 ; _⨾_ = _⨾_ ; nl = nl ; nw = nw ; ind = indT
    ; sum = HT.sum ; pt = HT.pt
    ; pt-z = λ _ _ → refl ; pt-s = λ _ _ _ → refl
    ; sum-n0 = λ _ → refl ; sum-n1 = λ _ → refl ; sum-⨾ = λ _ _ _ → refl
    ; sum-nl = λ _ _ → refl ; sum-nw = λ _ _ _ → refl
    ; sum-fst = HT.sum-fst ; Lg-sum = HT.Lg-sum }

  open Ops σT public using () renaming (smono to smonoᵀ; pre to preᵀ; val to valᵀ)
```
