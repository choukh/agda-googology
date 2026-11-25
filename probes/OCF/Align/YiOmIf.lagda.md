# YiOm 接口：公共上界含 Ω 结点 (第 4 步第一站)

**档位：定义、陈述与规范实例检查。没有折叠，没有值，没有否定。** 构造路 (`YiOmFold*`) 与否定路 (`YiOmNeg*`) 共用本文件；定稿后只增不改。
公共上界取 `tw 2` (读法 Ω₁)。它的位置有两种：主干上的，与某一支里的 (坐标 `η`，相关的守卫 `e`，`read0 η` 里的位置)；
孩子同样。而 `Raw` 的结点的分支只带无关的守卫。本文件把这一处写成两条陈述，各有相关与无关两种写法。上一步的接口 [YiRawIf](YiRawIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiOmIf where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
open import OCF.Align.YiRawIf
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂; br; Link; compare-link)
```

## 1 第 η 支里的槽位与孩子

`Slot η r`：`tw 2` 里一个层号等于 "第 η 支的位置 `r` 上的层号" 的位置。守卫是相关参数时，位置就是 `br η e r`。
`Kid` 一侧同理：第 η 支的孩子是 `Raw (read0 η)`，用 `em` 嵌进 `Raw (tw 2)` 要相关的守卫。

```agda
Slot : (η : R) → Pre (read0 η) → Set
Slot η r = Σ (Pre K₂ω) λ q → lev K₂ω q ≡ lev (read0 η) r

slot-rel : ∀ η → Gd zero raw1 η → (r : Pre (read0 η)) → Slot η r
slot-rel η e r = br η e r , refl

kid-rel : ∀ η → Gd zero raw1 η → Raw (read0 η) → Raw K₂ω
kid-rel η e T = G.em (inj₂ (inj₂ (η , e))) T

kid-rel-read : ∀ η (e : Gd zero raw1 η) T .(nb : Nested (read0 η) T) →
  up K₂ω (kid-rel η e T) nb ≡ up (read0 η) T nb
kid-rel-read η e T nb = refl
```

结点的分支函数只拿到无关的守卫。保留模式下折叠 `top : Raw (tw 2)` (读回是 `tw 3`) 时，根是层号 0 的结点，要保留；
它的第 η 支是第 η 支的 `top` 的折叠，其中的保留结点要落在第 η 支的槽位上。所以这一行需要下面两条之一。
它们有没有实例，本文件没有证，也没有否定。

```agda
-- 从无关的守卫交出第 η 支里的槽位.
SlotIrr : Set
SlotIrr = ∀ η → .(Gd zero raw1 η) → (r : Pre (read0 η)) → Slot η r

-- 从无关的守卫把第 η 支的树嵌进来, 读回不变.
KidIrr : Set
KidIrr = Σ (∀ η → .(Gd zero raw1 η) → Raw (read0 η) → Raw K₂ω) λ emb →
  ∀ η (e : Gd zero raw1 η) T (nb : Nested (read0 η) T) →
  Σ (Nested K₂ω (emb η e T)) λ nb′ → up K₂ω (emb η e T) nb′ ≡ up (read0 η) T nb
```

## 2 被折叠的对象

第一个越过 `tw 3` 的规范结点是 `Ω̂ (suc (tw 2))`：层号 `tw 2` 的结点，下界 `top`，第一支 `tw 3`，分支是 `Raw (tw 2)` 的读回。
它是 `top : Raw (suc (tw 2))` 的读回。目标层 0 的折叠要一条 `Raw (tw 2)` 里的链，起点 `top`，由目标是 `tw 2` 自己的折叠推进。

```agda
Ω₁⁺ : LF
Ω₁⁺ = Ω̂ (suc K₂ω)

Ω₁⁺-form : Ω₁⁺ ≡ lc K₂ω G.top tt tt (tw 3) (λ ξ e → up K₂ω ξ (proj₂ (proj₂ e)))
Ω₁⁺-form = refl

Ω₁⁺-is-top : Ω₁⁺ ≡ up (suc K₂ω) G.top tt
Ω₁⁺-is-top = refl

-- 链的起点: 下界 top 自己的守卫.
start₂ : Gd K₂ω G.top G.top
start₂ = inj₁ refl , tt , tt

-- 起点那一支就是 tw 3.
start-branch : up K₂ω G.top tt ≡ tw 3
start-branch = refl
```

## 3 主干上的位置与可比的位置对

主干上两个位置的层号都是 0。可比的位置对 (`Link`) 与它们的三路取自 [YiRawNegOmega](YiRawNegOmega.lagda.md)；
任意两个位置的三路不可满足 (`no-compare-tw2`)。目标与派发沿用 `YiRawIf.Tgt`，它对一切层号有定义。

```agda
root₂-level : lev K₂ω root₂ ≡ zero
root₂-level = refl

first₂-level : lev K₂ω first₂ ≡ zero
first₂-level = refl

tgt-self : tlev K₂ω self ≡ tw 2
tgt-self = refl
```
