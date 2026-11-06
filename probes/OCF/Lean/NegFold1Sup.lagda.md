# 改 "在上" 的折法, 否定一路 (一): sup 层没有前驱; 逐层复合在 sup 层与 ι 的值相容不可得

> 不含记号. 入口 [NegFold1](NegFold1.lagda.md). 本篇**不依赖**接口的契约 (记录 `Fold1If`), 只用接口 §1, §2 的塔 `Tw`/`Lv`, `mul` 与值关系 `_≤ᵛ_`, 外加 [CRwBase](CRwBase.lagda.md), [NegFold1Base](NegFold1Base.lagda.md), [NegNoAccPt](NegNoAccPt.lagda.md) 的 `no-child`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 作者本轮选 "摆脱: 改 '在上' 的折法". 候选之一是 Fab3Typed 的方式推广到 sup 层: 每次只降一层, 多层是复合. 本篇问两件事: (1) 在 sup 层 (层号是 ℕ-极限) 上 "只降一层" 降到哪一层; (2) 复合式的折叠能否在 sup 层与它的分量相容.
>
> 1. **`no-pred`, `sup-not-one` (定理).** 层号 $m=\lim f$, 相邻项字面严格 ($f\,n+1\lhd f\,(n+1)$, `StrictL`). 对 $m$ 之下的任一层 $j$ ($j+1\lhd m$), 都有 $m$ 之下的层 $i$ 使 $j+1\lhd i$ (`no-pred`); 所以第 $m$ 层有一个种类在第 $i+1$ 层, 不满足 $i\lhd j$ (`sup-two`). "从 $m$ 降一层到 $j$" (`OneStep m j`: 每个种类的层 $i+1$ 满足 $i\lhd j$, 即留下或恰好坍缩一层) 对一切 $j$ 都不成立 (`sup-not-one`). 对照: 后继层 $x+1$ 降到 $x$ 是一步 (`succ-one`); 相邻项不严格的常列 $\lim(x+1,x+1,\dots)$ 也有前驱 $x$ (`const-one`), 所以 `StrictL` 不是多余的前提.
> 2. **`CompIncoh.no-coh` (定理, 对一切分量族).** 设 $G_k$ 是第 $k$ 层折到第 $0$ 层的折叠, 只要 $G_1\,0=1$, $G_2\,0=\lim M$ 且 $M\,1=2$ (复合式 "$0\mapsto1$, 后继 $\mapsto\cdot\omega$" 折两次与一次的值), 则**没有**任何函数 $F_\omega$ (sup 层折到第 $0$ 层) 同时满足 $F_\omega(\iota_k x)\le G_k\,x$ 与 $G_k\,x\le F_\omega(\iota_k x)$ (值关系, 对一切 $k$, $x$). 原因: $\iota_k\,0$ 字面就是 $0$ (`refl`), 所以 $F_\omega\,0$ 要同时等值于 $G_1\,0=1$ 与 $G_2\,0=\omega$. 字面相等的版本 `no-coh≡` 是推论. 实例: [NegFold1Fab3](NegFold1Fab3.lagda.md) 对 Fab3Typed 的 `fold` (定理).
>
> **前提实例.** 1: `StrictL` 的实例 $\omega=\lim(0,1,2,\dots)$ (`ω-strict`); $j=0$ 在 $\omega$ 之下. 2: 三条等式的实例: 本篇的玩具族 `Gtoy` (§3) 与 Fab3Typed 的 `fold` (另篇, 三条都是 `refl`).
>
> **只否定什么.** 1 只否定: 从字面严格的 sup 层出发, 第一步只坍缩一层. **不否定**: 一步坍缩多层 (构造一路现在的设计就是直接折到目标层, 不降一层); 常列一类的 sup 层. 2 只否定: sup 层的折叠与复合式分量**双向**值相容 (两个方向各用到一处: $k=1$ 的上界, $k=2$ 的下界). **不否定**: 单向相容 (例如 $G_k\,x\le F_\omega(\iota_k x)$), 或 sup 层另取定义; 也不涉及构造一路的接口 (接口的 `Φ-z` 让每一层都有 $\Phi\,0=1$, 不是复合式).
>
> **对纲领与目标.** 纲领不受影响. 目标 "树侧的合法性标准 / 下一步的定义不看记号": 1 是层号树自己的事实 (sup 层没有前驱), 说明 "每次只降一层" 不能原样推广到 sup 层; 2 说复合式在后继层的好处 (单调是一步定理, Fab3Typed) 到 sup 层要付代价: 要么放弃与分量的相容, 要么不复合. 构造一路已选后者 (直接折, `Φ-z` 对一切层).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegFold1Sup where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (Tw; Lv; mul; _≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l; ≤Ω; Ω≤Ω)
open import OCF.Lean.NegFold1Base
open import OCF.Lean.NegNoAccPt using (Ch; cs; no-child)
```

## §1 层号: sup 层没有前驱

```agda
StrictL : (ℕ → Cd) → Set
StrictL f = ∀ n → hs (f n) ⊲ f (suc n)

¬hs⊲ : ∀ j → ¬ (hs j ⊲ j)
¬hs⊲ j = no-child {w = tt} j cs

no-pred : ∀ {f} → StrictL f → ∀ {j} → hs j ⊲ hl f → Σ Cd (λ i → (hs i ⊲ hl f) × (hs j ⊲ i))
no-pred {f} st (hlim n q) = f n , hlim (suc n) (st n) , q

-- 后继层: x 是前驱 (x+1 之下的层都 ⊲ x)
succ-pred : ∀ x {i} → hs i ⊲ hs x → i ⊲ x
succ-pred x hself = hself
succ-pred x (hsuc q) = ⊲ᴮ-tr (hsuc hself) q

nm : ℕ → Cd
nm zero = hz
nm (suc n) = hs (nm n)

ω-strict : StrictL nm
ω-strict n = hself
```

## §2 种类: sup 层降不了一层

`NewAt i t κ`: 第 $t$ 层的种类 $\kappa$ 是第 $i+1$ 层的新种类 (第 $i+1$ 层的 $\Omega$). 第 $t$ 层的每个种类都恰在某个 $i+1\lhd t$ 处 (`kind-layer`); 反过来每个 $i+1\lhd t$ 都有种类 (`along`).

```agda
data NewAt (i : Cd) : (t : Cd) → K (Lv t) → Set where
  here  : NewAt i (hs i) (inj₂ tt)
  there : ∀ {x κ} → NewAt i x κ → NewAt i (hs x) (inj₁ κ)
  limk  : ∀ {f n κ} → NewAt i (f n) κ → NewAt i (hl f) (n , κ)

newAt⊲ : ∀ {i t κ} → NewAt i t κ → hs i ⊲ t
newAt⊲ here = hself
newAt⊲ (there a) = hsuc (newAt⊲ a)
newAt⊲ (limk {n = n} a) = hlim n (newAt⊲ a)

kind-layer : ∀ t (κ : K (Lv t)) → Σ Cd (λ i → NewAt i t κ)
kind-layer hz ()
kind-layer (hs x) (inj₁ κ) with kind-layer x κ
... | i , a = i , there a
kind-layer (hs x) (inj₂ tt) = x , here
kind-layer (hl f) (n , κ) with kind-layer (f n) κ
... | i , a = i , limk a
kind-layer (hΩ () _) _

along : ∀ {i t} → hs i ⊲ t → Σ (K (Lv t)) (NewAt i t)
along hself = inj₂ tt , here
along (hsuc q) with along q
... | κ , a = inj₁ κ , there a
along (hlim n q) with along q
... | κ , a = (n , κ) , limk a
along (hLim {κ = ()} _ _)
```

**一步.** `OneStep m j`: 第 $m$ 层的每个种类 (在第 $i+1$ 层) 满足 $i\lhd j$: 要么留在第 $j$ 层 ($i+1\lhd j$), 要么恰好坍缩一层 ($i=j$). 这是 "从 $m$ 降一层到 $j$" 的必要条件.

```agda
OneStep : Cd → Cd → Set
OneStep m j = ∀ κ i → NewAt i m κ → i ⊲ j

succ-one : ∀ x → OneStep (hs x) x
succ-one x κ i a = succ-pred x (newAt⊲ a)

const-one : ∀ x → OneStep (hl (λ _ → hs x)) x
const-one x (n , κ) i (limk a) = succ-pred x (newAt⊲ a)

sup-two : ∀ {f} → StrictL f → ∀ j → hs j ⊲ hl f →
          Σ (K (Lv (hl f))) (λ κ → Σ Cd (λ i → NewAt i (hl f) κ × (hs j ⊲ i)))
sup-two st j p with no-pred st p
... | i , pi , ji with along pi
...   | κ , a = κ , i , a , ji

sup-not-one : ∀ {f} → StrictL f → ∀ j → hs j ⊲ hl f → ¬ OneStep (hl f) j
sup-not-one st j p os with sup-two st j p
... | κ , i , a , ji = ¬hs⊲ j (⊲ᴮ-tr ji (os κ i a))

-- 实例: 第 ω 层降不到任何一层
ω-not-one : ∀ j → hs j ⊲ hl nm → ¬ OneStep (hl nm) j
ω-not-one = sup-not-one ω-strict
```

## §3 复合式的分量与 sup 层的值相容

$G_k$: 第 $k$ 层 (任一种类结构族 $F$) 折到第 $0$ 层. 只用三条等式.

```agda
¬2≤1 : ¬ (hs (hs hz) ≤ᵛ hs (hz {S⊥}))
¬2≤1 (s≤s ())
¬2≤1 (≤s ())

module CompIncoh {F : ℕ → KS} (G : (k : ℕ) → HB (F k) → Cd) (M : ℕ → Cd)
  (e1 : G 1 hz ≡ hs hz) (e2 : G 2 hz ≡ hl M) (eM : M 1 ≡ hs (hs hz)) where

  ¬L≤1 : ¬ (hl M ≤ᵛ hs hz)
  ¬L≤1 (l≤ h) = ¬2≤1 (subst (λ z → z ≤ᵛ hs hz) eM (h 1))
  ¬L≤1 (≤s (l≤ h)) with subst (λ z → z ≤ᵛ hz) eM (h 1)
  ... | ()

  ¬21 : ¬ (G 2 hz ≤ᵛ G 1 hz)
  ¬21 p = ¬L≤1 (subst₂ _≤ᵛ_ e2 e1 p)

  -- ι k 0 字面是 0: 双向值相容迫使 G 2 0 ≤ G 1 0
  no-coh : ∀ (Fω : HB (sup ℕ F) → Cd) →
           (∀ k x → Fω (ι k x) ≤ᵛ G k x) → (∀ k x → G k x ≤ᵛ Fω (ι k x)) → ⊥
  no-coh Fω lo hi = ¬21 (≤ᵛ-trans (hi 2 hz) (lo 1 hz))

  no-coh≡ : ∀ (Fω : HB (sup ℕ F) → Cd) → ¬ (∀ k x → Fω (ι k x) ≡ G k x)
  no-coh≡ Fω e = no-coh Fω
    (λ k x → subst (λ z → Fω (ι k x) ≤ᵛ z) (e k x) (≤ᵛ-refl _))
    (λ k x → subst (λ z → z ≤ᵛ Fω (ι k x)) (e k x) (≤ᵛ-refl _))
```

**前提可满足 (玩具族).** 分量都取 `S⊥`, $G_1=1$, $G_k=\omega$ ($k\ge2$, 用 `mul` 写), 其余取 $0$.

```agda
Gtoy : (k : ℕ) → HB S⊥ → Cd
Gtoy zero _ = hz
Gtoy (suc zero) _ = hs hz
Gtoy (suc (suc _)) _ = hl (mul (hs hz))

module Toy = CompIncoh {F = λ (_ : ℕ) → S⊥} Gtoy (mul {S = S⊥} (hs hz)) refl refl refl
```

## 结论 (按档)

- **[定理]** `¬hs⊲`, **`no-pred`**, `succ-pred`, `ω-strict`; `NewAt`, `newAt⊲`, `kind-layer`, `along`; `succ-one`, `const-one`, **`sup-two`**, **`sup-not-one`**, `ω-not-one`; `¬2≤1`, **`CompIncoh.no-coh`**, `CompIncoh.no-coh≡` (对一切分量族, 三条等式作前提); 前提实例 `Toy`.
- **[判断]** "每次只降一层" 推广到 sup 层, 第一步就必须一次坍缩无穷多层 (由 `sup-two`: 对任何目标都有至少高两层的种类); 那一步就是 "直接折" 或 "两段折" 中的一种, 不再是复合. 这一句的 "必须" 对 `OneStep` 是定理, 对 "折叠的一步" 这个非形式的说法是判断.
