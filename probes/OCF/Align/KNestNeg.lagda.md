# 嵌套 `nκ` (一): 内层的分支对层**反**单调

> 不含记号. 入口 [KNest](KNest.lagda.md). 对象是 `SumOneClosed` 的折叠 ($S=\cdot\omega$) 在目标第 0 层上的输出, 语义沿用 [KValSound](KValSound.lagda.md) 的 `OutLe`.
>
> **最简单的嵌套族** $u_\kappa(c)=\mathrm{n}\kappa\,(\lambda d.\,1)$ (层 $c$ 上放一个世界 $c$ 上的回灌节点, 分支都是 $1$) 的分支**不能**对层单调: 同一个世界 $2$, 同一个状态, 同一个动作, 回灌层 $\ell=\ell'=2$ (所以 `Hℓ` 成立, 上下文 `Cx` 的四条都成立), 左边 $u_\kappa(1)$ 第一格走 $[1,2)$ 一层, 输出至少是 $1$; 右边 $u_\kappa(2)$ 第一格走 $[2,2)$, 空, 以后每格都空 (`L1ValBase.κ-stall`), 输出是 $0$.
>
> 所以 (`¬KMonoˢ`, `¬crit`): 对一切档 `m`, 语义上 `OutLe m (uκ 1) (uκ 2)` 是假的; 任何对 `OutLe m` 可靠的关系都不能有 "$c\le c'$ ⇒ $u_\kappa(c)\sqsubseteq u_\kappa(c')$". `KValTree` 的 `κ⊑` 的三条分支前提 (`KMono` 两条, `KX` 一条) 都是这个形状, 所以把 `κ⊑` 的分支直接放进同一个 (或更高的) 档, **推不出外层 $\mathrm{n}\kappa\,u_\kappa$ 的自比**.
>
> **否定的范围.** 只否定 "嵌套时分支对层单调" 这一个判据 (以及以它为前提的 `κ⊑` 规则用在 $u_\kappa$ 上). 前提可满足: 场景里的 `Ok`, `Cx` 都由具体项给出 (`ok₂`, `cx₂`). 不否定外层 $\mathrm{n}\kappa\,u_\kappa$ 的折叠单调 (判断: 它是单调的, 没有证); 不否定按值对齐 ($c\approx c'$) 或带 "领先量" 的判据 ([KNestAdm](KNestAdm.lagda.md)). 它也说明: **只有 `Hℓ` ($\ell\le\ell'$) 不够**, 内层右边的树世界比左边高时, 还要右边的回灌层领先得够多.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KNestNeg where

open import Data.Bool using (true)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤-refl; ≤-trans)
open import OCF.Align.SumOneTree using (D; n0; n1; nκ; cnt; sum; drp)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.L1ValBase using (Z; has1; low; zup; no10; drp-Z; Rκ; κ-stall)
open import OCF.Align.KValTree using (Md; lo; hi; Bk)
open import OCF.Align.KValSem using (cd; cohY0)
open import OCF.Align.KValSound using (Sd; sd; Ok; ok; HA⁺; Cx; cx-refl; OutLe; Ob)
```

## §1 场景

世界 $2$, 动作 `A⁺` 在一切目标上输出 $1$, 状态 `Y₂` 是零. 嵌套族 `uκ`: 层 $c$ 上放世界 $c$ 上的 `nκ`, 内层分支都是 $1$.

```agda
two : A
two = asuc one

A⁺ : F.Ig (cnt one) two
A⁺ _ _ _ _ = F.df (λ τ lt → n1) n0

s₂ : Sd
s₂ = sd two tt (C.suc C.self) A⁺

Y₂ : F.St two
Y₂ = F.st F.zeroD n0

uκ : Bk one
uκ _ _ = nκ tt (λ _ _ → n1)

ok₂ : Ok s₂ s₂
ok₂ = ok h h h c c
  where
  h : HA⁺ s₂ s₂
  h p p′ lV lV′ w w′ Y Y′ k k′ cY cY′ le c c′ cb = s≤ cb
  c : ∀ {V} (p : two ⊲ V) (lV : Lg V) w (Y : F.St V) → _ → _
  c p lV w Y cY = cd (λ τ τ′ e → ≤-refl _)

cx₂ : ∀ m → Cx m s₂ s₂ Y₂ Y₂
cx₂ m = cx-refl m s₂ Y₂ cohY0
```

## §2 两边的输出

左边: 树世界 $1$, 走 $[1,2)$, 第一格输出 `n0 ⨾ n1`. 右边: 树世界 $2$, 第一格走空路径, 以后停滞.

```agda
L R : D one two → A
L w = Ob s₂ azero (uκ {one} C.self tt) (C.suc C.self) w Y₂
R w = Ob s₂ azero (uκ {two} (C.suc C.self) tt) C.self w Y₂

outL : D one two → _
outL w = F.yc (F.Run (F.accCn one) (uκ {one} C.self tt) (C.suc C.self) tt (C.suc C.self) A⁺ w Y₂) (inj₁ (C.suc (C.suc C.self))) tt

big : ∀ w → has1 (outL w) ≡ true
big w = refl

-- 右边每一格都是零
u₁ : Bk two
u₁ _ _ = n1

rκ : ∀ w n → Rκ (F.accCn one) u₁ C.self tt (C.suc C.self) A⁺ w Y₂ n
rκ w zero = (λ τ lt → tt) , tt
rκ w (suc n) = κ-stall (F.accCn one) u₁ C.self tt (C.suc C.self) A⁺ w Y₂ n (rκ w n)

outR : D one two → _
outR w = F.yc (F.Run (F.accCn one) (uκ {two} (C.suc C.self) tt) C.self tt (C.suc C.self) A⁺ w Y₂) (inj₁ (C.suc (C.suc C.self))) tt

zR : ∀ w → Z (outR w)
zR w n = drp-Z _ (proj₁ (rκ w n) (inj₁ (z⊲ _)) tt)

anti : ∀ w w′ → ¬ (L w ≤ R w′)
anti w w′ le = no10 (≤-trans (low azero (outL w) (big w)) (≤-trans le (zup azero azero (outR w′) (zR w′) z≤)))
```

## §3 推论

```agda
¬mono : ∀ m → ¬ OutLe m (uκ {one} C.self tt) (uκ {two} (C.suc C.self) tt)
¬mono m H = anti n0 n0 (H s₂ s₂ ok₂ (C.suc C.self) C.self n0 n0 Y₂ Y₂ (cx₂ m) azero azero z≤)

-- 语义的 "分支对层单调"
KMonoˢ : Md → ∀ {V} → Bk V → Set
KMonoˢ m {V} u = ∀ {c c′} (p : V ⊲ c) (p′ : V ⊲ c′) (l : Lg c) (l′ : Lg c′) → c ≤ c′ → OutLe m (u p l) (u p′ l′)

¬KMonoˢ : ∀ m → ¬ KMonoˢ m uκ
¬KMonoˢ m h = ¬mono m (h C.self (C.suc C.self) tt tt (s≤ z≤))

-- 任何对 OutLe m 可靠的关系都不能有 KMono 形状的前提
¬crit : ∀ m (R : ∀ {V V′} → D one V → D one V′ → Set) →
        (∀ {V V′} {x : D one V} {x′ : D one V′} → R x x′ → OutLe m x x′) →
        ¬ (∀ {c c′} (p : one ⊲ c) (p′ : one ⊲ c′) (l : Lg c) (l′ : Lg c′) → c ≤ c′ → R (uκ p l) (uκ p′ l′))
¬crit m R snd h = ¬KMonoˢ m (λ p p′ l l′ le → snd (h p p′ l l′ le))
```
