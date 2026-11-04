# 树语言小实验 (一): 回灌是精确的, 闭包是回灌链上的 ℕ-极限

> 路线审查 (`probes/Survey/RouteReview.md`) 附带的小实验. 只导入 `OCF.Free.Level`, `OCF.Free.Force`, `OCF.Free.Prefix`, 不含记号. 两件事:
>
> 1. **`feed-exact` (定理).** 带证据的回灌 `toLevel` 没有毛刺: 把层号忘回第 0 层的树, 与原树 $\cong$. 这是与已发表 BTBO 的 `ordᴰ` (累加, `Cumsum.overshoot` 已编译出 $\omega\cdot3<\mathsf{ord}^\mathsf{D}(\omega+\omega)$) 的对照: 累加改值和基本列, 证据不改. 结论: "去掉累加" 在回灌这一处不是审美, 是精确性; 代价是回灌要 `HS` 证据.
> 2. **`Clo` (定义, 带条件的 `HS`).** 把 `Goodᴺ.gc` 的计值写成一个只看树的算子: 链 $y_0=t_0$, $y_{k+1}=g(\mathrm{lv}\,y_k)$, 输出 $\lim_k o(\mathrm{lv}\,y_k)$. 它不提 `Z`, 不提 `ĉᴸ`, 不提记号. `clo-force`: `gc` 的计值与它 $\cong$ (链点取 `gc` 自带的 `ys`). 这说明主线证书里 "闭包" 这个节点的语义就是回灌链, 可以脱离符号树 `Z` 单独陈述. 它**不**说明 `gc` 的前提 (`dy`, `lE`, 单调) 能脱离闭包定理拿到.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLangFeed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ)
open import OCF.Free.Force using (Goodᴺ; gc; forceᴺ; forceᴺ-HS; outsᴺ)
```

## §1 回灌精确

```agda
forget : Ordᴵ → Ordᶜ zero
forget zero      = zero
forget (suc a)   = suc (forget a)
forget (lim f s) = lim (λ n → forget (f n))

feed-exact : ∀ (x : Ordᶜ zero) (h : HS x) → forget (toLevel x h) ≅ x
feed-exact zero        hz        = z≅
feed-exact (suc a)     (hs h)    = s≅ (feed-exact a h)
feed-exact (lim f)     (hl h st) = l≅ (λ n → feed-exact (f n) (h n))
feed-exact (limᵢ () f) h
feed-exact (up () x)   h
```

## §2 闭包 = 回灌链上的 ℕ-极限

```agda
module Clo (t₀ : Ordᶜ zero) (h₀ : HS t₀)
           (g : Ordᴵ → Ordᶜ zero) (hg : ∀ η → HS (g η))
           (o₀ : Ordᶜ zero) (o : Ordᴵ → Ordᶜ zero) where

  ch : ℕ → Σ (Ordᶜ zero) HS
  ch zero    = t₀ , h₀
  ch (suc k) = g (toLevel (proj₁ (ch k)) (proj₂ (ch k))) , hg _

  lv : ℕ → Ordᴵ
  lv k = toLevel (proj₁ (ch k)) (proj₂ (ch k))

  outs : ℕ → Ordᶜ zero
  outs zero    = o₀
  outs (suc k) = o (lv k)

  clo : Ordᶜ zero
  clo = lim outs

  HS-clo : HS o₀ → (∀ k → HS (o (lv k))) → (∀ k → outs k ⊑⁰ outs (suc k)) → HS clo
  HS-clo ho₀ ho st = hl (λ { zero → ho₀ ; (suc k) → ho k }) st
```

`gc` 的计值就是这种形状: 链点 `ys` 由 `gc` 自带, 第 $k+1$ 个链点是第 $k$ 个链点层号上的分支的计值 (`lE`), 输出沿链点层号取. 下面只把这一点从 `gc` 里取出来写成陈述; 证明是 `≅-refl⁰`, 因为 `forceᴺ (gc …)` 按定义就是这个 `lim`.

```agda
module _ {c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} where
  gc-ys : Goodᴺ (ĉᴸ c t₀ g o₀ o) → ℕ → Ordᶜ zero
  gc-ys (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = ys

  gc-hy : (G : Goodᴺ (ĉᴸ c t₀ g o₀ o)) → ∀ m → HS (gc-ys G m)
  gc-hy (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = hy

  gc-dy : (G : Goodᴺ (ĉᴸ c t₀ g o₀ o)) → ∀ m → c ⊑ᴵ toLevel (gc-ys G m) (gc-hy G m)
  gc-dy (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = dy

  gc-Go₀ : Goodᴺ (ĉᴸ c t₀ g o₀ o) → Goodᴺ o₀
  gc-Go₀ (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = Go₀

  gc-Go : (G : Goodᴺ (ĉᴸ c t₀ g o₀ o)) → ∀ k → Goodᴺ (o (toLevel (gc-ys G k) (gc-hy G k)) (gc-dy G k))
  gc-Go (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = Go

  -- 链的步: 第 k+1 个链点是第 k 个链点层号上的 g 分支的计值
  gc-Gg : (G : Goodᴺ (ĉᴸ c t₀ g o₀ o)) → ∀ m → Goodᴺ (g (toLevel (gc-ys G m) (gc-hy G m)) (gc-dy G m))
  gc-Gg (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = Gg

  gc-step : (G : Goodᴺ (ĉᴸ c t₀ g o₀ o)) → ∀ m → forceᴺ _ (gc-Gg G m) ≅ gc-ys G (suc m)
  gc-step (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = lE

  clo-force : (G : Goodᴺ (ĉᴸ c t₀ g o₀ o)) →
              forceᴺ _ G ≅ lim (outsᴺ (forceᴺ _ (gc-Go₀ G)) (λ k → forceᴺ _ (gc-Go G k)))
  clo-force (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = ≅-refl⁰ _
```
