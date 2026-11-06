# `T-Ω` 的值: 验收 (条件的)

> **验收文件.** 读 `NoCumsum` 的 `BTBOᴵ` (标签树, 经 `SumOneAccept.T₀≈`). 入口 [HtVal](HtVal.lagda.md). 不要归档拷贝.
>
> 这里只把已证的东西拼起来, 说清 `BTBOᴵ ≼ T-Ω` (与反方向) 还缺什么. 缺的写成两对**树侧**命题 (不含记号, 值序是 `TLRuleSpec._≤_`):
>
> - `PortLo`, `PortHi`: 参照闭项 `T-Ω′` (同一个折叠与输入, 动作里的 $\Omega_t$ 照 `SumOne` 写, [HtValAct](HtValAct.lagda.md)) 与 `SumOne.T₀` 互相 $\le$. 有限测试 (宽 3 深 12 同形, [HtValTest](HtValTest.lagda.md)) 支持它们其实是结构互模拟; 证明要两个折叠 (`HtFeedFold` 与 `SumOneFold`) 之间的互模拟, 没有做.
> - `SwapLo`, `SwapHi`: 同一个折叠, 两个动作, 回灌格的层 $v_n$ 与 $v'_n$ 互相共尾. 第 0 格成立 (`swapLo₀`, `swapHi₀`, 无前提); 第 1 格起要走层 $\ge2$ 的节点, **未走通**. `SwapLo` 不能用逐点比较两个动作的核得到 (`HtValNeg.no-pointwise`).
>
> 结论 (条件定理): `lo : PortLo → SwapLo → BTBOᴵ ≼ trA T-Ω`, `hi : PortHi → SwapHi → trA T-Ω ≼ BTBOᴵ`. 无条件的只有 `T-Ω≈lim` (闭项是格的极限) 与第 0 格. `trA` 与 `EndLowAccept.⟪_⟫` 互模拟 (`⟪⟫≅trA`), 搬到 `⟪_⟫` 见 [HtValAcceptE](HtValAcceptE.lagda.md) (要归档拷贝).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtValAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; alim)
open import OCF.Align.Level using (Ordᶜ; lim)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans)
open import OCF.Align.NoCumsum using (BTBOᴵ)
open import OCF.Align.TLRuleVar using (trA; ≤→≼)
open import OCF.Align.TLRuleSpec using (_≤_; ≤l; l≤; ≤-trans)
open import OCF.Align.SumOneClosed using (T₀)
open import OCF.Align.SumOneAccept using (T₀≈)
open import OCF.Align.HtFeedClosed using (T-Ω)
open import OCF.Align.HtValSplit using (module M)
open import OCF.Align.HtValAct using (T-Ω′; module R; v0≤v0′; v0′≤v0)
```

## §1 无条件的部分

```agda
T-Ω≈lim : trA T-Ω ≈ᵛ lim (λ n → trA (M.v n))
T-Ω≈lim = ≤→≼ M.T≤lim , ≤→≼ M.lim≤T

T-Ω′≈lim : trA T-Ω′ ≈ᵛ lim (λ n → trA (R.v n))
T-Ω′≈lim = ≤→≼ R.T≤lim , ≤→≼ R.lim≤T
```

## §2 缺的树侧命题

```agda
PortLo PortHi : Set
PortLo = T₀ ≤ T-Ω′
PortHi = T-Ω′ ≤ T₀

SwapLo SwapHi : Set
SwapLo = ∀ n → Σ ℕ (λ m → R.v n ≤ M.v m)
SwapHi = ∀ n → Σ ℕ (λ m → M.v n ≤ R.v m)

-- 第 0 格无条件
swapLo₀ : Σ ℕ (λ m → R.v 0 ≤ M.v m)
swapLo₀ = 0 , v0′≤v0

swapHi₀ : Σ ℕ (λ m → M.v 0 ≤ R.v m)
swapHi₀ = 0 , v0≤v0′
```

## §3 条件定理

```agda
lim≤ : ∀ {f g : ℕ → A} → (∀ n → Σ ℕ (λ m → f n ≤ g m)) → alim f ≤ alim g
lim≤ c = l≤ (λ n → ≤l (proj₁ (c n)) (proj₂ (c n)))

lo : PortLo → SwapLo → BTBOᴵ ≼ trA T-Ω
lo pl sl = ≼-trans (proj₂ T₀≈) (≤→≼ (≤-trans pl (≤-trans R.T≤lim (≤-trans (lim≤ sl) M.lim≤T))))

hi : PortHi → SwapHi → trA T-Ω ≼ BTBOᴵ
hi ph sh = ≼-trans (≤→≼ (≤-trans M.T≤lim (≤-trans (lim≤ sh) (≤-trans R.lim≤T ph)))) (proj₁ T₀≈)

T-Ω≈B : PortLo → PortHi → SwapLo → SwapHi → trA T-Ω ≈ᵛ BTBOᴵ
T-Ω≈B pl ph sl sh = hi ph sh , lo pl sl
```
