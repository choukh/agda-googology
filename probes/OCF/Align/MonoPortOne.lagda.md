# 单调的移植 (三): 共同目标的最低一站, 无条件

> 不含记号. 入口 [MonoPort](MonoPort.lagda.md). **定理 `mono₁ : MonoTarget₁`** ([KValMonoTest](KValMonoTest.lagda.md) 的陈述, 即 `HtCrossInst.Hs.MonoStep (hs hz) tt`), 无前提, 不用 `Funext`.
>
> 证明的形状 (都是计算, 再用一次 [MonoPortZero](MonoPortZero.lagda.md) 的 `chain`):
>
> - 实例 $\Lambda=1$ 里 $\Omega_1=$ `n1 ⨾ ni (ss hself) (λ _ _ _ → n1)`. 两边先走 `n1`: 一次 `Step`, 读数是底加 $(1+\text{状态值})\cdot\omega$. 左边底 $1$, 状态值 $0$; 右边底 $b_0=1+\omega$, 状态值 $\omega$ (状态里多一段 `Step Y₀`).
> - 再走节点: 节点层 $0$, 目标层 $0$, `rkT` 计算出 `rise`, 读数就是链 `Chn` 的极限. 链的动作是 `Ai`, 分支是常数 `n1`, 归约到 `Step`, 与上下文和坐标无关: 定义性地等于 `StepA` (只看状态).
> - `StepA` 满足 `HAᶜ` (`HA-Step`: 底与状态值单调). 两条链的起点: 底 (`hb`) 与状态值 (`hY`) 各用一次 `HA-Step`. `chain` 给结论.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPortOne where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import OCF.Align.CumReadCF using (A; azero; asuc)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl; ⊲→≤)
open import OCF.Align.HtFeedTree using (hz; hs; hsuc; hself; ss; accL; n0; n1; _⨾_; nl; nw; sum; pt; sum-fst)
open import OCF.Align.HtFeedClosed using (ω⋅; module At; one)
open import OCF.Align.MonoPortBridge using (val; smono)
import OCF.Align.MonoPortZero
open import OCF.Align.KValMonoTest using (MonoTarget₁)
open import OCF.Align.HtCrossInst using (b₀)

module Q = At (hs hz) tt
module Z = OCF.Align.MonoPortZero ω⋅ (hs hz) tt {one} tt (hsuc hself) (accL hz)
```

## §1 动作: 只看状态的一步

```agda
StepA : Z.Act
StepA p lW′ z Y′ = Q.Step Y′

HA-Step : Z.HAᶜ StepA StepA
HA-Step w w′ c c′ Y Y′ hw hc hY = l≤ (λ n → ≤l n (go n))
  where
  δ  = Q.yc (Q.d Y) Z.T₀
  δ′ = Q.yc (Q.d Y′) Z.T₀
  go : ∀ n → pt c (λ _ → n1 ⨾ δ) n ≤ pt c′ (λ _ → n1 ⨾ δ′) n
  go zero = hc
  go (suc n) = smono {x = n1 ⨾ δ} {x′ = n1 ⨾ δ′} (go n) (smono {b = one} {b′ = one} {x = δ} {x′ = δ′} (≤-refl one) hY)
```

## §2 两条链的起点

```agda
-- 左边: TΛ 1 的设置. 右边: TΛ 2 的链第 0 项里的设置
Yᴸ Yʳ Yʳ₀ : Q.St one
Yᴸ = Q._⊕⟨_⟩_ Q.Y₀ tt (Q.Step Q.Y₀)
Yʳ₀ = Q._⊕⟨_⟩_ (Q._⊕⟨_⟩_ Q.Y₀ tt (Q.Step Q.Y₀)) tt Q.zeroD
Yʳ = Q._⊕⟨_⟩_ Yʳ₀ tt (Q.Step Yʳ₀)

bᴸ bʳ : A
bᴸ = sum one (Q.yc (Q.Step Q.Y₀) Z.T₀)
bʳ = sum b₀ (Q.yc (Q.Step Yʳ₀) Z.T₀)

one≤b₀ : one ≤ b₀
one≤b₀ = ⊲→≤ (sum-fst one (nl (λ _ → n1 ⨾ n0)))

hb : bᴸ ≤ bʳ
hb = HA-Step n0 n0 one b₀ Q.Y₀ Yʳ₀ z≤ one≤b₀ z≤

hY : Z.vY Yᴸ ≤ Z.vY Yʳ
hY = HA-Step n0 n0 azero (Z.vY Yʳ₀) Q.Y₀ Yʳ₀ z≤ z≤ z≤
```

## §3 定理

```agda
mono₁ : MonoTarget₁
mono₁ = Z.chain HA-Step HA-Step HA-Step Yᴸ Yʳ bᴸ bʳ hb hY
```

## §4 推论: 严格增长 $T_1 < T_2$, 不用外延性

[HtCrossVInst](HtCrossVInst.lagda.md) 的 `hs-reduce<′` (前提 `Free Λ` 与 `MonoStep`; 那里的 `MonoStep` 与 `HtCrossInst` 的逐字相同, `HtCrossVBridge.MonoStep≡` 用 `refl` 核对) 在 $\Lambda=1$ 上: `Free (hs hz)` 计算成 `⊤`, `MonoStep` 就是 `mono₁`. 与 `hz<1′` 接起来, 前三个有限高度的闭项严格上升.

```agda
open import OCF.Align.TLRuleSpec using (s≤; ≤-trans)
open import OCF.Align.HtFeedClosed using (TΛ)
import OCF.Align.HtCrossVInst as CV

grow₁₂ : asuc (TΛ (hs hz) tt) ≤ TΛ (hs (hs hz)) tt
grow₁₂ = CV.HsS.hs-reduce<′ (hs hz) tt tt mono₁

grow₀₁₂ : asuc (asuc (TΛ hz tt)) ≤ TΛ (hs (hs hz)) tt
grow₀₁₂ = ≤-trans (s≤ CV.hz<1′) grow₁₂
```
