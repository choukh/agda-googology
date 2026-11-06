# 第十八轮的否定 (一): `AiNoZ` 不成立: $\Omega$-极限处的节点, 分支含 `nκ`, 分支动作读累计

> 不读记号. 入口 [NegSR18](NegSR18.lagda.md). 对着接口 [StrRel18If](StrRel18If.lagda.md) (定稿 2026-11-05 14:22) §1 的 `NoZ`, `AiNoZ` 写.
>
> 实例 $\Lambda_\kappa=\mathrm{h\Omega}\,(\lambda\_\to1)$ (`NegSR16Kap`, 合法), 节点 `rK` 是 $\Omega$-极限处的种类 (`sL`, 层 $\Lambda_\kappa$, 坐标层 $0$), 分支 `uK` 是 `nκ` (每个值 `n1`). 动作是闭项的 `Act` (输出 `Step`, 只读状态的差), 它满足 `NoZ` (`noZAct`, `refl`).
>
> 1. **(定理) `outZ`, `outP`**: 分支动作 `AiK` (`HtFeedFold.Ai` 在这组参数上) 在两个**差相同**的状态上运行: 累计为 `n0` 时第 $0$ 层目标上的和 $\le 0$ (`NegSR16Kap.Cells.cellZ`: 每一格都空); 累计为 `n1` 时和 $\ge 1$ (`NegSR18Walk.walkLow`: 第 $0$ 格从世界 $0$ 走到世界 $1$, 一步, `Act` 至少加一).
> 2. **(否定) `¬AiNoZ`**: 接口的律 `AiNoZ` ("分支动作继承 `NoZ`") 不成立. 由 `AiNoZ` 与 `noZAct` 得 `NoZ` 对 `AiK` 成立, 于是上面两个输出字面相等, 与第 1 条的值矛盾.
>
> **机制 (判断, 依据证明).** `Ai` 运行分支的树 (`HtFeedFold.Ai` 的字面), 状态就是调用时的状态. 分支含 `nκ` 时, `nκ` 在第 $0$ 层目标上回灌 (`RKy` 的 `hz` 句), 第 $0$ 格的世界是 "运行世界 + 累计" (`κc` 的 `zero` 句). 所以不管动作读不读累计, 分支动作都通过 `nκ` 读累计. 限制 (a) 只约束动作, 碰不到分支里的 `nκ`.
>
> **构造一路为什么需要这条律.** `RkSoundTᶻ` 只对产生时满足 `NoZ` 的动作给结论. 节点上升时, 链用分支动作 `Ai` 运行坐标层上的树 (`RKi` 的 rise 句); 链里出现的节点 (坐标层 $\ge1$ 时链的段可以含节点) 以 `Ai` 为动作运行. 要在那里继续用 `RkSoundTᶻ`, 就要 `Ai` 满足 `NoZ`, 即 `AiNoZ`. 本文说: 分支含 `nκ` 时这一步断了, 所以 (a) 在这类节点下面是空的: 以它们的 `Ai` 为动作的节点, `RkSoundTᶻ` 的前提不成立.
>
> **只否定什么.** 只否定 `AiNoZ` 的字面陈述 (一切节点, 一切分支). 不否定分支不含 `nκ` 时的继承 (判断: 那时 `Ai` 只经 `Run` 的 `n1` 句调用动作, 状态里的累计不被读, 很可能成立; 未编译). 不说 `NoZ` 是空的: `Act` 与 `NegSR17Rk.C1` 满足它. 接口 "范围 (i)" 说 `NoZ` 是字面的; 这里的否定不只是字面的: 第 1 条是**值**的不同. 没有推出 LPO/WLPO 或判定.
>
> **前提可满足.** `noZAct` (定理); `AiNoZ` 的其余参数都是闭项 (`accL`, `rK`, `uK`, `C.self`, `hkK`, `hself`, `n0`, `tt`); 两个状态 `Ya`, `Yb` 是闭项.
>
> **它在折叠里出现吗 (判断, 未编译).** 闭项 $\Omega_{\Lambda}$ 在 $\Omega$-极限层的目标上运行时, 节点的保留输出的分支是 `BNi` 的输出, 即动作 `Act` 在那个目标上的输出 `Step`, 它是 $\omega\cdot(\Omega_t⨾\ldots)$, 而 $\Omega_t$ 在 $\Omega$-极限层 $t$ 上含 `nκ` (`HtFeedTree.Ωd` 的 `hΩ` 句). 所以闭项的折叠里有分支含 `nκ` 的节点, 它们日后再折叠时链的动作就是这样的 `Ai`. 本文的实例是最小的同类: 分支就是一个 `nκ`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR18Ai where

open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (azero; asuc; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤l; l≤; ≤-refl; ≤-trans; irr)
open import OCF.Align.HtFeedTree using (hz; hself; hsuc; sL; StH; Vs; D; D₀; n0; n1; _⨾_; nκ; nw; accL; sum; drp)
open import OCF.Align.StrRel13Val using (pt≤)
open import OCF.Align.NegSR16Kap using (Λκ; lΛκ; module Cells; YN)
open import OCF.Align.NegSR17RkT using (sumDrp)
open import OCF.Align.NegSR18Walk using (module WL)
open import OCF.Align.StrRel18If Λκ lΛκ using (NoZ; AiNoZ)
open import OCF.Align.HtFeedClosed using (module At)

module P = At Λκ lΛκ
open P using (τ₀; St; st; d; z; Df; yc; Ig; Ai; kk; Act; κΔ; lv)
open WL Λκ lΛκ using (κ1; walkLow; hAct)
```

## 1 实例

```agda
-- Act 不读累计
noZAct : ∀ {L W} (lW : Lg W) → NoZ {L} {W} lW Act
noZAct lW p lW₁ w Y z′ T = refl

-- 层 Λκ 的节点 (Ω-极限处, 坐标层 0), 分支是 nκ
rK : StH azero hz Λκ
rK = sL {c = azero} C.self (hsuc hself)

uK : ∀ {W₁} → azero ⊲ W₁ → Lg W₁ → Vs Λκ rK W₁ → D Λκ W₁
uK _ _ _ = nκ tt κ1

hkK = kk rK C.self hself

AiK : Ig hz azero
AiK = Ai (accL Λκ) (accL hz) rK uK C.self hkK hself Act n0

outK : St azero → D₀ azero
outK Y = yc (AiK C.self tt n0 Y) (τ₀ tt)

-- 两个状态: 差相同 (YN 的差), 累计 n0 与 n1
dN : Df azero
dN = d (YN {azero})

Ya Yb : St azero
Ya = st dN n0
Yb = st dN n1

-- 分支动作调用分支时的上下文 (Int 在 n0 上是 n0)
cw : D Λκ azero
cw = nw C.self n0 ⨾ n0
```

## 2 两个值

```agda
-- 累计 n0: 回灌的每一格都空
module CA = Cells (accL Λκ) κ1 tt hself (P.Ig↾ C.self Act) cw Ya

outZ : sum azero (outK Ya) ≤ azero
outZ = l≤ (pt≤ azero _ (λ n → cong drp (CA.cellZ refl n)))

-- 累计 n1: 第 0 格走一步
module CB = Cells (accL Λκ) κ1 tt hself (P.Ig↾ C.self Act) cw Yb

outP : asuc azero ≤ sum azero (outK Yb)
outP = ≤l 1 (≤-trans (walkLow (accL Λκ) (asuc azero) (C.suc C.self) C.self tt C.self tt _ _ _ _ (λ w Y′ β → hAct tt w Y′ β) azero z≤)
                     (sumDrp (yc (κΔ (accL Λκ) κ1 hself (P.Ig↾ C.self Act) (CB.cell 0)) (τ₀ (lv (CB.cell 0)))) azero))

-- 差相同, 累计不同, 输出的值不同
aiReadsZ : ¬ (sum azero (outK Yb) ≤ sum azero (outK Ya))
aiReadsZ h = irr azero (≤-trans outP (≤-trans h outZ))
```

## 3 否定

```agda
¬noZAiK : ¬ NoZ tt AiK
¬noZAiK h = aiReadsZ (subst (λ X → sum azero (outK Yb) ≤ sum azero X) (h C.self tt n0 Yb n0 (τ₀ tt)) (≤-refl _))

¬AiNoZ : ¬ AiNoZ
¬AiNoZ h = ¬noZAiK (h (accL Λκ) (accL hz) rK uK C.self hkK hself Act n0 tt (noZAct tt))
```
