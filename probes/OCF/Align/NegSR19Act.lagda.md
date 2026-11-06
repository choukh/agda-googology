# 第十九轮的否定 (三): `ActS` 里有读累计的动作, 包括闭项自己的节点的分支动作

> 不读记号. 入口 [NegSR19](NegSR19.lagda.md). 对着接口 [StrRel19If](StrRel19If.lagda.md) (定稿 2026-11-05 16:01) §1 的 `ActS` 写. 实例 $\Lambda_\kappa=\mathrm{h\Omega}\,(\lambda\_\to1)$ (`NegSR16Kap`, 合法).
>
> 1. **(定理) `actS-AiK`**: `NegSR18Ai` 的分支动作 `AiK` ($\Omega$-极限处的节点 `rK`, 分支 `nκ`, 动作 `Act`) 属于 `ActS` (`sAi … sAct`). 由 `NegSR18Ai.aiReadsZ` (值): 在两个差相同、累计分别为 `n0` 与 `n1` 的状态上, 它在第 $0$ 层目标上的和分别 $\le0$ 与 $\ge1$.
> 2. **(否定) `¬ActS→NoZ`**: "`ActS` 的动作都不读累计" (接口 `StrRel18If.NoZ`) 不成立.
> 3. **(定理) `actS-fold`**: 闭项 $\Omega_{\Lambda_\kappa}$ 第一步在第 $\Lambda_\kappa$ 层目标上产生的保留节点 (`StrRel18Az.cellK`), 它的分支动作属于 `ActS`; 由 `StrRel18Az.¬noZ-fold` 它读累计. 所以读累计的 `ActS` 动作不是人造的: 折叠自己会在再折叠时用到它.
>
> **对任务 (i) 的回答 (定理加判断).** `ActS` 由 `Ai` 生成, `Ai` 运行分支, 分支里的 `nκ` 在第 $0$ 层目标上从累计起回灌 (`NegSR18Walk`), 所以 `ActS` 把 "读累计" 带了进来, 虽然不带进 `Az` (`NegSR19Good.¬ActS-Az`). `NegSR18Up.¬UpSoundR` 的机制 (上升输出在产生时读累计, 保留输出的分支在 `cv` 之后运行) 因此在 `ActS` 下仍在: `NegSR19Rk.¬RkSoundS-Any` 是它在 `rk⁺⁺` 上的形式 (产生时动作 `Act`, 读累计的是分支里的 `nκ`). `NegSR19Up.¬UpSoundS-Any` 是它在 `up` 本身上的形式 (不带时间条件). 带 `DomZ` 时: 判断对称, 没有找到反例 (见 `NegSR19Rk` 文件头).
>
> **构造一路为什么需要这条.** 接口 "范围 (iii)": `up` 的产生时动作要 `ActS`, 是为了排除 `¬UpSoundR` 的反例. 若 "`ActS` ⇒ 不读累计" 成立, `UpSoundZ`, `RkSoundZ` 就可以不管产生时的累计 (`NegSR18Z` 的读法). 本文说它不成立, 所以证明必须用 `DomZ` 的累计分量.
>
> **只否定什么.** 只否定 "一切 `ActS` 动作满足 `NoZ`" 这一个全称陈述 (值的不同, 不只是字面). 不否定 `ActS` 作为规则前提的正性, 不否定 `¬ActS-Az`. 没有推出 LPO/WLPO 或判定.
>
> **前提可满足.** `NoZ` 是 `StrRel18If` 的定义; 实例 `AiK`, 闭项的节点都是闭项; `sAct`, `sAi` 的参数全部给出.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR19Act where

open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (hz; hs; hself; accL; n0)
open import OCF.Align.NegSR16Kap using (Λκ; lΛκ)
open import OCF.Align.StrRel18If Λκ lΛκ using (NoZ)
open import OCF.Align.StrRel19If Λκ lΛκ using (ActS; sAct; sAi)
open import OCF.Align.StrRel16If Λκ lΛκ using (module P)
open import OCF.Align.NegSR18Ai using (rK; uK; hkK; AiK; aiReadsZ; ¬noZAiK)
import OCF.Align.StrRel18Az as Az

open P using (Ig; Ai; Act)
```

```agda
actS-AiK : ActS AiK
actS-AiK = sAi (accL Λκ) (accL hz) rK uK C.self hkK hself n0 sAct

¬ActS→NoZ : ¬ (∀ {L W} (lW : Lg W) (A₀ : Ig L W) → ActS A₀ → NoZ lW A₀)
¬ActS→NoZ h = ¬noZAiK (h tt AiK actS-AiK)

-- 闭项里的那个保留节点的分支动作
AiFold : Ig (hs hz) azero
AiFold = Ai (accL Λκ) (accL (hs hz)) Az.r (Az.brK (proj₁ Az.cellK) (proj₁ (proj₂ Az.cellK))) C.self Az.hkK hself Act n0

actS-fold : ActS AiFold
actS-fold = sAi (accL Λκ) (accL (hs hz)) Az.r (Az.brK (proj₁ Az.cellK) (proj₁ (proj₂ Az.cellK))) C.self Az.hkK hself n0 sAct

¬noZ-actS-fold : ¬ NoZ tt AiFold
¬noZ-actS-fold = Az.¬noZ-fold
```
