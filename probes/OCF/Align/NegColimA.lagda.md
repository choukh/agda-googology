# 只对可入层号给分量: 否定一路 (入口)

> 不含记号. 作者选定原话: "ColimW: 只对可入层号给分量". 本路是**否定**一路, 与构造一路 `ColimA*` 配对 (手册 §5.2). 对着接口 [ColimAIf](ColimAIf.lagda.md) ("接口定稿 2026-11-05 11:12 (编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 分篇: [NegColimALoop](NegColimALoop.lagda.md) (单个增量与环的搬运), [NegColimACross](NegColimACross.lagda.md) (拷贝的认同要相干), [NegColimAGrow](NegColimAGrow.lagda.md) (外层世界变大), [NegColimADom](NegColimADom.lagda.md) (律的定义域). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; 函数外延 (`Funext`, `FE₀`) 只作前提, 用到它的结论标 "条件"; UIP 只作前提.
>
> **判决: 接口没有被否定; 编译的是三处律的确切强度与一处定义域.** 接口的族增量路线 (`RaiseA′`, 构造一路的 `ColimARaise.raiseA′`) 在这里**推不出任何禁忌**; 单个增量路线 (`RaiseA1`) 要可入层号上的环搬运平凡, 那是外延性原理, 不是禁忌.
>
> 1. **嫌疑 (i): 认同要跨证据相干; 单个增量的更新保相干推出环的搬运平凡.** 前半是定理: `NegColimACross.cross-needs-coh` (合法而不相干的世界里, 层号 `finH 1` 经坐标 2 与坐标 3 的两个证据读到不同的界; 与构造一路的 `ColimAKS.noCrossA` 独立地得到同一件事). 后半是定理 `NegColimALoop.raise1→fix₀`: **任一**满足 `at1` 与 `coh1` 的 `RaiseA1` 推出每个可入层号 $y_0$ 上的 `LoopFix₀` (环 $\ell : y_0\equiv y_0$ 沿 `HB ∘ LevA w` 的搬运在 `hz ⊞` 之后是恒等), 对一切 `S`, $X$, $w$; 最小实例上是第一个无限层号 `up ω₀` (`raise1→fixω`). 族化单个增量 (在 $(y_0,p_0)$ 处取 $\delta$ 的相干族) **当且仅当** $y_0$ 上的环搬运不动 $\delta$ (`famOf→fix`, `Legal.fix→famOf`). 反方向: 一切可入层号上环的搬运平凡且 $X$, $w$ 合法时有 `RaiseA1` (`Legal.fix→raise1`). 所以嫌疑 (i) 的 "等价于合法高度上的 K" 精确化为: `RaiseA1` 夹在 `LoopFix₀` 与 `LoopFix` (可入层号上) 之间; 二者都被 UIP 推出, 在 `HB S₀` 上被函数外延推出 (`fe→raise1₀`). **不是禁忌**, 不能关闭单个增量路线; 判断 (同 `LocUipNegLoop`): 不加外延证不出.
> 2. **嫌疑 (ii): 外层世界变大时世界要对新证据给值, 重新出现分离子.** 形状上成立: `NegColimAGrow.Need.need` (定理, 一般形): 保旧值、新可入层号从 $0$ 起、保相干的延拓推出 "旧时可入" 的弱判定. 但在接口的最小实例上那个判定是**构造的**: `Grow.odec` (定理): $X = x_0$, 外层界 $b \lhd_{[a]} b'$ ($a$, $b'$ 合法) 时, 带新证据的层号在旧世界里是否可入可判定 (两次 `cmpB` 加良基). 由它造出满足那三条律的延拓 (`Grow.ext₀`, 分量族取常值). 所以嫌疑 (ii) 在这里**推不出禁忌**; 这回答了构造一路第一个障碍的第 2 条 (`ColimA` 判决, 判断 "大概可判定") 在 $b$ 长高时的情形. $a$ 也长高、一般的合法 $X$、分量族随 $w$ 的搬运: 没有写 (判断: 同样可判定, 对路径与目标的良基递归).
> 3. **嫌疑 (iii): 认同与 `copy→⊥` 的四组前提.** `copy→⊥` 要一个种类在两个证据下有界; `LevA` 的种类带路径, 一个种类只有一个证据, 这组前提在层号种类上不出现; 底种类上的实例就是 `ColimWCopy.shapeA` 的形状, 只推出一个字面不合法的公共上界不合法 (构造一路 `ColimACopy` 已写). 两个证据的问题以 (1) 的 `cross-needs-coh` 的形式出现. 判断, 不另写定理.
> 4. **律的定义域** (`NegColimADom`): 接口的 `RaiseA′` 记录不带 $X$, $w$ 的合法性. 若对一族外层界 $X_\alpha$ (某处为真时不合法, `illegal`) 一致地满足 `atA`/`offA`, 则有分离子 (`SepD.raiseA′-sep`, 无条件), 有 `FE₀` 时 WLPO (`raiseA′→WLPO`, 条件). 构造一路的 `raiseA′` 正是以 `LgW S w`, `LgB X` 为前提造的, 与此一致; 这条只说那两个前提不能省.
>
> **对纲领与目标.** 不触壁垒: 一切判定都在同一合法界之下 (`bdec`, `cmpB`), 唯一推出 WLPO 的定理 (`raiseA′→WLPO`) 用的是不合法的外层界族. 对 "让树自足": 本路说明这一接口剩下的墙不是全知原理, 而是 "回灌产出的增量是否对层号一致" (单个增量 ⇒ 要环的搬运平凡); 这与 `LocUipNegSec` 的结论同一个位置.

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `along1`, `raise1→fix⊞`, `raise1→fix₀` | Loop | 任一 `RaiseA1` ⇒ 相干世界里 `β y₀ p₀ ⊞ subst ℓ δ ≡ β y₀ p₀ ⊞ δ`; 特别地 `LoopFix₀At y₀` (可入 $y_0$) | 定理 |
| `raise1→fixω` | Loop | 最小实例 $(x_0, w_\omega)$ 上, `RaiseA1` ⇒ `LoopFix₀At (up ω₀)` | 定理 |
| `famOf→fix` | Loop | 单个增量的相干族化 ⇒ `subst ℓ δ ≡ δ` | 定理 |
| `Legal.fix→famOf`, `Legal.fix→raise1` | Loop | 合法 $X, w$ 且环搬运平凡 ⇒ 族化 / `RaiseA1` | 定理 |
| `uip→fix`, `uip→raise1`, `raise1ω-sat` | Loop | UIP ⇒ 环搬运平凡 ⇒ `RaiseA1` (最小实例) | 定理 (前提 UIP) |
| `raise1-fin` | Loop | 外层界 `finH k`: `RaiseA1` 无条件 | 定理 |
| `fe→raise1₀`, `fe→fix₀ω` | Loop | `S₀`, $X_0=\omega+2$: Funext ⇒ `RaiseA1`, 从而 ω 上的结论 | 定理, 条件 Funext |
| `cross-needs-coh`, `¬CrossLg`, `¬coh×` | Cross | 合法不相干世界里拷贝的界不互推; 去掉 `CohA` 的 `CrossA` 不成立 | 定理 (否定, 只说去掉 `CohA` 的那条律) |
| `Need.need` | Grow | 保旧值 + 新层号从 0 起 + 保相干的延拓 ⇒ 旧可入的弱判定 | 定理 (一般形) |
| `Grow.odec` | Grow | $x_0$, $b$ 长到 $b'$: 旧可入可判定 | 定理 |
| `Grow.ext₀`, `Grow.need₀` | Grow | `Need` 的前提在那里可满足 (常值分量族) | 定理 |
| `SepD.raiseA′-sep` | Dom | 不合法外层界族上一致的 `RaiseA′` ⇒ 分离子 | 定理 |
| `raiseA′→WLPO` | Dom | 同上 ⇒ WLPO | 定理, 条件 `FE₀` |
| `illegal` | Dom | $\alpha$ 某处为真时 $X_\alpha$ 不合法 | 定理 |
| "`LoopFix₀` 不加外延证不出" | — | 同 `LocUipNegLoop` 的判断 | 判断 |
| "$a$ 也长高 / 一般 $X$ 时旧可入可判定" | — | 见判决第 2 条 | 判断 |
| "`copy→⊥` 的前提在 `LevA` 的层号种类上不出现" | — | 见判决第 3 条 | 判断 |

## 每条律为什么是构造一路需要的

- `at1`, `coh1` (`RaiseA1`): 接口原文. `coh1` 必需, 因为 `CrossA` 以 `CohA` 为前提 (`cross-needs-coh` 说明这个前提去不掉), 回灌后的世界还要被认同. 若折叠在节点处只读回一个高度 (构造一路第一个障碍第 1 条), 就要 `RaiseA1`, 或者先族化 (`FamOf`) 再用 `RaiseA′`.
- `CrossA` 的 `CohA` 前提: 取并的目的就是拷贝读同一个界.
- `Need` 的三条: 回灌使外层界长高, 节点的世界要随 $w$ 换成 `GWA X w′`; (a) 旧界不丢 (`_≤GA_` 的跨 $w$ 版本), (b) 新层号的初值, (c) 认同所需的不变量.
- `atA`, `offA` 对模块参数 $X$, $w$: 接口原文; `Dom` 说明它们只能在合法的 $X$, $w$ 上一致地满足.

## 前提实例

- `raise1→fix₀` 的前提 `RaiseA1`: 无条件 `raise1-fin` (外层界有限); 条件 Funext `fe→raise1₀` (`S₀`, 含无限可入层号 ω); 条件 UIP `raise1ω-sat` (最小实例; "Funext ⇒ `HB S₁` 的 UIP" 是判断, 仓库只证了 `HB S₀`). 构造一路 `ColimARaise.uip→raiseA1` 是同一前提的另一实例.
- `famOf→fix` 的前提 `FamOf`: `Legal.fix→famOf` (有 `LoopFixAt` 时), 例如 `uip→fix`.
- `cross-needs-coh`: 世界 `W×` 合法 (`lg×`), 一半前提 `bd₂` 成立.
- `Need.need`: `Grow.ext₀` (定理).
- `Grow.odec`: 任一 $b \lhd_{[a]} b'$, 合法 $a$, $b'$; 例如 `wω` 自身 ($b = b' =$ `hs (hs ω₀)`, `hself`).
- `raiseA′-sep`: 证据 `pa`, `pb` 是闭项, `wω` 合法; 前提族经典可满足 (判断, 元层; 同 `ColimWNeg.raiseA→WLPO`).

## 只否定什么, 不否定什么

- **只否定**: 去掉 `CohA` 前提的 `CrossA` (`¬CrossLg`); 对不合法外层界族 $X_\alpha$ 一致的 `RaiseA′` (条件 `FE₀` 到 WLPO; 无条件到分离子).
- **不否定**: 接口的 `CrossA`, `GlobA`, `LevC′` 是 `KS`; 族增量的 `RaiseA′` (合法 $X$, $w$; 构造一路已造); 单个增量的 `RaiseA1` (只给出它要的强度 `LoopFix₀`, 被函数外延推出, 不是禁忌); 外层世界变大 (在 $x_0$, $b$ 长高时构造的判定); 有限层号; 有 UIP 的模型; "回灌产出对层号一致的族" (`LocUipNegSec` 的形状). 路线状态: 本路没有关闭任何路线.

## 审计

- 编译: 从仓库根 `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/NegColimA.lagda.md +RTS -M6G -RTS`, 退出码 0 (五个文件; 各分篇单独编译也是 0).
- 导入闭包 (`importclosure.py --only OCF.Align. --only OCF.BTBO --only OCF.Free. OCF.Align.NegColimA`): 55 个模块 (本地 42, 库 13), 禁用表命中 0, `--only` 之外 0, 退出码 0. (只给 `--only OCF.Align. --only OCF.BTBO` 时, `OCF.Free.Level` 经 `AdmWCoh → AdmWRaise → UniTrNeg → DiagK3One → DiagK3Zero` 进闭包, 落在 `--only` 之外; 它是树侧模块.)
- 定义级切片 (`depslice.py`, 同一个 `--html` 目录): `NegColimALoop:raise1→fix₀` 76/0/0, `famOf→fix` 72/0/0, `fix→raise1` 89/0/0, `raise1-fin` 84/0/0, `fe→raise1₀` 113/0/0; `NegColimACross:cross-needs-coh` 96/0/0; `NegColimAGrow:need` 9/0/0, `odec` 78/0/0, `ext₀` 89/0/0; `NegColimADom:raiseA′→WLPO` 112/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58.
- 禁用构造: 无 postulate, 无洞, 无 TERMINATING/NON_TERMINATING/NO_POSITIVITY, 无 trustMe, 不开 K; 函数外延 (`Funext`, `FE₀`) 与 UIP 只作前提.
- 行数 (总行 / 非空代码行): 入口 71/6, `NegColimALoop` 222/135, `NegColimACross` 89/51, `NegColimAGrow` 151/101, `NegColimADom` 112/65.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegColimA where

open import OCF.Align.NegColimALoop public
open import OCF.Align.NegColimACross
open import OCF.Align.NegColimAGrow
open import OCF.Align.NegColimADom
```
