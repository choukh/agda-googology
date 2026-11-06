# 第十六轮的否定一路: 入口

> **判决: 否定成立 (第三条规则 `nκ⁺`); 第一条 `in⁺` 正面 (可靠); 第二条 `rk⁺` 未找到否定, 只编译了它的缺口.** 对着接口 [StrRel16If](StrRel16If.lagda.md) 写 (定稿 2026-11-05 11:28, §1–§5; 11:55 增补的 §6 `RkSound` 只读未用). 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 不改任何已有文件, 不改接口与 `StrRel16` 前缀的文件.
>
> **对纲领与目标意味着什么 (判断).** 全部是第 4 层 (关系与语义) 的结论, 不碰树、折叠、合法性. 第三条规则 "节点 ≤ `nκ`" 在语义下不可靠, 原因来自折叠的字面: 节点在第 $0$ 层目标上读状态的**差** `d` (链从坐标层上的读数起), `nκ` 在第 $0$ 层目标上读状态的**第 $0$ 层累计** `z` (回灌的格从运行世界走到运行世界加 `z`). `J²⁺` 把 `d` 与 `d`, `z` 与 `z` 分别相关, 但不把 `z` 与 `d` 相关; 而换世界 `cv` 把 `z` 清零, 保留 `d`, 所以对 `cv` 封闭 (`Lawcv⁺`) 的不变量必然含 "`d` 非空, `z` 为空" 的状态. 在这样的状态上, 节点一边非零, `nκ` 一边为零. 这是值上的错, 不是结构关系少了规则. 没有推出 LPO/WLPO 或判定.

## 1 定理表

| 名字 | 文件 | 陈述 | 档 |
|---|---|---|---|
| `Λκ`, `lΛκ`, `YN`, **`cvYN`** | [NegSR16Kap](NegSR16Kap.lagda.md) | 合法高度 $\mathrm{h\Omega}\,(\lambda\_\to1)$; 状态 `YN` (读 $\omega\cdot(\Omega_t⨾0)$, `z = n0`); `cv q YN ≡ YN` | 定义, 定理 |
| **`Cells.cellZ`** | NegSR16Kap | 路径 `self`, 第 $0$ 格为空 ⇒ `nκ` 回灌的每一格在 `τ₀` 上读 `n0` (对 $n$ 归纳) | 定理 |
| **`¬NK`** (`lowN`, `upK`) | NegSR16Kap | 层 $1$ 节点 `xN` 对层 $\Lambda_\kappa$ 的 `xK`, 动作 `Act`, 状态 `YN`: 第 $0$ 层的和左 $\ge1$, 右 $\le0$ | 定理 (值) |
| **`¬NK₂`** (`lowN₂`, `upK₂`) | NegSR16Kap | `Ωd 1` 对 `Ωd Λκ`, 动作 `Az`: 同上 | 定理 (值) |
| `noRel`, `noRel₂` | NegSR16Kap | 第 $0$ 层值可靠的关系族 (`VS0`) 都不能关联这两对输出 | 定理 |
| **`vsum⁺`**, `vs0⁺`, `inSum`, `sum-mono` | [NegSR16Sem](NegSR16Sem.lagda.md) | `RelX⁺ hz hz` 值可靠 | 定理 |
| `ΩXκ`, **`jN⁺`**, `stepOA⁺`, **`hawAct⁺`** | NegSR16Sem | $\Lambda_\kappa$ 上一切 `TX` 对 `Ωd t ≤⁺ Ωd t′` ($(1,\Lambda_\kappa)$ 用 `nκ⁺`); `J²⁺ YN YN`; `HAW²⁺ Act Act` | 定理 (前提可满足) |
| **`relNK`**, **`¬semNK`**, **`¬sem∀⁺`** | NegSR16Sem | `RelX⁺ (hs hz) Λκ tt tt xN xK` 成立 (`nκ⁺`), `SemX²⁺` 不成立; "`RelX⁺` ⇒ `SemX²⁺`" 不成立 | **否定 (定理)** |
| `inv0`, `AzM.azOA`, **`hawAz`**, `relΩ`, **`¬semΩ`** | NegSR16Sem | `HAW²⁺ Az Az`; `Ωd 1 ≤⁺ Ωd Λκ` 成立, `SemX²⁺` 不成立 | **否定 (定理)** |
| **`Old.¬J²YN`**, **`Old.¬rkPreYN`** | NegSR16Sem | `YN` 满足 `J²⁺` 而不满足旧 `J²`; 以 `YN` 为状态的 `RkPre` 都不成立 | 否定 (定理) |
| `kRK`, `txRK` | NegSR16Sem | 同一实例, 层 $\Lambda_\kappa$ 坐标层 $0$ 的节点在 `TX` 对 $(0,1)$ 上左升右留 (`refl`) | 定理 (实例) |
| **`law⊕⁺`**, **`lawcv⁺`** | [NegSR16Law](NegSR16Law.lagda.md) | 接口的 `Law⊕⁺`, `Lawcv⁺` 成立, 一切 $\Lambda$ | 定理 (正面) |
| `jwk`, `rptwk`, **`sem-in⁺`** | NegSR16Law | 右边加东西保持 `J²⁺` 与上下文; `SemX²⁺ x y′ → In y′ x′ → SemX²⁺ x x′` | 定理 (正面) |
| **`¬genAl⁺`** (`rel1ω`, `adm1ω`) | NegSR16Law | `genAl` 形状的对齐生成对 `RelX⁺ hz hz` 不成立 | 否定 (定理) |

## 2 每条律为什么是构造一路需要的

- **`SemX²⁺` 对 `nκ⁺` 的可靠性.** 接口 §2 说 `nκ⁺` 的目的是 $\Omega_1$ 对 $\Omega_\Omega$ (`StrRel15Bar.¬ΩΩ`), "让 $\Omega^{\mathsf H}$ 处闭项的状态进入不变量". 状态的读数在折叠里被当作链的段再运行 (`HtFeedFold.Chn` 的第 $0$ 段是 `yc (d Y) …`), 所以读数对之间的 `RelX⁺` 要有语义; 构造一路的 "`RelX⁺` ⇒ `SemX²⁺`" 要逐条规则成立. `¬sem∀⁺` 说在层对 $(1,\Lambda_\kappa)$ 上它不成立.
- **带开头 `n1` 的一对 (`¬semΩ`).** 闭项状态里实际出现的是 `Ωd 1 ⨾ …` 对 `Ωd Λκ ⨾ …`; `⨾⁺` 的语义把第二段放在 "状态 ⊕ 第一段输出" 上运行, 动作是 `HAW²⁺` 允许的任意一对. `Az` 是这样一对.
- **`rk⁺` 的前提 (`¬rkPreYN`, `kRK`).** 接口自己写明 `rk⁺` 的前提是旧关系 (严格正性), "在 `NodeSound²⁺` 里不一定能用上". 本文把它编译成: 在 $\Lambda_\kappa$ 上, `J²⁺` 的状态 `YN` 不是旧 `J²`, 而左升右留在这组参数上实际出现. 节点义务 `OblRK²⁺` 按接口要对一切 `TX` 对与实际种类成立.
- **`Law⊕⁺`, `Lawcv⁺`, `in⁺`.** 接口的律与第一条规则; 结论是正面的.
- **`genAl` 形状 (`¬genAl⁺`).** `κ⁺` 在第 $0$ 层目标上的语义要第 $0$ 格的对齐; 旧证明 (`StrRel12Kp`) 由 `z Y ≤ z Y′` 生成.

## 3 前提实例

全部写出, 都是定理: `cp00` (路径), `(cp00 , s∞)` (目标对 $(\tau_0,\tau_0)$), `jN⁺` (状态), `hawAct⁺` 与 `hawAz` (动作), `n0⁺` (上下文), `relNK` 与 `relΩ` (关系成立), `rel1ω` 与 `adm1ω` (`¬genAl⁺`), `kRK`/`txRK` (左升右留出现). `YN` 是 `cv` 的不动点 (`cvYN`), 即它就是换世界之后的状态; 任何非空且对 `cv` 封闭的 `J²⁺` 都含第 $0$ 层累计为 `n0` 的状态.

## 4 只否定什么, 不否定什么

- **否定**: (a) `nκ⁺` 作为 `RelX⁺` 的一条规则在 `SemX²⁺` 下的可靠性 (`¬semNK`, 动作 `Act`); 推广: 任何第 $0$ 层值可靠的输出关系都不能关联那对输出 (`noRel`), 所以不是缺规则的问题. (b) 动作前提只要求 "相关的输入与状态 ⇒ 相关的输出" 时, 带开头 `n1` 的 `Ωd 1` 对 `Ωd Λκ` 也不可靠 (`¬semΩ`). (c) `rk⁺` 以状态 `YN` 为参数时的前提 (`¬rkPreYN`). (d) `genAl` 形状的对齐生成 (`¬genAl⁺`).
- **不否定**: 动作限制为尊重值的一类之后的 (b) (`Az` 区分 `n0` 与 `n0 ⨾ n0`); 动作 `Act` 下 `Ωd 1` 对 `Ωd Λκ` 的语义 (那时 `z` 非空; 没有比较); `rk⁺` 本身的可靠性 `RkSound` (没有找到反例, 也没有证; 判断: 有限 $\Lambda$ 上右边节点的分支带着生产时状态在高层的读数, `J²` 让它支配左边链的起点, 与构造一路 `StrRel16Val.valLK` 一致); `RelX⁺` 里 (`nl …`, `ni …`) 那一对在 `kRK` 的参数上是否可推 (`rk⁺` 的参数存在量化, 没有求逆); `κ⁺` 的可靠性. `in⁺` 是正面的 (`sem-in⁺`, 不用 `NE`).
- **phead 形状 (判断).** 三条规则都带字面证据 (`In` 的路径, `rk⁺` 的 `RKi` 字面与 `RkPre`, `nκ⁺` 的 `self`); 本文的否定没有一条走 "从值求位置". `¬genAl⁺` 要的新对齐构造子可以由 `inE n` 的 $n$ 给出, 不需要搜索.

## 5 修补的方向 (判断, 未试)

`nκ⁺` 的失败点是 `z` 与 `d` 不相关. 加一个不变量 "第 $0$ 层累计支配坐标层上的读数" 与 `Lawcv⁺` 冲突 (`cv` 清零 `z`, 保留 `d`). 可能的出路: `nκ⁺` 只在右边的 `nκ` 前有一段在第 $0$ 层目标上严格非零的输出时用 (`Ωd` 的开头 `n1` 正是这样), 并把动作限制到在第 $0$ 层目标上不输出零的一类 (`Act` 是, `Az` 不是). 这要改接口 (新关系或新的动作前提), 交构造一路定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR16 where

open import Data.Unit using (tt)
open import OCF.Align.HtFeedTree using (hs; hz)
open import OCF.Align.NegSR16Kap public using (Λκ; lΛκ; YN; cvYN; module Cells; ¬NK; ¬NK₂; VS0; noRel; noRel₂)
open import OCF.Align.NegSR16Sem public using (vsum⁺; vs0⁺; jN⁺; hawAct⁺; relNK; ¬semNK; ¬sem∀⁺; hawAz; relΩ; ¬semΩ; module Old; kRK; txRK)
open import OCF.Align.NegSR16Law (hs hz) tt public using (law⊕⁺; lawcv⁺; sem-in⁺; ¬genAl⁺)
```

## 6 账

| 文件 | 行 (代码, 去空行与注释) | 内容 |
|---|---|---|
| `NegSR16Kap` | 85 | 实例 $\Lambda_\kappa$, `YN`, `cellZ`, `¬NK`, `Az`, `¬NK₂`, `noRel` (不依赖接口) |
| `NegSR16Sem` | 139 | `vsum⁺`, `ΩXκ`, `jN⁺`, `hawAct⁺`, `¬semNK`, `¬sem∀⁺`, `hawAz`, `¬semΩ`, `Old.¬J²YN`, `¬rkPreYN`, `kRK` |
| `NegSR16Law` | 63 | `law⊕⁺`, `lawcv⁺`, `sem-in⁺`, `¬genAl⁺` (一切 $\Lambda$) |
| 入口 | 7 | |
| 合计 | 294 | 全部手写, 没有生成文件 |

## 7 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `¬NK`, `cellZ` | `RKy` 的第 $0$ 层回灌读 `z`, `RKi` 的 rise 读 `d`; `cv` 的字面清零 `z` | 树逼的 (否定) |
| `Az`, `¬NK₂` | `HAW²⁺` 只要求关系; `sum-fst W (n0 ⨾ n0)` 字面是 `self` | 树逼的 (否定) |
| `¬J²YN` | `StrRel14If.RelX` 无 `ni` 对 `nκ` | 树逼的 (否定) |
| `sem-in⁺` | `Run` 对 `⨾`, `nl` 的字面 (`Rpt` 只在右边加东西) | 树逼的 (正面) |
| `¬genAl⁺` | `sum-fst b (nl d) = lim 0 self`; `Al` 的五个构造子 | 树逼的 (否定) |

**归类: 提供信息.** 没有新构造子或节点字段, 没有改树与折叠, 没有 `Lab`, 没有记号. 否定划出: 以 `J²⁺` (`z` 与 `d` 分别相关) 为状态前提的语义里, 不能有 "节点 ≤ `nκ`" 的无条件规则.
