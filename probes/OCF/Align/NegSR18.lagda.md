# 第十八轮的否定一路: 入口

> **判决: 否定成立 (`AiNoZ`; `RkSoundTK kD`; `UpSound`, 含时间条件 `DomL`; 跨层传递性); `kJ` 的前提在闭项的状态上不成立且不对 `⊕` 封闭; 去掉时间条件的 (a) 版本不成立. `RkSoundTᶻ`, `RkSoundTK kZ`, `RkSoundTK kJ`, `Trans00` 未找到否定.** 对着接口 [StrRel18If](StrRel18If.lagda.md) 写 (定稿 2026-11-05 14:22, §1–§3; 本文写完时接口没有变更记录之外的改动). 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 不改任何已有文件, 不改接口与 `StrRel18` 前缀的文件.
>
> **对纲领与目标意味着什么 (判断).** 全部是第 4 层 (关系与语义) 的结论, 不碰树、折叠、合法性. `NegSR17` 的缺陷是 "`cv` 清零累计, 保留差": 上升输出在产生时读累计, 保留输出的分支在 `cv` 之后运行. 本轮对作者选的两项修补逐项编译:
>
> - **(a) 限制动作不读累计, 不够.** 累计不只由动作读: 分支里的 `nκ` 在第 $0$ 层目标上回灌, 第 $0$ 格走到 "运行世界 + 累计". 所以动作满足 `NoZ` 时分支动作 `Ai` 仍读累计 (`¬AiNoZ`, $\Omega$-极限处的节点, 动作 `Act`); 去掉时间条件时 `rk⁺` 那一对在值上分开 (`¬RkSoundᶻ-Any`). 在 (a) 下, 挡住这一机制的只有时间条件 `DomL`, 而 `DomL` 在 `cv` 之后不成立 (`NegSR17Time.¬domCv`, 本轮 `¬domY0`).
> - **(c) 保留分支运行时的状态**: 三个变体里, 只比差的 `kD` 挡不住 `NegSR17RkT` 的反例 (`¬RkSoundTK-kD`); 带累计的 `kJ` 太强: 它要求产生时的累计低于 `n0 ⨾ n0`, 闭项的状态 $Y_1$ 就不满足, 且不经 `⊕` 传下去; `kZ` (累计被保留分支状态的第 $0$ 层**读数**支配) 在 $Y_1$ 上成立, 本文没有找到反例.
> - **`Up` 不可靠**, 与传递性无关, 带时间条件 (`DomL`, 即这个节点的产生状态) 也一样 (`¬UpSound-DomL`): `Up` 允许左边是上升输出的任何下界, 上升输出读到的累计就被带到保留输出上.
>
> 没有推出 LPO/WLPO 或判定.

## 1 定理表

| 名字 | 文件 | 陈述 | 档 |
|---|---|---|---|
| `walkLow`, `limAux`, `hAct` | [NegSR18Walk](NegSR18Walk.lagda.md) | `nκ` 回灌的一格沿 $a\lhd b$ 运行值为 `n1` 的分支, 动作至少加一 ⇒ 和 $\ge b$; `Act` 满足动作前提 | 定理 (工具, 一切 $\Lambda$) |
| `noZAct` | [NegSR18Ai](NegSR18Ai.lagda.md) | `Act` 满足 `NoZ` | 定理 |
| `outZ`, `outP`, `aiReadsZ` | NegSR18Ai | $\Lambda_\kappa$, $\Omega$-极限处的节点 `rK`, 分支 `nκ`, 动作 `Act`: 差相同的两个状态 (累计 `n0`, `n1`) 上分支动作的输出, 和 $\le0$ 与 $\ge1$ | 定理 (值) |
| **`¬AiNoZ`**, `¬noZAiK` | NegSR18Ai | 接口的 `AiNoZ` 不成立; `AiK` 不满足 `NoZ` | **否定 (定理, 值)** |
| `neN`, `dK` | [NegSR18K](NegSR18K.lagda.md) | `NegSR17RkT` 的那一对满足 `DomKv kD` | 定理 (前提可满足) |
| **`¬RkSoundTK-kD`** | NegSR18K | `¬ RkSoundTK kD hz (hs hz)` | **否定 (定理, 值)** |
| `¬nl0`, `¬nlP`, `¬low00`, `domKJ→low` | NegSR18K | `kJ` ⇒ 产生时的累计 `RelX⁺ hz hz` 低于 `n0 ⨾ n0`; `n0 ⨾ nl e` 不低于它 | 定理 |
| **`¬domKJ`**, **`¬domKJ-Y₁`** | NegSR18K | 累计形如 `n0 ⨾ nl e` 的状态 (闭项的 $Y_1$ 是) 对一切右边的节点都不满足 `kJ` | 定理 (前提的范围) |
| `kJ0`, **`¬kJ⊕`** | NegSR18K | `kJ` 在 `Y0` 上成立; `Y0 ⊕ Step Y0` 上不成立 (不对 `⊕` 封闭) | 定理 |
| `kZY₁` | NegSR18K | `kZ` 在 $Y_1$ 上成立 (`rkAt` 那一对) | 定理 (正面) |
| `reflLift⁺`, `xU`, `relXU`, `semXU`, `semRXU` | [NegSR18Up](NegSR18Up.lagda.md) | 上升输出的分量 `lift zP ⨾ n1` 在它之下, 第 $0$ 层的语义无条件成立 | 定理 |
| **`¬UpSoundR`** | NegSR18Up | 对一切含 `RelX⁺`、第 $0$ 层值可靠的 $R$, 一切在 $(Y_P,Y_P)$ 上成立的 `Ok`: `¬ UpSound R Ok` | **否定 (定理, 值)** |
| **`¬UpSound-DomL`**, `¬UpSound-Any` | NegSR18Up | `¬ UpSound RelX⁺ (DomL tt YP)`; `¬ UpSound RelX⁺ Any` | **否定 (定理, 值)** |
| `oneL`, `LK`, `¬oneK`, **`¬trans⁺`** | NegSR18Up | `n1 ≤ Lr`, `Lr ≤ Kr` (`rkAt`), `n1 ≤ Kr` 推不出: `RelX⁺` 的跨层传递性不成立 | **否定 (定理)** |
| `noZC1`, `preK`, `kL`, `kR`, `jY0` | [NegSR18Z](NegSR18Z.lagda.md) | 分支为 `nκ` 的节点, 动作 `C1`: `NoZ`, `RkPre`, 种类, 再折叠状态 | 定理 (前提可满足) |
| `lowAi`, `lowL`, `orEq`, `gap`, `¬relGap` | NegSR18Z | 左边 (及其任意再折叠) $\ge\Sigma z_P$; 右边不依赖产生时的累计 (`refl`); 两边以 `Y0` 再折叠时左 $>$ 右 | 定理 (值) |
| **`¬RkSoundᶻ-Any`** | NegSR18Z | 本文的变体 (`RkSoundTᶻ` 去掉 `DomL`) 不成立 | **否定 (定理, 值)** |
| `¬domY0` | NegSR18Z | 上一行的再折叠不满足 `DomL` | 定理 |
| `keptK`, **`brK`** | NegSR18Z | 保留输出的分支字面是 `n0 ⨾ nκ tt κ1`, 不依赖产生状态 | 定理 (`refl`) |

## 2 每条律为什么是构造一路需要的

- **`AiNoZ`** (接口 §1): `RkSoundTᶻ` 只对 `NoZ` 的产生时动作给结论; 链里的节点以分支动作 `Ai` 为动作运行 (`RKi` 的 rise 句, 坐标层 $\ge1$ 时链的段含节点), 要继续用 `RkSoundTᶻ` 就要 `Ai` 继承 `NoZ`.
- **`RkSoundTK v`** (接口 §2): (c) 修补后的 `rk⁺` 可靠性; 要它成立, 且它的前提 `DomKv v` 能由折叠的字面 (`⊕`, `cv`) 得到. `¬RkSoundTK-kD` 否定前者 ($v=$ `kD`); `¬domKJ-Y₁`, `¬kJ⊕` 说 $v=$ `kJ` 时后者在闭项的状态上做不到.
- **`UpSound`** (接口 §3): `Up` 规则要加进关系, 就要它的可靠性; `StrRel17` 的接手清单把 `rk⁺` 看成 "升升义务 + `Up`". 本文否定 `UpSound` 本身.
- **传递性** (接口 §3 的 `Trans00`, `StrRel17` 接手清单第 2 项): `Up` 的可靠性的一个来源. 本文只否定跨层的版本 (`¬trans⁺`), 并说明 `UpSound` 是假的, 所以不能单由传递性得到.
- **去掉时间条件的 (a) 版本** (`RkSoundᶻ-Any`, 本文的变体): 检验 (a) 能否代替时间条件. 不能.

## 3 前提实例

全部是编译过的定理, 没有空真的否定. `¬AiNoZ`: `noZAct`, 闭项参数. `¬RkSoundTK-kD`: `NegSR17RkT.preP`, `(cp00 , u∞ s∞)`, `refl`, `dK`; 再折叠 `cp00`, `hawC1⁺`, `n0⁺`, `jYP` 两次, `(cp00 , s∞)`. `¬UpSoundR`: `EmbR` 与 `VS0R` 对 `RelX⁺` 是 `id` 与 `vsum⁺`, `Ok` 取 `DomL tt YP` (由 `jYP`) 或 `Any` (由 `tt`), `UpSound` 的节点参数是闭项, 种类 `refl`. `¬trans⁺`: `oneL`, `LK`. `¬RkSoundᶻ-Any`: `preK`, `kL`, `kR`, `noZC1`, `(hawC1⁺ , noZC1 , noZC1)`, `jY0`. `¬domKJ-Y₁` 对一切右边的参数成立 (是 "前提不成立" 的定理), 可满足的对照是 `kJ0`.

## 4 只否定什么, 不否定什么

- **否定**: (1) `AiNoZ` (分支含 `nκ` 时; 值的不同, 不只是字面). (2) `RkSoundTK kD hz (hs hz)` (产生时动作取遍旧 `HAW²`, 反例的 `Az` 读累计). (3) `UpSound R Ok`, 对一切含 `RelX⁺` 且第 $0$ 层值可靠的 $R$, 一切在 $(Y_P,Y_P)$ 上成立的 `Ok` (含 `DomL tt YP`, `Any`); 产生时动作 `Az` 读累计 (`UpSound` 不限动作). (4) `RelX⁺` 的跨层传递性. (5) 本文的变体 `RkSoundᶻ-Any hz (hs hz)` (产生时动作 `C1` 满足 `NoZ`; 累计经分支里的 `nκ` 被读).
- **前提的范围 (不是律的否定)**: `kJ` 在累计形如 `n0 ⨾ nl e` 的状态上不成立 (闭项的 $Y_1$), 不对 `⊕` 封闭.
- **未找到否定**: `RkSoundTᶻ` (判断: 在 (a) 下 `cv` 机制只经分支里的 `nκ`, 而 `brK` 说保留输出把同一个 `nκ` 带进再折叠, `DomL` 让两边读到的累计对称; 未比较值). `RkSoundTK kZ` (判断: 累计被读数支配, 读数又被再折叠状态的差支配, 对称; `kZY₁` 是正面的). `RkSoundTK kJ` (前提太窄, 没有比较值). `Trans00` (本文没有否定; 构造一路的 `StrRel18Tr.trans00⁺` 声称证明了它, 本路未复核. 若它成立, 与本文的 `¬UpSoundR` 合起来说: 第 $0$ 层传递, 而 `Up` 仍不可靠, 缺的是 "上升输出的再折叠 $\le$ 保留输出的再折叠" 这一半, 它在 `Az` 的节点上是假的). 限制 `NoZ` 的 `Up` (判断同 `RkSoundTᶻ`). 右边保留的再折叠目标对 (`StrRel17Obs` 的障碍) 本文不涉及.
- 没有推出 LPO/WLPO 或判定.
- **与构造一路的重合 (本路只读了文件头, 未复核).** 构造一路独立得到 `StrRel18Az.¬AiNoZ` (实例是闭项 $\Omega_{\Lambda_\kappa}$ 在折叠里产生的保留节点, 比本文的 `rK` 更贴近折叠), `StrRel18Obs.¬RkSoundTKD`, `StrRel18Obs.¬domKJ` (在 `rkAt` 那一对上), `StrRel18KZ.¬domKZ-P` (`NegSR17RkT` 的反例不满足 `kZ`, 与本文对 `kZ` 的判断一致). 本文的 `¬UpSoundR`, `¬trans⁺`, `¬kJ⊕`, `¬RkSoundᶻ-Any`, `brK`, `walkLow` 不在其中.

## 5 模块

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR18 where

open import OCF.Align.NegSR18Walk public using (module WL; limAux)
open import OCF.Align.NegSR18Ai public using (noZAct; rK; uK; AiK; outZ; outP; aiReadsZ; ¬noZAiK; ¬AiNoZ)
open import OCF.Align.NegSR18K public using (dK; ¬RkSoundTK-kD; ¬low00; domKJ→low; ¬domKJ; ¬domKJ-Y₁; kJ0; ¬kJ⊕; kZY₁)
open import OCF.Align.NegSR18Up public using (xU; relXU; semXU; EmbR; VS0R; ¬UpSoundR; ¬UpSound-DomL; ¬UpSound-Any; Lr; Kr; ¬oneK; Trans⁺; ¬trans⁺)
open import OCF.Align.NegSR18Z public using (noZC1; preK; lowAi; lowL; orEq; gap; ¬relGap; RkSoundᶻ-Any; ¬RkSoundᶻ-Any; ¬domY0; BRK; keptK; brK)
```

## 6 审计

- **冷编译** (2026-11-05): 删掉本组 `.agdai` (逐个写模块名: `NegSR18Walk`, `NegSR18Ai`, `NegSR18K`, `NegSR18Up`, `NegSR18Z`, `NegSR18`; 未动 `StrRel18*` 与接口), 从入口重编: 退出码 0, 约 6 秒, 峰值常驻约 1.0 GB (`-M8G`). 代码块里 `postulate`, 洞, `TERMINATING`, `NON_TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext` 都是 0, 不开 K.
- **导入闭包** (`importclosure.py`, `--only OCF.Free. OCF.BTBO OCF.Align.BrwMid OCF.Align.CumRead OCF.Align.DVal OCF.Align.HtFeed OCF.Align.KNest OCF.Align.KVal OCF.Align.L1Val OCF.Align.LayerTr OCF.Align.NegSR16 OCF.Align.NegSR17 OCF.Align.NegSR18 OCF.Align.NoCumLit OCF.Align.StrRel OCF.Align.SumOne OCF.Align.TLRule`): 入口闭包 89 个模块 (本地 79, 库 10), 禁用表 0, `--only` 之外 0; `Walk`, `Ai`, `K`, `Up`, `Z` 各自单跑 (20, 83, 81, 83, 82 个模块) 也都是 0, 0. 不加 `--only` 时禁用表也是 0.
- **定义级切片** (`depslice.py`, `--html` 由本组入口生成; 正对照 `Om1HnAccept` 及其闭包的 html 从 `NegSR17` 那一轮的 scratch 目录拷来, 未重生成): `¬AiNoZ` 242 块, `¬RkSoundTK-kD` 282, `¬domKJ-Y₁` 203, `¬kJ⊕` 229, `¬UpSound-DomL` 328, `¬trans⁺` 220, `¬RkSoundᶻ-Any` 284, `brK` 240, `walkLow` 116; 记号模块 0, 记号词 0. 正对照 `Om1HnAccept:label-term₀` 1188 块, 记号模块 92, 记号词 58. 切片看不见模块应用, 块数偏少; 记号无关由导入闭包保证.

## 7 账

| 文件 | 行 (代码, 去空行与注释) | 内容 |
|---|---|---|
| `NegSR18Walk` | 37 | `up`, `limAux`, `walkLow`, `hAct` |
| `NegSR18Ai` | 49 | $\Lambda_\kappa$ 的实例, `outZ`, `outP`, `¬AiNoZ` |
| `NegSR18K` | 83 | `dK`, `¬RkSoundTK-kD`, `¬low00`, `¬domKJ`, `¬domKJ-Y₁`, `kJ0`, `¬kJ⊕`, `kZY₁` |
| `NegSR18Up` | 84 | `reflLift⁺`, `xU`, `¬UpSoundR`, `¬UpSound-DomL`, `¬UpSound-Any`, `¬trans⁺` |
| `NegSR18Z` | 119 | 分支为 `nκ` 的实例, `lowAi`, `gap`, `RkSoundᶻ-Any`, `¬RkSoundᶻ-Any`, `¬domY0`, `brK` |
| 入口 | 7 | |
| 合计 | 379 | 全部手写; scratch 里的草稿 (`D1`–`D4`) 按段落搬入, 没有生成脚本入库 |

## 8 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `walkLow` | `HtFeedFold.Walk` 的三句 (路径的 `self`/后继/极限), `κc` 的第 $0$ 格的世界 | 树逼的 (工具) |
| `¬AiNoZ` 的机制 | `Ai` 运行分支的字面; `RKy` 的 `hz` 句与 `κc` 的 `zero` 句读累计 | 树逼的 (否定) |
| `¬RkSoundTK-kD` | `cv` 保留差、清零累计 (`NegSR17RkT` 的机制), `KSt` 的差字面地是 `cv` 之后的读数加一段 | 树逼的 (否定) |
| `¬domKJ`, `¬kJ⊕` | `KSt` 在输入 `n0` 上的累计字面是 `n0 ⨾ n0`; `⊕` 给累计加上第 $0$ 层的输出 | 树逼的 |
| `¬UpSoundR` | `Up` 的左边是上升输出的任意下界; 上升输出的分量 (分支动作的输出) 读产生时的累计 | 树逼的 (否定) |
| `¬trans⁺` | `RelX⁺` 里右边是节点的规则只有字面的 `rk⁺` (`invNi` 的同一事实) | 树逼的 (否定) |
| `¬RkSoundᶻ-Any`, `brK` | 分支里的 `nκ` 在保留输出的分支里原样留下 (`RKk` 的 `Kp ⨾ nκ` 形状, `Kp` 在 `self` 上为空) | 树逼的 |

**归类: 提供信息.** 没有新构造子或节点字段, 没有改树、折叠、合法性, 没有 `Lab`, 没有记号. 否定划出: (a) 管不到分支里的 `nκ` (它在第 $0$ 层目标上读累计); (c) 的 `kD` 太弱, `kJ` 在闭项的状态上不成立且不对 `⊕` 封闭; `Up` 在带时间条件的语义下不可靠, 与传递性无关.
