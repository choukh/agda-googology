# 结构关系, 第十六轮: 扩充的异质关系 `RelX⁺`: 入口

> **判决: PARTIAL (构造一路).** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 不改树、折叠、合法性, 不改已有文件 (只新建 `StrRel16`, `StrRel16If`, `StrRel16Lem`, `StrRel16Val`, `StrRel16Sem`, `StrRel16Fin`, `StrRel16Kr`, `StrRel16Node`).
>
> **对纲领与目标意味着什么 (判断).** 全在第 4 层. (1) 决定性实验通过: `xL` 在目标对 $(0,1)$ 上的两个输出 (链的极限对节点, `StrRel15Bar.¬semXLL` 的那一对) 以产生它们时的状态再折叠一次, 第 $0$ 层的和左边不超过右边 (**`valLK`**, 值的定理), 而且结构上就是 "左边 $\le$ 右边的一个分量" (`valLK⁺`). (2) "节点 ≤ 链极限" 写成一般的分量规则 `in⁺` 后可靠 (**`sem-in`**, 一切层), 左留右升的实例在 `RelX⁺` 里 (**`krAt`**, 无条件), `¬laterV` 的那一对不在 (`¬laterPair`). (3) "链极限 ≤ 节点" 只能写成字面的 `rk⁺`, 它的可靠性 (`RkSound`) 没有证, 是本轮的第一个障碍. (4) "ni 对 nκ" (`nκ⁺`) 被否定一路否定 (`NegSR16`, 主审转告, 见 §4). 关于闭项的值 ($T_\Omega<T_{\Omega+1}$ 或界) 本轮没有结果.
>
> 交付 (按 `AGENTS.md` "交付拆成闭项与值"). (a) 构造: 接口 `StrRel16If`; 状态律 `law⊕⁺`, `lawcv⁺`; 六条规则与 `sem-in`; `semX00⁺` (无条件), `semX0⁺` (条件 `RkSound₀`); `Zero²` 的升升与留留 (坐标层 $0$ 对 $0$ 无条件, 对 $k'$ 条件 `RkSound₀ k′`); 实例 `krAt`, `rkAt`, `rkAtLR`. (b) 值: **`valLK`**: $\Sigma_0(\mathrm{LaterL})\le\Sigma_0(\mathrm{LaterR})$. 闭项的严格增长或界: 没有.

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `In`, `RkPre`, `LeX⁺`/`RelX⁺` (旧八条 + `in⁺`, `rk⁺`, `nκ⁺`), `Emb`, `OA²⁺`, `R²⁺`, `J²⁺`, `Law⊕⁺`, `Lawcv⁺`, `HAW²⁺`, `SemX²⁺`, `NodeObl²⁺`, `NodeSound²⁺`, `NodeSound²⁺₀`, §6 `RkSound`, `RkSound₀` | StrRel16If | 接口 (只有类型) | 定义 |
| `sum-mono`, `pt-ge`, `inSum`, `Lp`, `jPfx`, `V0.embX00`, `V0.vsum⁺` | StrRel16Lem | 分量的和 $\le$ 整棵树的和; 左前缀延长保持 `J²`; 第 $0$ 层对第 $0$ 层旧关系嵌入、`RelX⁺` 值可靠 | 定理 |
| **`valLK⁺`**, **`valLK`** | StrRel16Val | `RelX⁺ hz hz LaterL LaterR`; $\Sigma_0(\mathrm{LaterL})\le\Sigma_0(\mathrm{LaterR})$ | **定理 (值)** |
| **`law⊕⁺`**, **`lawcv⁺`**, `ext⁺`, `jPfx⁺`, `haw↾²⁺` | StrRel16Sem | 接口的两条律; 状态向右延长 | 定理 |
| `sem-n0` … `sem-pr` (`Six`) | StrRel16Sem | 六条规则, 一切层 | 定理 |
| **`sem-in`** (`RunIn.pos`, `runIn`, `posOK`) | StrRel16Sem | `in⁺` 可靠, 一切层 | 定理 |
| **`semX00⁺`** | StrRel16Sem | `RelX⁺ hz hz ⇒ SemX²⁺ hz hz` | 定理 |
| **`Zero⁺.semX0⁺`** | StrRel16Sem | `RkSound₀ L′` ⇒ (`RelX⁺ hz L′ ⇒ SemX²⁺ hz L′`) | 条件定理 (`RkSound₀ L′`) |
| `ΩRX²⁺`, `stepOA²⁺`, `hawAct²⁺`, `hY₁⁺` | StrRel16Fin | 有限 $\Lambda$ 上的动作前提与状态 $Y_1$ | 定理 |
| **`krAt`** | StrRel16Kr | 左留右升: `xL` 对 `xR`, 目标对 $(1,1)$, 状态 $Y_1$: `Out²⁺ … (keep _) rise` | 定理 |
| `rkAt`, `rkAtLR` | StrRel16Kr | 左升右留的两对 (`rk⁺` 的实例) | 定理 |
| **`¬laterPair`**, `¬niN0`, `¬niNl` | StrRel16Kr | `StrRel13Later.¬laterV` 的那一对 (状态 $Y_0$) 不 `RelX⁺` 相关; 节点 $\not\le$ `n0`, 节点 $\not\le$ 全零的链 | 否定 (定理) |
| `Zero².oblRR`, `Zero².oblKK` | StrRel16Node | 左坐标层 $0$, 以坐标层语义 `sem0` 为参数 | 条件定理 (`sem0`) |
| **`Z00.rr00`**, **`Z00.kk00`** | StrRel16Node | 两个坐标层都是 $0$: 升升与留留 (`sem0 = semX00⁺`) | 条件定理 (`Top`, 分支动作 `HAW²⁺`, `J²⁺`; 同 `StrRel15Node`) |
| `ZRk.rrRk`, `ZRk.kkRk` | StrRel16Node | 右坐标层 $k'$ 任意 | 条件定理 (`RkSound₀ k′` 及上一行的前提) |

## 前提实例

- `valLK`/`valLK⁺`: 无前提. 内部用到的前提全部填上: `cp00`, 两个分支动作化成 `Step` (`stepOA²`), `hY₁` 加 `jPfx` (状态 $S^\circ$, $S^*$ 是 $Y_1$ 向右延长二、五次, 由 `Lp` 的 `left` 链逐字检查).
- `krAt`: 无前提; 内部 `hS°` ($S^\circ$ 写出, `jPfx⁺`), `lawcv⁺`, `semX00⁺`, `ΩRX²⁺`, `stepOA²⁺`.
- `rkAt`, `rkAtLR`: `RkPre` 填为 `cp00`, `s∞` / `u∞ s∞`, 分支 `n1ˣ`, `hawAct²`, `n0ˣ`, `hY₁`; `TX` 与两个种类等式 (`refl`).
- `Z00.rr00`/`kk00` 的前提: 与 `StrRel15Node.Zero` 相同, `StrRel15Fin` 的 `cp00`, `hawAi`, `hY₁` 一类的实例在 `⁺` 下同样可写 (`stepOA²⁺`, `hY₁⁺`); 本轮没有另写一个两坐标层都是 $0$ 的实例.
- `RkSound₀ k′`: **没有实例, 也没有否定.** `valLK` 是它在一组参数上的值的那一半 (判断: 它不推出 `RkSound₀`). 主审转告: 否定一路证明以 `YN` 为参数时 `RkPre` 不成立 (`Old.¬rkPreYN`), 没有否定 `RkSound`.
- `¬laterPair` 没有前提.

## 1 决定性实验 (`StrRel16Val`)

`LaterL`: `xL` 在第 $0$ 层目标上的输出 (链的极限) 以第 $0$ 层运行; `LaterR`: `xL` 在第 $1$ 层目标上的输出 (节点) 以第 $1$ 层运行; 两者都以 `Act`, `n0`, $Y_1$ 运行, 读第 $0$ 层. 结果: **左边不超过右边** (`valLK`). 证明的四步见 `StrRel16Val` §2. 关键 (判断, 依据证明): 右边的节点在第 $0$ 层上升时, 分支是 $\omega\cdot(\Omega_1⨾\ldots)$, 其中 $\Omega_1$ 的节点又上升成一条坐标层 $0$ 的链; 这条链从 "再折叠的状态向右延长" 起, 而再折叠的状态与产生 `OutL` 时的状态都是 $Y_1$, 所以 `OutL` (那条坐标层 $0$ 的链) 在它之下 (`StrRel15Node.Zero.oblRR`).

## 2 第一个障碍: `rk⁺` 的可靠性

`RkSound₀ (hs hz)` 要求对**一切** `J²⁺` 相关的再折叠状态 (以及一切 `HAW²⁺` 动作与 `TX` 目标对) 成立. `valLK` 的证明在第 2 步用 "右边内部的状态是产生左边时的状态的延长"; 一般的再折叠状态与产生时的状态 (藏在 `rk⁺` 的数据里) 之间没有关系. 判断: 结构上的证明要么需要语义里带 "再折叠的状态延长产生时的状态" 这一类时间关系 (要改 `SemX²⁺` 的量化, 只增的新接口), 要么需要值上的论证 (再折叠状态很小时, 右边的分支里仍有产生时状态的第 $1$ 层读数, 与 $\Omega_1$ 的节点一起, 值上看仍应支配左边; 没有编译, 也没有写成测试). 没有否定定理, 写 "未走通".

**严格正性.** `rk⁺` 的前提用旧关系 (接口文件头): `LeX⁺` 以层为参数, 构造子的前提里不能出现别的层上的 `LeX⁺`, 动作前提还在负位置 (判断, 依据正性检查的规则; 没有把被拒的定义编进仓库). 所以即便 `RkSound` 成立, `NodeSound²⁺` 的节点情形给出的是 `J²⁺`/`HAW²⁺`, 未必满足 `RkPre`; 否定一路的 `Old.¬rkPreYN` 是这一缺口的一个编译实例 (主审转告).

**其余未做 (接手清单原第 2–3 项).** 一般的 $k\sqsubseteq k'$ (左坐标层不是 $0$) 要坐标层上的 `SemX²⁺ k k′`, 即 `NodeSound²⁺` 本身; 没有开始. $\Omega^{\mathsf H}$ 处的 `HAW` 与 `MonoStep`: 没有开始, 理由见 §4.

## 3 `in⁺`, 与 `¬laterV`

- `sem-in` (一切层): $x'$ 的运行在分量 $y'$ 处的上下文与状态是 $x'$ 的向右延长, 所以 `in⁺` 的前提的语义直接搬过去. 主审转告否定一路也证了它可靠且不用 `NE`; **本路的 `sem-in` 也不用 `NE`** (状态延长只经 `ne⊕` 维持 `J²⁺` 的 `NE` 分量). 接口文件头 "在 `J²` 的状态下 (带 `NE`) … 节点可以落在它下面" 说的是**可推导性** (`krAt` 用的是 $Y_1$ 的读数里含 $\Omega_1$ 的节点), 不是可靠性; `¬laterV` 的那一对不在 `RelX⁺` 里是因为推不出 (`¬laterPair`: 空状态下链的每一项是 `n0`), 与 `NE` 无关. 接口变更记录里补了这一句.
- `krAt` 是左留右升在一个实例上的结论; 一般的 `OblKR²⁺` (一切状态、一切目标对) 没有证 (判断: 要 "状态在坐标层 $k'$ 上的读数含 $\Omega_{k'}$ 的节点, 且该节点在目标层上保留", `NE` 给出前半, 后半要 $k'$ 与目标层的关系, 一般情形要对 $t'\sqsubset k'$ 再下降).

## 4 `nκ⁺` 与 $\Omega^{\mathsf H}$ (依主审转告与判断)

主审转告否定一路的结论: `nκ⁺` 不可靠 (`¬semNK`, `¬sem∀⁺`, `¬semΩ`; 节点在第 $0$ 层读状态的差 `d`, `nκ` 读第 $0$ 层累计 `z`, `cv` 把 `z` 清零而保留 `d`). 本路没有复核那些文件, 只转述. 另一处本路的判断 (未编译): 即便有可靠的 "ni 对 nκ", $\Omega^{\mathsf H}$ 上闭项的状态 $Y_1$ 要 `J²⁺`, 还要 $\Omega_{\omega}=1⨾\mathrm{nl}(\lambda n.\,\mathrm{ni}_{f(n)})$ 对 $\Omega_{\omega+1}=1⨾\mathrm{ni}_{\omega}$ (`emb ω ⊑∞ hs (emb ω)` 是 `TX` 允许的一对). `RelX⁺` 里结论是 "左 `nl`, 右 `ni`" 的规则只有字面的 `rk⁺`. 朴素的 "每一项 $\le$ 节点 ⇒ 极限 $\le$ 节点" 在序数上就不对 ($\Omega\cdot\omega>\Omega$, 判断); 对 $\Omega_{f(n)}$ 一列可行的理由是右边的状态读数含 $\Omega_\omega$ 本身 (`NE`), 那又是 "再折叠状态" 的性质. 所以 (c) 在本接口里走不到.

## 5 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `In`, `in⁺` | `Run` 对 `⨾` 与 `nl` 的两句: 输出的分量是分量的输出 (`runIn`); `RKi` keep/rise 的输出对 | **树逼的** |
| `rk⁺` 的字面结论 | `RKi` 的 rise 句与 keep 句 | **树逼的** (形状); 前提用旧关系是正性逼出的脚手架 |
| `RkPre` | `StrRel15Node.Red².node-red²` 的前提 | 脚手架 (关系侧) |
| `nκ⁺` | `Ωd (hΩ g)` 的字面; 自身世界的分支 | 树逼的形状; 已被否定 (转告) |
| `RkSound`, `RkSound₀` | `semX0⁺` 的条件 | 脚手架 (缺的引理的类型) |
| `valLK` 的证明路线 | `RKi` rise 句 (链从状态在坐标层上的读数起), `BNi`/`Step` 的字面, `Ωd (hs hz)` 的节点 | 树逼的 |

**归类: 提供信息.** 没有新构造子进树或折叠, 没有 `Lab`, 没有记号. `sem-in`, `semX00⁺` 是对一切层/一切 $\Lambda$ 的一步定理; 这一站新用到的字段: `Run` 的 `⨾` 句里第二段的上下文 `w ⨾ nw q x` 与状态 `Y ⊕ Run x`, `Rpt` 的两个分量 (`pos`), 以及 `RKi` rise 句里 `Chn` 的起点 `yc (d Y) (tg self hk lW)` 在再折叠时与 $\Omega_1$ 的节点的链 (`valLK`). 否定 `¬laterPair` 划出: "节点 ≤ 链" 不能对全零的链成立. 缺陷是否变深 (判断): `rk⁺` 的字面形与旧关系前提加深了翻译的形态 (结论形状读自折叠的两句, 前提是脚手架), 它的可靠性是开放的; `in⁺` 不加深 (一般的结构规则, 不看折叠).

## 6 接手清单

1. **`rk⁺` 的可靠性的定义域** (最便宜的下一步): 对 `valLK` 的同一对输出, 以**更小的**再折叠状态 (例如 $Y_1$ 的左右两边都换成 `StrRel15NNode` 的 `YN` 一类 `J²` 状态, 或 $Y_0\oplus\mathrm{Step}\,Y_0$ 在别的世界) 再折叠, 比第 $0$ 层的和. 过: 说明 `RkSound` 有望对一切状态成立, 再找结构证明; 不过: 写成否定, `SemX²⁺` 的量化要改成 "再折叠的状态延长产生时的状态" (新接口, 只增).
2. `rk⁺` 的前提的正性缺口: 若要在 `NodeSound²⁺` 里用 `rk⁺`, 要么换成按层分阶的关系, 要么把前提做成先定义的谓词; 先写最小的否定 (`Old.¬rkPreYN` 已是一例).
3. 一般的 `OblKR²⁺` (§3 末条), 然后一般的 $k\sqsubseteq k'$.
4. $\Omega^{\mathsf H}$: `nκ⁺` 的修补 (否定一路的建议: 只在右边 `nκ` 前有一段第 $0$ 层严格非零的输出时用, 并限制动作) 与 §4 的 "极限对节点" 一对; 两者都在 `MonoStep Ωᴴ` 之前.

## 7 审计

- 冷编译 (2026-11-05): 删掉本组 8 个模块的 `.agdai` (逐个写模块名, 未动 `NegSR16*`), 从入口重编: 退出码 0, 约 42 秒, 峰值常驻约 5.5 GiB (`-M6G`; 其中 `StrRel16Val` 单独约 30 秒, 活数据约 3.1G, 余量小, 复核建议 `-M8G`). 代码块里 `postulate`, 洞, `TERMINATING`, `NON_TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext`, K 都是 0.
- 导入闭包 (`importclosure.py`, `--only` 同 `StrRel15`): 入口闭包 81 个模块 (本地 71, 库 10), 禁用表 0, `--only` 之外 0.
- 定义级切片 (`depslice.py`): `valLK` 265 块, `valLK⁺` 264, `krAt` 252, `rkAt` 196, `¬laterPair` 198, `sem-in` 158, `semX00⁺` 196, `rr00` 178, `kk00` 200, `rrRk` 180; 记号模块 0, 记号词 0. 正对照 `Om1HnAccept:label-term₀` 1188 块, 记号模块 92, 记号词 58. 切片看不见模块应用, 块数偏少; 记号无关由导入闭包保证.
- 行数 (代码, 去空行与注释): If 154, Lem 85, Val 53, Sem 144, Fin 35, Kr 74, Node 98 (其中 `Zero²` 一节由 `StrRel15Node.Zero` 文本替换得到, 生成脚本没有入库, 改动是逐字的名字替换, 判断), 入口 10; 合计 653.

## 0 模块

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel16 where

open import Data.Unit using (tt)
open import OCF.Align.StrRel16Lem public using (sum-mono; pt-ge; inSum; Lp; module Pf; module V0)
open import OCF.Align.StrRel16Val public using (LaterL; LaterR; valLK⁺; valLK)
open import OCF.Align.StrRel16Fin public using (module FinΛ⁺)
open import OCF.Align.StrRel16Kr public using (krAt; rkAt; rkAtLR; ¬niN0; ¬niNl; ¬laterPair)
import OCF.Align.StrRel16If
import OCF.Align.StrRel16Sem
import OCF.Align.StrRel16Node
```
