# 结构关系, 第十四轮的否定一路: 入口

> **判决: 部分 (否定成立的三条, 写不出的两条).** 对着接口 [StrRel14If](StrRel14If.lagda.md) 写: 定稿 10:18 的 §1–§5 与 10:40 增补的 §6 (`NodeObl⁼`). 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 不改任何已有文件, 不改接口与 `StrRel14` 前缀的构造文件.
>
> **对纲领与目标意味着什么 (判断).** 全部是第 4 层 (关系与语义) 的结论, 不碰树、折叠、合法性. 三条否定都落在 "状态前提" 与 "对齐给出的分支对" 上, 不落在树上. 它们说: 跨坐标层的节点规则 (a) 不能用同目标层的状态关系 (`R∀X`) 作前提; (b) 改用接口的不变量 `J` 时, 只要 `J` 含一个 "右边在高坐标层上读数为零" 的状态对就不行, 因为 `⊕J` 对任意相关输出封闭; (c) `κˣ` 只取 `CPᴸ` 是必要的, 但对齐 (`Al`) 给出的走法位置对可以不是 `CPᴸ`, 在合法的 Ω-极限层上还可以值递减. 没有推出 LPO/WLPO 或判定; 三条都是 "这条律在可满足的前提下是假的" 一类.

## 1 定理表

| 名字 | 文件 | 陈述 | 档 |
|---|---|---|---|
| **`¬NodeSound`** | [StrRel14NegNode](StrRel14NegNode.lagda.md) | `¬ NodeSound` (接口 §4, 实例 $\Lambda=2$) | 否定 (定理) |
| **`¬semX`**, `relX` | StrRel14NegNode | `RelX Λ₂ Λ₂ tt tt xL xR` 成立 (`niˣ`), `SemX` 不成立 | 否定 (定理) |
| **`¬oblRR`**, **`¬oblRR⁼`** | StrRel14NegNode | §4 的 `OblRR` 与 §6 的 `OblRR⁼` 在一组满足 `SemX` 全部前提的参数上不成立 | 否定 (定理) |
| `vsumX`, `ΩRX`, `haActX` | StrRel14NegNode | 第 0 层 `RelX hz hz` 值可靠; $\Omega_t$ 自 `RelX` 相关; `Act` 满足 `HAWX` (不含 Ω-极限的 $\Lambda$) | 定理 (辅助) |
| **`inv-kill`**, **`inv-obl`** | [StrRel14NegInv](StrRel14NegInv.lagda.md) | 任意 `I : Inv`, `J tt tt Y Y′`, $Y'$ 在坐标层 1 上读数为零树 ⇒ $(Y\oplus\Delta_v, Y'\oplus\Delta_v)$ 仍 `J` 相关, 且第 0 层值左 > 右; 写成接口类型: 那里 `OblRR⁼` 不成立 | 否定 (定理) |
| `inv-kill₀`, `I∀`, `r∀c₀`, `kill-R∀c` | StrRel14NegInv | 特例 `J ∋ (Y₀,Y₀)`; `J = R∀c` 是一个 `Inv` 且含 $(Y_0,Y_0)$ | 定理 (前提实例) |
| `runZ`, `chZ`, `sumZ` | StrRel14NegInv | 零树的折叠与链仍是零树, 和不超过底 | 定理 (辅助) |
| **`cpω`**, **`¬⊲₁₂`**, `¬⊲₂₁`, **`¬cpᴸ`** | [StrRel14NegLit](StrRel14NegLit.lagda.md) | $\omega$ 的两种写法上的 `CP` 分支对, 两个方向都无字面 $\lhd$, 不是 `CPᴸ` | 否定 (定理) |
| **`Λh`**, `lΛh`, **`hdec`**, **`¬litH`**, **`¬relBr`** | StrRel14NegLit | 合法的 $\mathrm{h\Omega}\,(\mathrm{emb}\circ h)$, $h$ 字面单调; 在 `cpω` 上左坐标层值严格大, 无 $\sqsubseteq_\infty$, 两分支不 `RelX` 相关 | 否定 (定理) |
| **`NoHt.no-ht`** | StrRel14NegLit | 没有沿 `_⊏_` 严格单调的 $H\to A$ | 否定 (定理) |

## 2 每条律为什么是构造一路需要的

- `NodeSound` (§4): 接手清单第 2 项的可靠性本身, 接口直接写成类型. `OblRR`/`OblRR⁼`: 构造一路 `StrRel14Rk.node-red` 把 `SemX` 归约到这三种义务, 升升是其中之一.
- `Inv.⊕J` (§2): `semJ` 只经 `toR`, `cvJ`, `⊕J` 用状态 (`StrRel14J` 文件头). 跨坐标层规则若改用 `J` 作状态前提, 要在一切 `J` 相关的状态上成立, 包括 `⊕J` 造出来的.
- `κˣ` 的 `CPᴸ` (§1, §3): `RelX` ⇒ `SemX` 的 `nκ` 一句要在折叠走到的位置对上用分支关系; 走到的位置对来自 `Al`, 只带值.

## 3 前提实例

全部写出: `relX` 的分支前提 `n1ˣ`; `cp00`; `haActX tt Λ₂`; `n0ˣ`; `hYvX`; 目标 `τ₀`; `I∀` 与 `r∀c₀` (`inv-kill₀` 的前提); 零树前提对 $Y_0$ 是 `z0`; `cpω` 的对齐、领先量、顶端可比、自洽; `lΛh` (合法性).

## 4 只否定什么, 不否定什么

- `¬NodeSound`, `¬semX`, `¬oblRR`, `¬oblRR⁼`: 否定以 `R∀X` (同目标层) 为状态前提的跨坐标层节点可靠性. 不否定换成别的状态前提之后的版本, 不否定 `niˣ` 作为构造子, 不否定 `semJ` (同层).
- `inv-kill`, `inv-obl`: 否定 "`J` 含某个右边坐标层 1 读数为零树的状态对" 的不变量下的跨坐标层升升义务. **不否定** `StrRel14J.I₁` (`NE` 要求一切目标上的读数含 $\omega\cdot(\Omega_t⨾y)$, 不含零树读数). 判断: 本办法对 `I₁` 不起作用. 原因是 `R∀c` 使右边第 0 层的读数不小于左边, 而右边坐标层 1 的读数里 $\Omega_1$ 的节点上升时读的正是第 0 层读数; 没有编译.
- `cpω`, `Λh`, `¬relBr`: 否定 "`CP` ⇒ 字面 $\lhd$", "合法 Ω-极限层的分支坐标层在 `CP` 对上值单调", 以及 "`CP` 对上的 $\Omega_{\Lambda_h}$ 分支 `RelX` 相关". 不否定 `κˣ` 的可靠性 (没有编译 $\Lambda_h$ 上折叠的值), 不涉及 $\Omega^{\mathsf H}$ ($\mathrm{emb}$ 对值单调, 判断).
- `no-ht`: 只否定 "经一个值函数 $H\to A$" 的写法.

## 5 三个嫌疑的结论 (简报 §2)

| 嫌疑 | 结论 | 档 |
|---|---|---|
| (i) 跨目标层的状态不变量落入 `phead→LPO` 形状 | **写不出 LPO.** 接口的律都带字面证据 (`⊑∞`, `CPᴸ`, `AP`), 没有 "只给值求位置" 的字段. 能编译的是更弱也更直接的否定: 同目标层的状态前提下节点可靠性是假的 (`¬NodeSound`), `⊕J` 的封闭使含零树读数的 `J` 也不行 (`inv-kill`). `no-ht` 说 "值上的 `rk-mono`" 不能经值函数写. | 否定 (定理) + 判断 |
| (ii) 左留右升吸收所需的 `Al` 新构造子破坏已有性质 | **没有否定.** 构造一路的 `¬alCell0` 已说现有 `Al` 对不齐 `MonoStep Ωᴴ` 第 0 格 (我在 scratch 里独立写出了同一个三行证明, 不重复入库). 判断: 需要的不是 "左边单走一步" (那是 `StrRel8Neg.¬nwˡ` 杀掉的 `nw` 形状), 而是 "错一格" (左第 $n$ 位对右第 $n+1$ 位); 它要求关系里有 `⨾` 与 `nl` 的重组规则 (值上由 `StrRel12Rel.Tail` 的 `tup`/`tdn` 保证, 结构上 `LeX` 没有). 这条规则在第 0 层喂 `genAl` 时与新构造子互相依赖, 没有编译出矛盾. 构造一路的 `shiftV` 是它的值版. | 判断 |
| (iii) 不经 `CP` 的顶层比较在 $\Omega^{\mathsf H}$ 处需要跨世界的 Ω-节点相关 | **在 `RelX` 里不需要额外的东西.** $\Omega^{\mathsf H}$ 的分支在 `CPᴸ` 对上由 `emb⊲` 给出字面 $\sqsubseteq_\infty$, 所以 `κˣ` 的前提成立 (判断, 依据 `StrRel14Rk.κlit`). 障碍转到 (i): 错一格之后左第 $n$ 位 (坐标层 $\mathrm{emb}\,n$) 对右第 $n+1$ 位, 全是跨坐标层的节点对, 由升升义务承担, 而 `¬oblRR⁼`/`inv-obl` 划出了它不能用的状态前提. 在一般的 $\mathrm{h\Omega}\,g$ 上还有 `Λh` 这种值递减的 `CP` 对. | 判断 + 定理 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel14Neg where

open import OCF.Align.StrRel14NegNode public using (¬NodeSound; ¬semX; relX; ¬oblRR; ¬oblRR⁼; module G)
open import OCF.Align.StrRel14NegInv public using (Zt; inv-kill; inv-obl; inv-kill₀; I∀; kill-R∀c)
open import OCF.Align.StrRel14NegLit public using (cpω; ¬⊲₁₂; ¬⊲₂₁; ¬cpᴸ; Λh; lΛh; hdec; ¬litH; ¬relBr; module NoHt)
```

## 6 账

| 文件 | 行 (代码, 去空行与注释) | 内容 |
|---|---|---|
| `StrRel14NegNode` | 65 | `vsumX`, `ΩRX`, `haActX`, `¬NodeSound`, `¬semX`, `¬oblRR`, `¬oblRR⁼` |
| `StrRel14NegInv` | 74 | `Zt`, `runZ`, `chZ`, `sumZ`, `inv-kill`, `inv-obl`, `I∀` |
| `StrRel14NegLit` | 173 | `cpω`, `¬cpᴸ`, `Λh`, `hdec`, `¬litH`, `¬relBr`, `no-ht` |
| 入口 | 5 | |
| 合计 | 317 | 全部手写, 没有生成文件 |

审计 (2026-11-05): 删掉本组 4 个 `.agdai` 后从入口编译, 退出码 0, 约 5 秒, 峰值常驻约 0.8G (`-M6G`). 代码块里 `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext` 都是 0. 导入闭包 (`importclosure.py`, `--only` 同 `MonoPort7`/`MonoPort9`, 前缀 `OCF.Free.Level`, `OCF.BTBO`, `OCF.Align.` 下 `CumReadCF`, `TLRule`, `TLOpsW`, `SumOne`, `BrwMid`, `LayerTr`, `CvFold`, `CvHigh`, `CvLayer`, `NoCumLit`, `L1Val`, `DVal`, `HtGen`, `HtFeed`, `HtCross`, `KVal`, `KNest`, `MonoPort`, `StrRel`): 四个文件各自单跑都是禁用表 0, `--only` 之外 0 (入口闭包 66 个模块, 本地 56). 定义级切片: `¬NodeSound` 到达 176 块, `¬oblRR⁼` 170, `inv-obl` 191, `inv-kill` 166, `¬relBr` 81, `¬cpᴸ` 73, 记号模块 0, 记号词 0; 正对照 `Om1HnAccept:label-term₀` 1188 块, 记号模块 92, 记号词 58.

## 7 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `¬NodeSound` 的反例 | `StrRel13Val` 的同一对节点与状态; `SemX` 的状态前提 `R∀X` 的字面 | 树逼的 (否定) |
| `inv-kill` | `Inv.⊕J` 对任意 `OAc` 相关输出的字面; `RKi` 的 `rise` 句从各自坐标层读状态 | 树逼的 (否定) |
| `cpω`, `Λh` | `Al` 的 `aP` 只带值; `LgH (hΩ g)` 只要求字面单调 | 树逼的 (否定) |

**归类: 提供信息.** 没有新构造子或节点字段, 没有改树与折叠, 没有 `Lab`, 没有记号. 否定划出不能有的形状: 同目标层的状态前提 (对跨坐标层), 含零树读数对的不变量, `CP` 分支对上的节点关系.
