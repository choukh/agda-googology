# 高度来自折叠的输出

> 主线第 3 步 (摆脱侧). 入口. **判决: PARTIAL (交付 (a)).** 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K. 定义不读记号, 没有验收文件, 没有打开 `EBO`, `Lab`, 标签.
>
> 一句话: 第 1 层的差树 (折叠在第 1 层目标上的输出) 有一个**读成高度的算子** `rd`, 读出来一律满足 `LgH`, 前提只有底合法 (`Lg-rd`). 关键是一条对任意分支 $g$ 的一步定理 `cont→LgH`: $\Omega$-分支在极限坐标处**字面连续** ($g(\lim f)\equiv\mathrm{hl}(g\circ f)$), 在后继坐标处步进, 就沿坐标的一切第一位置单调. `no-weak` 缺的那条字段就是连续 (`drop-lim`); 两条字段都不能去掉 (`drop-suc`). 用 `rd` 写出回灌算子 `Fb` ($h\mapsto$ 以 $1\boxplus h$ 为最高层折叠, 取第 1 层输出, 接在 $h+1$ 后读回), 闭项 `T-fbω` 的高度 `Λω` 是 **从 $0$ 出发**, 只用 `Fb` 与 ℕ-对角生成的, 不用 [HtFeedHt](HtFeedHt.lagda.md) 的任何生成规则, 连 $\Omega$ 也是输出里读出来的 (`Λ₁-Ω`). 增长: 在每个回灌高度上与在 `Λω` 上, `HtFeedGrow.Sup` 那一档的定理成立 (`Sup-fb`, `Sup-ω`).
>
> **没有做到的:** 闭项之间跨高度的比较 (`T-fb (n+1)` 对 `T-fb n`); 回灌的 $\Omega$-迭代 (`no-total` 划出障碍); 一切值. 强度的读法都是判断.

## 设计

| 件 | 定义 | 文件 |
|---|---|---|
| 连续的分支 | `Cont g`: `c-lim` ($g(\lim f)\equiv\mathrm{hl}(g\circ f)$), `c-suc` ($g\,c\lhd_{[0]}g(c+1)$), 起点与后继保合法 | [HtOutRead](HtOutRead.lagda.md) |
| 一步定理 | `cont→LgH : Cont g → LgH (hΩ g)`; 单调对坐标的路径归纳, 不要坐标合法 | 同上 |
| 对坐标递归 | `nb b s`: $g(0)=b$, $g(c+1)=s\,c\,(g\,c)$, $g(\lim f)=\mathrm{hl}(g\circ f)$; `nb-cont`; `HtFeedHt.it` 是特例 (`it-cont`) | 同上 |
| 读法 | `rd b x`: `n0, n1, ⨾, nl` 照和读; `ni`, `nκ` 读成 `hΩ (nb b s)`, 坐标 $c$ 上的增量是差树在坐标 `toD c` (`ni`) 或世界 $W+$`toD c` (`nκ`) 上的分支 | 同上 |
| 合法 | `Lg-rd`: 底合法则读出合法, 无别的前提; `rd-fst`: 底是第一位置 (世界 $0$) | 同上 |
| 第 1 层输出 | `out₁ h`: 以 $1\boxplus h$ 为最高层折叠 `Ωd`, 取目标 $(1,\ \text{世界 }1)$ 上的差; 折叠是 `HtFeedClosed.At` 的, 不改 | [HtOutFeed](HtOutFeed.lagda.md) |
| 回灌算子 | `Fb : HL → HL`, `Fb h = rd (h+1) (out₁ h)`; `HL = Σ H LgH` | 同上 |
| 回灌高度 | `Λs n = Fb^n 0`, `Λω = hl Λs`; 对照 `Λψ = Fb Ωᴴ` | 同上 |
| 闭项 | `T-fb n`, `T-fbω`, `T-ψΩΩ`, `fgh = FGH (ord T-fbω)`; 都是 `HtFeedClosed.TΛ` 的实例 | 同上 |

**为什么 `H` 的坐标不必改成差树.** [HtFeed](HtFeed.lagda.md) 的第一个障碍 2 判断要用 [BrwHigh](BrwHigh.lagda.md) 的正规节点, 把 $\Omega$-分支的坐标改成差树. 这里不必: 坐标仍是 `A`, 分支对坐标结构递归, 极限坐标上取 `hl`, 沿坐标的第一位置单调对路径归纳就有 (`cont-mono`). `BrwHigh` 的正规节点在极限坐标上取部分和 (`Ig`), 不是 `hl (g ∘ f)`, 所以那里要差树坐标. 差树坐标在这里只出现一次: 喂给差树分支的 `toD c`.

**为什么不用读回增量.** `incr-blind` 说只存分支时增量读不回来. 这里高度只作下一次折叠的层 (`StH`, `D L` 对它结构递归), 不再当差树输入走, 所以不用读回.

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `cont-mono`, **`cont→LgH`** | HtOutRead | 对一切 $g$: `Cont g` 推出沿坐标一切第一位置单调, 推出 `LgH (hΩ g)` | 定理 |
| `nb-cont`, `it-cont` | HtOutRead | 对坐标递归的分支都是 `Cont`; `HtFeedHt.it` 也是 | 定理 |
| `rd-fst`, **`Lg-rd`** | HtOutRead | 第 1 层的一切差树读成合法高度, 前提只有底合法 | 定理 |
| `Fb`, `Λs`, `Λω`, `lΛω` | HtOutFeed | 回灌算子与回灌高度, 合法性是 `Lg-rd` 的调用 | 定义; 合法性是定理 |
| `T-fb`, **`T-fbω`**, `T-ψΩΩ`, `Lg-T-fbω`, `fgh` | HtOutFeed | 闭项; `T-fbω` 的高度只由回灌与 ℕ-对角生成 | 定义; 合法性是定理 |
| `fb-fst`, `fb-st`, `Λ-st` | HtOutFeed, HtOutGrow | $h+1\lhd_{[0]}\mathrm{Fb}\,h$ | 定理 |
| `Λ₁-Ω` | HtOutFeed | `Λs 1` 的最外构造子是 `hΩ` (起点是 $0$) | 定理 (`refl`, 对具体项的计算) |
| **`Fb-Ω`**, `Λ-Ω` | HtOutGrow | 对一切 $g$: `Fb (hΩ g)` 是 `hΩ g′`; 所以 `Λs (n+1)` 都是 $\Omega$-极限 | 定理 (`Fb-Ω` 是对变量 $g$ 的 `refl`) |
| **`Sup-fb n`** | HtOutGrow | 在 `Λs (n+1) = hΩ gₙ` 上, `ΩSup`: 闭包站严格高于前缀站的任意可数子族的上确界 | 定理 |
| **`Sup-ω`**, `pre<-ω` | HtOutGrow | 在 `Λω` 上, 前缀站第 $j$ 段过层 $\Lambda_j$; 同上 | 定理 |
| **`drop-lim`** | HtOutNeg | `gx` 满足后继步进与其余字段, 不连续, `¬ LgH (hΩ gx)` | 否定, 定理 |
| **`drop-suc`** | HtOutNeg | `gd` 连续, 满足其余字段, 不步进, `¬ LgH (hΩ gd)` | 否定, 定理 |
| `no-loop` | HtOutNeg | 没有 $h+1\lhd h$ | 定理 |
| **`no-total`** | HtOutNeg | 连续且后继严格变大的分支不能在一切坐标 (含不合法的) 上都合法 | 否定, 定理 |
| `a6`, `a7`, `b10`, `b11`, `c12`, `d12` | HtOutTest | 见下 | 有限测试 |

**`Sup-fb`, `Sup-ω` 说什么, 不说什么.** 与 `HtFeedGrow.Sup` 同一档: 一个折叠实例之内, 闭包站高于前缀站的任意可数子族. 新的只是节点族: 层是回灌高度 $g_n(j)$ 或 $\Lambda_j$. **不说** `T-fb (n+1)` 高于 `T-fb n`: 两者在不同的折叠实例里, 要换实例的引理 (`HtFeed` 第一个障碍 1).

**否定的范围.** `drop-lim`, `drop-suc` 只说 `Cont` 的两条形状字段各自不能去掉, 不说 `LgH (hΩ g)` 推出 `Cont g`. `drop-lim` 说 "只在后继处步进" (`LayerTr` 的 `LgB` 对 `bi` 的要求) 推不出 `LgH`; 不说 `LayerTr.toB` 的每个读法都不合法. `no-total` 只否定 "连续, 后继严格变大, 一切坐标上合法"; 不否定把 $\Omega$-分支的定义域改成合法坐标, 也不否定让折叠在不合法的最高层上有定义.

## 闭项与读法

**读法都是判断** (纸面, 按 `HtFeed` 的读法: `TΛ Λ` 读 $\psi_0(\Omega_\Lambda)$, 第 1 层目标上的输出读 $\psi_1$ 的那一段; 换算 $\psi_1(\Omega)=\Omega^2$, $\psi_1(\Omega_2)=\varepsilon_{\Omega+1}$ 是手算的序数算术, 不是定理). `toD` 在极限坐标处值不忠实, 读法默认它不改分支的上确界, 这也是判断.

| 闭项 | 高度 | 读法 (判断) |
|---|---|---|
| `T-fb 1` | `Fb 0` $=\mathrm{rd}(1,\psi_1(\Omega_1))$ | $\psi_0(\Omega_{\Omega^2})$ |
| `T-ψΩΩ` | `Fb Ωᴴ` (对照, 底用了 `HtFeedHt` 的 $\Omega$) | $\psi_0(\Omega_x)$, $x=\psi_1(\Omega_\Omega)$, 不能用 $\Omega$ 的算术写 |
| `T-fb 2` | `Fb (Fb 0)` | $\psi_0(\Omega_{x_2})$, $x_2=\psi_1(\Omega_{\Omega^2})>\psi_1(\Omega_2)=\varepsilon_{\Omega+1}$, 不能用 $\Omega$ 的算术写 |
| `T-fb (n+1)` | `Fb^{n+1} 0` | $x_{n+1}=\psi_1(\Omega_{x_n})$ |
| `T-fbω` | `hl Λs` | $\psi_0(\Omega_{x_\omega})$, $x_\omega=\sup_n x_n$ |

按读法, `T-fb 2` 已高于 `HtFeed` 的一切闭项 (那里最高读 $\psi_0(\Omega_{\Omega^{\Omega^\omega}})$, $\Omega^{\Omega^\omega}<\varepsilon_{\Omega+1}$), `T-ψΩΩ` 是 README 记的 "下一障碍" $\psi_0(\Omega_{\psi_1(\Omega_\Omega)})$ 那一站. 这些都没有定理: 没有树与参照树之间的 $\preccurlyeq$, 没有跨高度的比较.

**有限测试** ([HtOutTest](HtOutTest.lagda.md), `same d 2`):

| 比较 | 结果 |
|---|---|
| `T-fb 1` 对 `T-Ω` | 深度 6 同, 深度 7 不同 |
| `T-fb 1` 对 `T-Ωk 2` (`HtFeed` 读 $\psi_0(\Omega_{\Omega^2})$) | 深度 10 同, 深度 11 不同 |
| 对照: `T-Ωk 3` 对 `T-Ωk 2` | 深度 12 同 |
| `T-fb 2` 对 `T-fb 1` | 深度 12 同 |

第 1 行说 `T-fb 1` 不是 $\Omega$ 那一站的形状. 对照行说这个比较器在深度 12 分不开 $\Omega^2$, $\Omega^3$ 两站, 所以第 2, 4 行对值没有分辨力.

## 第一个障碍

1. **跨高度的比较.** 同 `HtFeed` 的第一个障碍 1: 每个闭项在自己的折叠实例里. 所以 "回灌一次严格变大" 只在高度上是定理 (`fb-fst`), 在闭项上没有.
2. **回灌的 $\Omega$-迭代.** `Fb` 只在合法高度上有定义 (`HtFeedFold` 的模块参数要 `LgH Λ`, `cmpH` 用它). `HtFeedHt` 的 `Ωit` 要全函数 `H → H`; `hΩ` 的分支对一切 `A` 都要有值, 而 `no-total` 说连续且严格变大的分支在不合法的坐标上必有不合法的值, 所以不能在递归里随身带着合法性去调用 `Fb`. 剩下的两条出路 (分支的定义域改成合法坐标; 折叠对不合法的最高层也有定义) 没有试, 未走通, 没有否定定理. 判断: 前者要改 `H`, 由作者定.
3. **值.** 没有任何一站与参照树有 $\preccurlyeq$; `toD` 在极限坐标处取部分和, 不忠实 (忠实的 `dif` 要坐标合法, 分支是全函数拿不到).
4. 判断: $x_\omega$ 之上要第 2 层的输出作高度, 它的分支吃第 1 层的树, 要第三数类的高度树.

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `Cont` 的两条字段 (极限连续, 后继步进) | `LgH` 的 $\Omega$-单调沿一切第一位置 | **树逼的** (`drop-lim`, `drop-suc`; `no-weak`) |
| `nb` (对坐标递归) | 布劳威尔树的迭代, 同 `HtFeedHt.it` | 树侧 |
| `rd` 的 `n0`, `n1`, `⨾`, `nl` | 和的读法 (同 `sum`, `LayerTr.toB`) | 树侧, 沿用 |
| `rd` 的 `ni`, `nκ` 读成 `hΩ (nb …)`, 增量是差树的分支 | 增量就是折叠算出的差 (`BrwHigh`) | 形状由 `Cont` 逼出; 增量的取法沿用 `BrwHigh` |
| `toD`: 坐标 $c$ 喂给差树分支, 极限取 `nl` | 差树分支吃 `D₀`, 高度分支吃 `A` | **选择** (值不忠实; `dif` 要 `Lg`) |
| `nκ` 的世界取 $W+$`toD c` | 世界要路径与合法 | 树逼的 (`sum-fst`, `Lg-sum`); 形状同 `BrwHigh` 的 `mK` |
| 读第 1 层目标 | 第 0 层输出读成高度只是可数的 (`HtGen.no-top` 那一族); 第 $\ge2$ 层的分支吃第 1 层的树, `H` 装不下 | 判断: 树的类型逼的; 受记号启发 ($\psi_0(\Omega_{\psi_1(\dots)})$ 的形状), 定义里没有记号 |
| 最高层取 $1\boxplus h$ (`top⁺`) | 目标要字面是最高层的第一位置 (`Tg` 的 `tm`) | 树逼的 |
| `Fb` 的底取 $h+1$ | 新高度字面严格高于旧的 | 选择 |
| `Fb` 定义在 `HL` 上 | 折叠要最高层合法 | 树逼的; 见障碍 2 |
| ℕ-对角 `Λω` | 布劳威尔极限, 步进由 `fb-st` | 树侧 |
| 折叠本体, `S = ω⋅`, `Ωd` | `HtFeed` 原样 | 形状受旧树影响 (同 README 翻译账 `HtFeedTree`, `HtFeedFold`) |

**按 `AGENTS.md` 归类: 提供信息; 摆脱翻译的一步.**
- 加深的三个标志: 新构造子或节点字段读自基本列规则: **没有** (没有新类型; `H`, `D₊` 不变). 闭包定理新增专属前提: **没有** (`Lg-rd` 只要底合法; `Sup-fb`, `Sup-ω` 是 `HtFeedGrow` 的实例, 不加前提). 只能用 `Lab` 验收: **不是**.
- 提供信息的三个标志: 对结构参数的一步定理: **有** (`cont→LgH` 对任意 $g$, 新用到的字段是极限坐标上的 `hl`; `Fb-Ω` 对任意 $g$, 归约走的是折叠的 `nκ` 在非零目标上的保留 `RKk` (看定义的判断; 定理本身是 `refl`); `Lg-rd` 对一切第 1 层差树). 序数值验收: **没有**. 否定定理划出字段: **有** (`drop-lim`: 连续不能少; `drop-suc`: 步进不能少; `no-total`: 分支不能处处合法).
- 摆脱了什么: `HtFeed` 的 "高度是给定的数据" (它的没有做到的那一条). `T-fbω` 的高度不经 `Ωit`, `Hier`, `ΩD`, `upT`, `Upω`, `Tω`, `emb`, `Ωᴴ` (定义级切片里 `HtFeedHt` 是 0 块, 见账). 没摆脱的: 折叠的形状; 读哪一层的目标 (第 1 层) 是我选的; 回灌只能沿 ℕ 迭代 (障碍 2).

## 账

**定义级切片** (口径同 `htfeed/locslice_htfeed.py`: 计 agda 非空非注释行, 记号模块除外; 脚本在临时目录 `htout/locslice_htout.py`).

| 路线 | 层 1 (类型) | 层 2 (+折叠, 闭项, FGH) | 层 3 (+合法性) | 加增长 |
|---|---|---|---|---|
| HtFeed, 高度给定; 闭项到 $\Omega^{\Omega^\omega}$ (读法) | 51 | 661 (去共用 578) | 665 (去共用 582) | 892 (净增 227) |
| **HtOut, 高度由回灌生成; 闭项 `T-fbω`** | 51 | 643 (去共用 560) | 649 (去共用 566) | 892 (净增 243) |

- 层 2 按模块: HtFeedTree 220, HtFeedFold 167, HtOutRead 82, Free.Level 56, CumReadCF 36, HtOutFeed 33, BTBO 27, HtFeedClosed 22. 与 `HtFeed` 比: 少了 `HtFeedHt` 121 行 (生成规则), 多了 `HtOutRead` 82 + `HtOutFeed` 33 行 (读法, `Cont`, 回灌). 高度的合法性仍在层 2 (`Fb` 带着 `Lg-rd`).
- 层 3 多 6 行 (`Lg-T-fbω` 是 `Lg-TΛ` 的一次调用).
- 增长净增 243 行 (HtFeedGrow 193, HtOutGrow 26, TLRuleSpec 24); 本路新写的只有 26 行.
- 独立切片: 读法加合法 (`rd`, `Lg-rd`) 174 行 (HtFeedTree 88, HtOutRead 62, CumReadCF 24); `cont→LgH` 64 行; 否定 153 行 (HtOutNeg 45, HtFeedNeg 45, HtFeedTree 27, CumReadCF 20, HtFeedHt 16).
- 文件级 (代码块里非空非注释行): `HtOutRead` 96, `HtOutFeed` 58, `HtOutGrow` 42, `HtOutNeg` 58, `HtOutTest` 19, 入口 6.

## 审计

- **导入闭包** (`importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRuleSpec --only OCF.Align.TLRuleSum --only OCF.Align.SumOne --only OCF.Align.HtGen --only OCF.Align.HtFeed --only OCF.Align.BrwMid --only OCF.Align.BrwHigh --only OCF.Align.LayerTr --only OCF.Align.HtOut`): `HtOut` (30 个模块, 本地 20), `HtOutRead` (12, 本地 5), `HtOutFeed` (18, 本地 9), `HtOutGrow` (23, 本地 13), `HtOutNeg` (23, 本地 13) 都是退出码 0, 禁用表 0, `--only` 之外 0. `HtOutTest` 退出码 1: 禁用表 0, `--only` 之外 29, 列出的都经比较器 `CumUpAcceptF` 进来 (同 `HtFeedTest`). `HtOutFeed` 的闭包含 `HtFeedHt` (经 `HtFeedClosed`), 定义级切片里 `T-fbω` 不到达它.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `HtOutFeed:fgh` 165/0/0, `HtOutFeed:T-fbω` 147/0/0, `HtOutFeed:Lg-T-fbω` 150/0/0, `HtOutFeed:Fb` 138/0/0, `HtOutRead:rd` 28/0/0, `HtOutRead:Lg-rd` 41/0/0, `HtOutRead:cont→LgH` 18/0/0, `HtOutGrow:Sup-fb` 222/0/0, `HtOutGrow:Λ-Ω` 144/0/0, `HtOutNeg:drop-lim` 37/0/0, `HtOutNeg:drop-suc` 13/0/0, `HtOutNeg:no-total` 14/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明没受记号启发 (见翻译账).
- **禁用构造**: 六个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 不用 `--cubical`; 都带 `--safe --without-K --lossy-unification`.
- **从头编译** (`--ignore-interfaces`): 入口退出码 0 (28 秒, 1.2G); `HtOutTest` 退出码 0 (102 秒, 3.2G).

## 时间线

写定义前读过: `HtFeed*` 全部, `BrwHigh`, `BrwHighOne`, `HtGen`, `LayerTr`, `LayerTrBase` 与 `LayerTrOne` 的签名, `CumReadCF` 的签名, `BrwMidZero` 的 `dif` 签名. 没有打开 `EBO`, `Correspond`, `Label`, 也没有读任何基本列规则. 第 1 层目标与 $\psi_1$ 的读法来自 `HtFeed` 与 README 已有的读法.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtOut where

open import OCF.Align.HtOutRead using (_⊞ᴴ_; ⊞ᴴ-fst; Lg-⊞ᴴ; Cont; cont-mono; cont→LgH; nb; nb-cont; it-cont; toD; rd; rd-fst; Lg-rd) public
open import OCF.Align.HtOutFeed using (top⁺; out₁; HL; Fb; fb-fst; fb-st; Λs; Λω; lΛω; Λψ; T-fb; T-fbω; T-ψΩΩ; Lg-T-fbω; fgh; Λ₁-Ω) public
open import OCF.Align.HtOutGrow using (Λ-st; Fb-Ω; Λ-Ω; Sup-fb; module ωSt) public
open import OCF.Align.HtOutNeg using (drop-lim; drop-suc; no-loop; no-total) public
```
