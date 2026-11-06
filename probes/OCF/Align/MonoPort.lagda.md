# 共同的单调目标, 最低一站: 入口

> **判决: PARTIAL (最低一站 HOLDS).** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, **不用 `Funext`**, 没有验收文件.
>
> 1. **规范形与链搬到高度树主线 (HOLDS, 第 0 层, 对一切实例).** [MonoPortZero](MonoPortZero.lagda.md): 对一切高度 $\Lambda$, 一切一步 $S$, 一切世界与第 0 层路径, 折叠 `HtFeedFold S Λ` 在第 0 层目标上对第 0 层输入的**值**单调 (`cong0`, 两边动作可以不同, 前提是动作的三条 `HAᶜ`), 节点上升时的链对起点单调 (`chain`). 规范形论证没有重抄: `DValCanon.Gen` 原样套用, 关系经翻译 `ofS` 拉回到 `SumOneTree.D azero` ([MonoPortBridge](MonoPortBridge.lagda.md), 两种第 0 层差树构造子相同).
> 2. **`MonoTarget₁` 无条件成立 (HOLDS).** [MonoPortOne](MonoPortOne.lagda.md) `mono₁ : MonoTarget₁` (即 `Hs.MonoStep (hs hz) tt`, [KValMonoTest](KValMonoTest.lagda.md) 的陈述). 链的动作定义性地归约到只看状态的 `StepA`, `HA-Step` 一条引理给出三条前提与两个起点.
> 3. **推论: $T_1<T_2$, 不用外延性 (HOLDS).** `grow₁₂ : asuc (TΛ 1) ≤ TΛ 2`, `grow₀₁₂ : asuc (asuc (TΛ 0)) ≤ TΛ 2`. 用的是 `HtCrossVInst.HsS.hs-reduce<′` (无 `Funext`, 前提 `Free (hs hz)` 计算成 `⊤`) 与 `hz<1′`.
> 4. **一切后继高度: 归结做了, 证明没做.** [MonoPortStep](MonoPortStep.lagda.md) `step≡`: 对一切 $\Lambda$, `MonoStep (hs Λ)` 字面就是两条链的比较 `ChainLe Λ` (`refl`), 链的点在层 $\Lambda$. $\Lambda=0$ 由 `chain` 给出 (`mono₁′`); $\Lambda\ge1$ **未走通** (未完成, 不是否定), 第一个障碍见 §3. 没有找到反例, 没有否定定理.

## 1 结构

| 件 | 内容 | 文件 |
|---|---|---|
| `toS`, `ofS`, `preH`, `ofS-pre` | 两种第 0 层差树互译, 与构造子定义性交换; 部分和的交换是命题相等 (对 $k$ 归纳, 不用外延性) | MonoPortBridge |
| `sumT≤`, `sumT≥`, `toV`, `smono` | `sum` 在翻译下不变; 高度树一侧 `sum` 对底与树的值单调 | MonoPortBridge |
| `OutLe`, `Rl`, `HAᶜ` | 与 `DValZero` 同形: 上下文值、底、状态在 $T_0$ 上的值都 $\le$ ⇒ 读数 $\le$; `Rl` 另加树自己的值 (`val = sum azero`) | MonoPortZero |
| `⨾-mono` … `tr⊑ʳ` | 十四条结构律, 逐条照 `DValZero` §2 | MonoPortZero |
| `Rˢ`, `GG = Gen …`, `rt`, `rt′` | 拉回 `SumOne`, 套 `Gen`; 往返 `ofS (toS z)` 与 $z$ 两向相关 | MonoPortZero |
| **`cong0`**, **`chain`** | 值同余; 链的极限对起点单调 | MonoPortZero |
| `StepA`, `HA-Step`, `hb`, `hY`, **`mono₁`** | 最低一站 | MonoPortOne |
| **`grow₁₂`**, `grow₀₁₂` | 严格增长 | MonoPortOne |
| `Ch.ChainLe`, **`step≡`**, `mono₁′` | 一切 `hs Λ` 上 `MonoStep` 的链形式 | MonoPortStep |

与 `DValZero` 的差别只有三处: 折叠换成 `HtFeedFold` (目标是高度目标 `tg self hk lW`, `⊕⟨ lW ⟩`); 树的值用 `sum azero` 而不经 `toA`, 所以单位律与结合律的值那一半是 `≤-refl` (定义性相等); 规范形经翻译套 `Gen`, 不重写. 估计 500 行, 实际 342 行 agda 代码 (含 `MonoPortStep`), 其中照 `DValZero` 搬的约 150 行.

## 2 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `ofS-pre`, `sumT≤`, `sumT≥`, `toV`, `smono` | MonoPortBridge | 翻译与和 | 定理 |
| 结构律十四条, `rt`, `rt′` | MonoPortZero | 关系的同余、单位、结合、极限、传递、往返 | 条件定理 (动作的 `HAᶜ`) |
| **`cong0`** | MonoPortZero | 第 0 层值 $\le$ ⇒ 折叠读数 $\le$, 一切实例 $\Lambda$ | 条件定理 (三条 `HAᶜ`) |
| **`chain`** | MonoPortZero | 底 $\le$, 状态值 $\le$ ⇒ 链的极限 $\le$, 一切实例 $\Lambda$ | 条件定理 (三条 `HAᶜ`) |
| `HA-Step` | MonoPortOne | 只看状态的一步满足 `HAᶜ` | 定理 |
| **`mono₁`** | MonoPortOne | `MonoTarget₁` | **定理, 无前提** |
| **`grow₁₂`**, `grow₀₁₂` | MonoPortOne | $T_1+1\le T_2$, $T_0+2\le T_2$ | **定理, 无前提, 无 `Funext`** |
| **`step≡`** | MonoPortStep | `MonoStep (hs Λ) ≡ ChainLe Λ`, 一切 $\Lambda$ | 定理 (`refl`) |
| `mono₁′` | MonoPortStep | 经 `step≡` 的同一结论 | 定理 |
| `MonoStep (hs Λ)`, $\Lambda\ge1$ | — | 纸面: 两条链右边每项不低 | **未证明 (判断)** |

`KValMonoTest` 的有限测试 (`G 1` 左 4 右 32) 现在被 `mono₁` 覆盖; 它们仍只是测试.

## 3 第一个障碍: $\Lambda=1$ 上的 `MonoStep (hs (hs hz))`

`step≡` 把它化成 `ChainLe (hs hz)`: 链的点 $\delta_n$ 是**第 1 层**的差树, $\delta_0$ 是状态在第 1 层目标上的差 (左 $0⨾\omega\cdot(\Omega_1⨾0)$, 右多两段), 下一个点 $\delta_{n+1}$ 是 $\delta_n$ 的折叠在第 1 层目标上的读数. 第 0 层的点没有节点, 所以 `cong0` 只要比值; 第 1 层的点有 `ni`, 节点层 $0$ 对第 1 层目标**保留** (`keep`), 输出节点的分支是 `BNi` 的再折叠, 读坐标. 所以要的是 (判断):

- (a) 第 1 层差树上的关系, 让第 0 层读数单调: `DValSound.snd` 的同形物, 那边已在 `SumOneClosed` 上证过 (含 `ni⊑`), 搬到 `HtFeedFold` 是与本组同样的机械工作.
- (b) **这个关系对折叠在第 1 层目标上的输出封闭**: $\delta_n\sqsubseteq\delta'_n$ ⇒ $\delta_{n+1}\sqsubseteq\delta'_{n+1}$, 也就是 `ni⊑` 的三条分支前提 (`Mono` 两条与跨分支一条) 对 `BNi` 产出的分支成立. `DValKn.Kn-Rf` 只做了折叠产出的第一个节点的自比. 这就是 `CvLayer` §2 停下的地方, 本组没有做.

所以 $\Lambda\ge1$ 不是本组的方法再走一层, 而是第 4 层的问题本身. 没有否定定理, 也没有找到反例: 只写 "未走通".

## 4 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 翻译 `toS`, `ofS` | 两种第 0 层差树构造子相同, 规范形论证只写过一次 (`Gen`) | 树侧, 去重复 |
| 关系 `Rl` 的形状 (上下文值、底、状态值) | `Run` 的三个累积量: 上下文接 `nw q x`, 状态接 `⊕`, 读数从底起加 | **树逼的** (折叠的形状), 照 `DValZero` |
| 动作作参数, 前提 `HAᶜ` 三条 | 链的两边动作来自两组分支 | 树逼的, 照 `DValZero` |
| `StepA`: 链的动作只看状态 | `Ai` 在分支 `n1` 上定义性归约到 `Step` | 树侧, 计算 |
| `ChainLe Λ` | `Ωd (hs Λ)` 的计算展开 | 树侧; 对结构参数 $\Lambda$ 的一步陈述, 新用到 `hs` 的节点 `ss hself` |

**按 `AGENTS.md` 归类: 提供信息.** 没有新构造子, 没有新节点字段, 没有改折叠, 没有 `Lab`, 没有记号, 没有为这一站定制的前提: `cong0`, `chain` 对一切实例 $\Lambda$ 与一切一步 $S$ 成立, `step≡` 对一切 $\Lambda$; 只有 `mono₁` 是 $\Lambda=1$ 的实例 (它是共同目标的这一站本身). 脚手架 (判断): 翻译 65 行是 "规范形论证写在 `SumOne` 上" 带来的, 若把 `Gen` 对树类型抽象就可去掉; 结构律 150 行是折叠形状逼出的, 与高度无关. 没有序数值验收 (无参照树); `grow₁₂` 只说明不塌缩.

## 5 账

文件级 (agda 代码块里非空非注释的行):

| 文件 | 行 | 内容 |
|---|---|---|
| `MonoPortBridge` | 65 | 翻译, 和不变, `smono` |
| `MonoPortZero` | 194 | 关系, 结构律, 套 `Gen`, `cong0`, `chain` |
| `MonoPortOne` | 47 | `mono₁`, `grow₁₂` |
| `MonoPortStep` | 36 | `step≡` |
| 入口 | 6 | |
| 合计 | 348 | |

## 6 审计

- **导入闭包** (`importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRule --only OCF.Align.TLOpsW --only OCF.Align.SumOne --only OCF.Align.BrwMid --only OCF.Align.LayerTr --only OCF.Align.CvFold --only OCF.Align.CvHigh --only OCF.Align.CvLayer --only OCF.Align.NoCumLit --only OCF.Align.L1Val --only OCF.Align.DVal --only OCF.Align.HtGen --only OCF.Align.HtFeed --only OCF.Align.HtCross --only OCF.Align.KVal --only OCF.Align.MonoPort`): 入口 41 个模块 (本地 31), `MonoPortBridge` 26 (16), `MonoPortZero` 28 (18), `MonoPortOne` 39 (29), `MonoPortStep` 40 (30); 都是退出码 0, 禁用表 0, `--only` 之外 0. 闭包里有 `HtCrossInst`, `HtCrossRun` (经 `KValMonoTest` 读 `MonoStep` 的定义), 那里的 `Funext` 只是定理参数, 本组没有用到以它为前提的定理.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `MonoPortOne:mono₁` 247/0/0, `MonoPortOne:grow₁₂` 328/0/0, `MonoPortOne:grow₀₁₂` 332/0/0, `MonoPortStep:step≡` 127/0/0, `MonoPortZero:chain` 217/0/0, `MonoPortZero:cong0` 213/0/0, `MonoPortBridge:smono` 66/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明没受记号启发.
- **禁用构造**: 五个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 不用 `--cubical`, 不出现 `Funext`; 都带 `--safe --without-K --lossy-unification`.
- **从头编译** (`--ignore-interfaces`): 入口退出码 0 (44 秒, 峰值 1.1G).

## 7 时间线

写定义前读过: `AGENTS.md`, `probes/README.md` 两节, `KValMonoTest`, `CumReadCF`, `TLRuleSpec`, `HtFeedTree`, `HtFeedFold`, `HtFeedClosed`, `HtCrossInst`, `HtCross`, `DValTree`, `DValCanon`, `DValZero`, `DValSound`, `SumOneTree` 前半, `BrwMidZero` 的签名, `HtCrossVInst` 的签名, `KValZero` 与 `KVal` 的开头. 没有打开 `EBO`, `Correspond`, `Label`, 没有读任何基本列规则.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort where

open import OCF.Align.MonoPortBridge using (toS; ofS; ofS-pre; smono; toV) public
import OCF.Align.MonoPortZero
open import OCF.Align.MonoPortOne using (StepA; HA-Step; mono₁; grow₁₂; grow₀₁₂) public
open import OCF.Align.MonoPortStep using (module Ch; mono₁′) public
```
