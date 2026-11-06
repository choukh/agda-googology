# 一步对一切有限高度: 入口

> **判决: HOLDS (编译过的定理, 无前提).** 对一切 $n$, $T_\Lambda$ 在高度 $n$ 到 $n+1$ 严格增长: `grow : ∀ n → asuc (TΛ (N n)) ≤ TΛ (N (suc n))`, `grow₀ : ∀ n → TΛ 0 + n ≤ TΛ n`. 证明是**一句话加一次归纳**: "坐标层 $k$ 的 `snd` (两个动作, 一切目标) ⇒ 节点层的节点一步" (`MonoPort6Snd.Node.step`), 对 (良基证明, 推导) 字典序归纳一次 (`sndS`, `sndArg`); 不按站写, 不对层号算位置. 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`, 没有验收文件, 不改定义, 不改已有文件.
>
> 极限高度 `hl` (`MonoL`) 未做, 见 §3.

## 1 定理表

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `Rel`, `LowT`, `CtxP`, `Ctx` | MonoPort6Rel | 一切层上的结构关系: 第 0 层 $\sqsubseteq_0$, 后继层 `RelM`, 节点的坐标关系对位置递归 | 定义 |
| `lowOut`, `lowIn` | MonoPort6Rel | 坐标关系沿位置搬运 (对位置归纳, 每步定义性) | 定理 |
| `O`, `preO` | MonoPort6Rel | 观测 = 一切目标、一切位置上 `Rel`; 核的输出律与 `PreLaw` | 定理 |
| `HAK`, `obs` | MonoPort6Rel | 与核实例无关的动作前提; 观测由 `≼` 给出 | 定义, 定理 |
| `B.snd₀`, `B.Chain.chain₀` | MonoPort6Zero | 第 0 层对一切良基证明 `ac` 与位置 `ll`; 链的各段在一切目标上相关 | 条件定理 (三条 `HA`) |
| `CxS.*` | MonoPort6Int | 第 $\ge1$ 层上下文律, 对 $b$ 写一次 | 定理 |
| `Z.IntM₀` | MonoPort6Int | 第 0 层进任意层的 `Int` 单调 | 条件定理 (分支三条单调) |
| **`IntMK`, `IntMS`** | MonoPort6Int | 一切层对 $(k, \text{ly})$ 的 `Int` 单调, 源层带节点; (良基证明, 推导) 字典序归纳 | 条件定理 (分支三条单调) |
| `L.cl`, `L.Ch`, `L.brn` | MonoPort6Lay | 层 `hs b` 的核实例 (一切 `ac`, `ll`): 上下文律, 链, 分支一步 | 定理 / 条件定理 |
| `chainK`, `brnK` | MonoPort6Snd | 对一切层: 链与分支一步 (第 0 层与 `hs b` 两种) | 条件定理 (坐标层的 `snd`, 三条 `HAK`) |
| **`Node.step`** | MonoPort6Snd | 节点一步: 对 `Rk` 的值分 `rise`/`keep`, 一切节点层、坐标层、目标层 | 条件定理 (坐标层 `snd`, 分支的关系与语义, 三条 `HAK`) |
| **`sndS`, `sndArg`** | MonoPort6Snd | 一切有限层: $x \mathrel{\mathrm{Rel}} x'$ ⇒ 两动作的语义 | 定理 (`Fin`) |
| `HA-Step`, `sLR`, `hb` | MonoPort6Chain | 外层动作与两个起点, 对 $\Lambda_0$ 写一次 | 定理 |
| **`Top.chainLe`, `Top.monoS`** | MonoPort6Chain | 一切有限 $\Lambda_0$: `ChainLe Λ₀`, 即 `MonoStep (hs Λ₀)` | **定理 (`FinH Λ₀`)** |
| **`grow`**, **`grow₀`** | MonoPort6Chain | 一切 $n$: $T_n < T_{n+1}$; $T_0 + n \le T_n$ | **定理 (无前提)** |
| `mono₃′`, `grow₄₅`, `grow₁₀` | MonoPort6Chain | 特例 (`MonoPort5Chain.mono₃` 同型; 4 到 5 是新的一站) | 定理 |
| 极限高度 `hl` | — | 见 §3 | 判断, 未做 |

## 2 三个障碍怎么没了

上一组 ([MonoPort5](MonoPort5.lagda.md) §3) 列出的障碍都是 "对抽象层号的计算不定义性化简". 这里的做法是**不算**:

- **(i) `rkT` 的取值引理.** 节点输出在目标 `tm` 上的读数字面是 `RKi … (rkT …)`. `Node.rkRel` 对 `Rk` 的**值**分情形 (`rise` / `keep (ss p)` / 另两种 $\top$), 不问 `rkT` 算出哪一个; `step tm = rkRel tm (rkT …)` 一行. `rise` 时输出是层 $k$ 的链段极限, 链对一切目标给出 `≼` (所以 `MonoPort6Zero` 的链结论加了这一项); `keep (ss p)` 时输出是同一种节点, 分支是层 $k$ 的分支一步, 坐标关系经 `lowOut` 到层 $k$ 的上下文关系.
- **(ii) 位置等式与 `subst`.** 一切陈述 (`SemS`, `SndArg`, 链, 分支一步, `Int` 单调) 对位置全称. 递归调用直接取折叠给出的位置: 链在 `kk r C.self ll`, 分支在 `⊲ᴴ↑ C.self ll`, 分支一步的坐标在 `⊲ᴴ↑ C.self (kk …)`, 观测在 `⊲ᴴ↑ C.self tm`. 观测本身对一切位置取, 所以没有一处要两个位置相等. 核实例之间的记录类型不同, 用与实例无关的 `HAK` 与一行换算 (`toHA`, `fromHA`, `toHA₀`).
- **(iii) `Low` 沿 `inC`/`outC` 的搬运.** 坐标关系 `CtxP b P` 对位置 $P$ 递归 (到 `hself` 取坐标层的 `Ctx`), 搬运引理 `lowOut`, `lowIn` 对 $P$ 归纳, 每一步 `refl` 级.
- **第二个障碍 (`Int` 走带节点的树).** `IntMS` 的 `ni` 句: 输出是新节点 `mk … R`, 分支里外层 `Int` 走节点分支 (同一个良基证明, 更小的推导), 内层 `Int` 把坐标 (层 $j$) 嵌进层 $k$ (更小的良基证明 `g (ss P)`). 两边要同一个 `mk` (折叠里 `Ai` 两边都是 `mkOf r …`). 终止由字典序给出; 递归调用必须写在子句体里 (经 `where` 提升会丢掉 `g x ≤ g` 的信息, 编译器拒绝).
- **良基证明.** 第 0 层的核原来固定在 `accL hz`; 折叠在节点处给出的是 `f r`. 一切层的语义对良基证明全称 (`MonoPort6Zero` 的 `B` 模块参数 `ac`), 归纳就是对它.

## 3 未做: 极限高度 `hl` (判断)

`HtCrossVInst.HlS.hl-reduce<′` 要 `MonoL n`: `TΛ-in (hl f) l (f n) hk ≤ sum β X`. 左边是 `Ωd (f n) {azero}` 经 `z⊲ one` 嵌进世界 1 后用动作 `Act` 折叠 (良基证明 `accᴸ`, 上下文 `n0`, 状态 `Y₀`); 右边是 `Ωd (f n) {one}` 在 `C.self` 处用动作 `A²` 折叠 (良基证明 `accK r`, 上下文 `n0 ⨾ nw C.self n0`, 状态 `Rp n ⊕ 0`). **第一个障碍**: 本组第 $\ge1$ 层的关系 (`RelM`) 只在一个世界上 (`nw` 只取 `C.self`, 语义的路径是 $\top$), 而这里两边的嵌入位置不同 (`z⊲ one` 对 `C.self`), 节点的嵌入 `mkOf r (⊲-tr q₀ p)` 两边也不同, `IntMS` 要两边同一个 `mk`. 可能的出路 (未试): 这里的分支是常数 `n1`, `Ai` 读到的上下文最后被 `Act` 丢掉, 所以可以对 `Ωd` 这一棵树直接写动作前提, 不经 `IntMK`. 实例 `hl f` 本身不是有限的, 但本组的关系对一切 $\Lambda$ 定义, 有限的只要是 `f n` 以下各层. 没有否定定理, 只是没做.

## 4 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `Rel` 对层递归, 节点坐标关系 `CtxP` 对位置递归 | 节点分支的类型 `Vs L r = Vc b P`, 对位置递归 | 树逼的 (类型的递归形状) |
| 观测取一切目标、一切位置 | 状态的每一层分量都被读 (`Step`, 链起点, `keep` 输出在 `⊲ᴴ↑ C.self tm` 上读) | 树逼的 |
| 对 `Rk` 的值分情形, 不算 `rkT` | `RunNi` 的字面 | 树逼的 |
| 语义对良基证明、位置全称 | 折叠在节点处给出 `f r`, `kk r …`, `⊲ᴴ↑ …` | 树逼的 |
| `HAK` (实例无关) | 核的记录类型依赖实例 | 脚手架 (工程, 不是序数值需要的) |
| `IntMS` 的字典序归纳, 同一个 `mk` | `Int` 的 `ni` 句 (内层 `Int` 用 `g R`) 与 `Ai` 的 `mkOf r …` | 树逼的 |
| 第 0 层的链结论加 "一切目标上相关" | `rise` 时目标层未知 | 树逼的 |

**按 `AGENTS.md` 归类: 提供信息.** 没有新构造子或节点字段, 没有改折叠, 没有 `Lab`, 没有记号. 闭包定理不按站定制: 一个 `Node.step` 对一切 (节点层, 坐标层, 目标层), 一次归纳. 这一步新用到的字段: 节点 `ss P` 的位置 $P$ (`CtxP` 对它递归) 与良基证明的构造子 `acc f` (`sndS`, `IntMS` 对它归纳); 对 `hs` 以外的层没有用到字段. 严格增长是值的定理 (`TΛ n < TΛ (n+1)`), 不是强度的序数值验收.

## 5 账

| 文件 | 行 (代码, 去空行与注释) | 内容 |
|---|---|---|
| `MonoPort6Rel` | 227 | `Fin`, `Rel`/`LowT`/`CtxP`/`Ctx`, 搬运, 输出律 (对目标层分情形), `O`, `preO`, `HAK`, `obs` |
| `MonoPort6Zero` | 103 | 第 0 层核对一切 `ac`, `ll` (`MonoPort4Zero.R0` 推广), 链加一切目标 |
| `MonoPort6Int` | 218 | 上下文律 `CxS`, `IntM₀`, `IntMK`/`IntMS` |
| `MonoPort6Lay` | 83 | 层 `hs b` 的核实例, `cl`, `toHA`/`fromHA`, `Ch`, `brn` |
| `MonoPort6Snd` | 163 | `SemK`, `chainK`, `brnK`, `Node.step`, `sndS`/`sndArg` |
| `MonoPort6Chain` | 107 | `HA-Step`, 起点, `chainLe`, `monoS`, `grow`, `grow₀`, 特例 |
| 入口 | 6 | |
| 合计 | 907 | |

审计 (2026-11-05):

- 编译: 删掉本组 6 个 `.agdai` 后从入口重编, 退出码 0, 约 12 秒, 峰值常驻约 1.3G (`-M6G`). 无禁用构造 (`postulate`, 洞, `TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext`, K 都是 0; `Funext` 只在讲解文字里出现). 终止全由编译器的结构检查给出 (`Rel`/`CtxP` 对层与位置, `IntMS`/`sndS` 对良基证明与推导).
- 导入闭包 (`importclosure.py`, `--only` 同 `MonoPort5`): 入口闭包 52 个模块 (本地 42, 库 10), 禁用表 0, `--only` 之外 0. 闭包里有 `DValCanon`: 由已有的 `MonoPort3Gen → MonoPortBridge` (只导入不使用 `smono`) 与 `MonoPortStep → MonoPortOne` 带进来; 本组不用规范形, 不用 `LimLaw`/`limS` (左边极限截断), 文件里没有这些名字.
- 定义级切片 (`depslice.py`): `grow` 到达 463 块, `grow₀` 465, `sndS` 327, `IntMS` 133, 记号模块 0, 记号词 0; 正对照 `Om1HnAccept:label-term₀` 到达 1188 块, 记号模块 92, 记号词 58. 切片看不见模块应用, 块数偏少; 记号无关由导入闭包保证.
- `grow 0` 是 `HtCrossVInst.hz<1′` (不经规范形); `grow (suc n)` 经 `Top.monoS`, 高度 1 到 2 这一站也走本组的第 0 层链, 不再经 `MonoPortOne` 的规范形.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort6 where

open import OCF.Align.MonoPort6Chain using (grow; grow₀; N; module Top; mono₃′; grow₄₅) public
import OCF.Align.MonoPort6Snd
import OCF.Align.MonoPort6Int
import OCF.Align.MonoPort6Lay
```
