# 第三站: 高度 3 到 4 的严格增长 (结构版): 入口

> **判决: (A) HOLDS; (B) 未完成 (暂停, 不是否定).** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`, 没有验收文件, 不改定义, 不经规范形 (`Gen`/`DValCanon`), 不用左边极限截断 (`LimLaw`).
>
> 1. **`mono₃ : MonoStep 3`, `grow₃₄ : asuc (TΛ 3) ≤ TΛ 4`, `grow₀₄ : TΛ 0 + 4 ≤ TΛ 4`, 无前提 (HOLDS).** [MonoPort5Chain](MonoPort5Chain.lagda.md). 与 `MonoPort2Chain.grow₀₃` 合起来, $T_\Lambda$ 在 $\Lambda=0,1,2,3,4$ 上严格增长.
> 2. 证明的构件 (都编译过): 实例 3 的三层结构关系与观测 `O₃` ([MonoPort5Rel](MonoPort5Rel.lagda.md)); `Int` 对结构关系单调 ([MonoPort5Int](MonoPort5Int.lagda.md), **上一组缺件表里没有的一件**); 一切单世界层的上升链 `chainG` ([MonoPort5Chn](MonoPort5Chn.lagda.md)); 第 1 层的 `snd₁` ([MonoPort5One](MonoPort5One.lagda.md)); 第 2 层的 `snd₂` ([MonoPort5Two](MonoPort5Two.lagda.md)).
> 3. **(B) 一步 $c\to c+1$ 对一切有限高度: 没有做.** §3 写出它要的形状与已经一次写成的部分; 第一个障碍是对抽象层号的位置计算 (`rkT`, `kk`, `Vs`) 不再定义性地化简, 第二个是实例 $\ge4$ 时 `Int` 要走带节点的树. 没有反例, 没有否定定理.

## 1 定理表

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `RelM` | MonoPort5Rel | 第 $\ge1$ 层的结构关系, 节点构造子对一切节点种类, 坐标关系作参数 | 定义 |
| `O₃`, `pre₃` | MonoPort5Rel | $T_0,T_1,T_2$ 上 $\sqsubseteq_0\times\sqsubseteq_1\times\sqsubseteq_2$ 满足核的输出律与 `PreLaw` | 定理 |
| `IntS`, `IntM` | MonoPort5Int | 分支单调 ⇒ `Int` 把 $\sqsubseteq_0$ 送到 $\sqsubseteq_1$ (对上下文与对树) | 条件定理 (分支的三条单调前提) |
| `chainG` | MonoPort5Chn | 一切实例、观测、单世界层: 链点按 `Pt` 相关 ⇒ 各段输出逐项相关, 读数极限 $\le$ | 条件定理 (`sndP`, `prj`, `cxn`, `cxc`, 三条 `HA`) |
| `cl₁` | MonoPort5One | 上下文取 "$\sqsubseteq_1$ 且沿左脊自比" 时核的九条上下文律 | 定理 |
| `brn₀` | MonoPort5One | 第 0 层节点保留时的分支, 对一切第 0 层动作 | 条件定理 (三条 `HA`) |
| `hAi₁`, `niS₁` | MonoPort5One | 第 1 层节点的动作满足 `HA`; 节点一步 ($T_0$ 升, $T_1,T_2$ 留) | 条件定理 (分支的语义前提) |
| **`snd₁`** | MonoPort5One | $x\sqsubseteq_1x'$ ⇒ 两动作的第 1 层语义 (实例 3, 三个目标) | 条件定理 (三条 `HA`) |
| `brn₁`, `niS₂₁`, `niS₂₀` | MonoPort5Two | 第 1 层节点保留的分支; 第 2 层的两种节点一步 | 条件定理 |
| **`snd₂`** | MonoPort5Two | $x\sqsubseteq_2x'$ ⇒ 两动作的第 2 层语义 | 条件定理 (三条 `HA`) |
| `HA-Step`, `sLR`, `hb` | MonoPort5Chain | `StepA` 的 `HA`; 两个起点 | 定理 |
| **`mono₃`**, **`grow₃₄`**, `grow₀₄` | MonoPort5Chain | `MonoStep 3`; $T_3<T_4$; $T_0+4\le T_4$ | **定理 (无前提)** |
| (B) 一切有限高度 | — | 见 §3 | 判断, 未做 |

## 2 证明的形状

- 外层链 (点在第 2 层, 动作 `StepA`) 每一步是 `snd₂`. `snd₂` 对 $\sqsubseteq_2$ 的推导归纳; 和的构造子全由核 [MonoPort3Gen](MonoPort3Gen.lagda.md), `nw` 三条各一行 (`Run (nw self x) self` 定义性地是 `Run x self`).
- 节点一步按节点层 $k$ 对目标层 $e$: $e\le k$ 上升, 输出是层 $k$ 的链段极限 (`chain₀ᴳ`, `chainG`); $e>k$ 保留, 输出是同一种节点, 分支是 "层 $k$ 走坐标、再走分支" (`brn₀`, `brn₁`). 三处 (`niS₁`, `niS₂₁`, `niS₂₀`) 是同一句话.
- 动作 `Ai` 的 `HA` 就是分支的语义, 外加上下文 `nw w ⨾ Int z` 相关: 第 2 层的上下文不被读 ($\top$), 第 1 层的上下文被第 2 层节点当坐标读, 所以要 `IntM`.
- 第 1 层的上下文关系不能只是 "$\sqsubseteq_1$ 且两边自比": 部分和那条上下文律要从 `w ⨾ nw (preL d n)` 的自比拆出 `w` 与 `preL d n` 的自比, 而 $\sqsubseteq_1$ 带自比前提的 `⨾⊑` 不能反演. 改为沿 ⨾ 左脊对树的形状计算的 `Ok` (不对推导反演), 加一条 `nwᵉ` (语义一行). 第 2 层节点的坐标关系随之取同一个 (`Low₂`).

## 3 (B): 一步 $c\to c+1$ 要的形状 (判断)

**已经一次写成的** (对层号不按站写): 第 $\ge1$ 层的关系 `RelM ly Low` (节点构造子对一切节点种类); 和的结构 (核); 上升的链 `chainG` (一切单世界层); 第 0 层 `snd₀ᴳ`, `chain₀ᴳ` (一切实例与观测). 按站写的: 观测 `O₃` (三个分量), 上下文律 `cl₁` (只用 `RelM` 的构造子, 实际与层无关), `brn₀`/`brn₁` (同一个论证, 下层的 `Core` 不同), 节点一步的分派 (`niS₁`, `niS₂₁`, `niS₂₀`), `IntM` (只做了第 0 层进第 1 层).

**要的陈述.** 高度 $N_n=$ `hs`$^n$ `hz`. 对 $n$ 归纳: 实例 $N_{n+1}$, 观测 $O_n=\forall e\le n.\ T_e$ 上 $\sqsubseteq_e$; 层关系 $\sqsubseteq_{j+1}=$ `RelM` $N_{j+1}$ `Low`$_{j+1}$, `Low`$_{j+1}$ (ss $P$) 对 $P$ 递归取 "层 $i$ 的上下文关系" ($i=0$: $\sqsubseteq_0$; $i\ge1$: $\sqsubseteq_i$ 加 `Ok`). 一步: "层 $<j$ 的 `snd` (两动作, 观测 $O_n$) 与层 $j$ 分支的语义 ⇒ 层 $j$ 的节点一步", 节点一步对 "$e\le i$ 上升 / $e>i$ 保留" 统一陈述.

**第一个障碍: 位置计算对抽象层号不化简.** 上面三处节点一步能写, 是因为实例 3 里目标、节点的位置都是闭的 `hsuc` 链: `RunNi` 的 `rkT` 经 `cmpH` 算出 `rise` 或 `keep (ss …)`, `kk r self ll` 算回下层的位置, `accL` 的分量算回 `accL`, `inS`/`outS` 化成恒等, 全是定义性的. 层号是变量时这些都卡住: 要 (i) `rkT` 的取值引理 (目标层 $\le$ 节点层 ⇒ `rise`, 否则 `keep (ss P')`, 对差归纳), (ii) `kk r self (pos j) ≡ pos i` 一类位置等式, 再把链与分支的陈述沿它们 `subst` (`Run` 依赖 `ll`), (iii) `Low` 对 `inC`/`outC` 的搬运 (对 $P$ 归纳, 这一件是定义性的). 这是工程, 不是数学障碍; 但它与核的接口有关: 核 `Core` 以 `ll` 为模块参数, 节点给出的 `kk …` 与层自己的 `pos` 不定义性相等时, 两个 `Core` 实例的 `Sem` 不是同一个类型.

**第二个障碍: 实例 $\ge4$ 时 `Int` 走带节点的树.** 实例 3 里只有第 0 层树进第 1 层的 `Int` 被读 (`IntM`): 第 1 层树进第 2 层的 `Int` 作第 2 层的上下文, 不被读. 实例 4 里第 2 层的上下文被第 3 层节点读, 于是第 1 层树 (含第 0 层节点) 进第 2 层的 `Int` 要单调; `Int` 的 `ni` 句造一个嵌套的节点 (分支里再 `Int` 一次坐标), 要对 $(k',k)$ 双重归纳的 `IntM`. 形状与 `IntM` 相同, 没有写.

## 4 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `RelM` 的节点构造子对一切节点种类, 坐标关系作参数 | 节点的分支类型 `Vs ly r` | 树逼的 (字段形状由树的类型给出) |
| `nwˡ`, `nwʳ`, `nwᵉ` (只在 `self`) | 第 1 层的上下文里有 `w ⨾ nw self x`, 又作坐标 | 树逼的 (`Run` 的 `⨾` 句; 语义定义性) |
| 第 1 层上下文关系 = $\sqsubseteq_1$ 加 `Ok` | 被第 2 层节点读作坐标; 部分和的上下文律要拆自比 | 树逼的 (`Ai` 与 `Rpt` 的字面) |
| `IntM` | `Ai` 的上下文 `nw w ⨾ Int z` | 树逼的 (`Int` 的字面) |
| 观测 `O₃` 三个分量 | 状态的 $T_0,T_1,T_2$ 分量都被读 (`Step`, 链的起点) | 树逼的 |
| 节点一步按 $e\le k$ / $e>k$ 分派 | `RKi` 的 `rise`/`keep` 两句 | 树逼的 |

**按 `AGENTS.md` 归类: 提供信息.** 没有新构造子或节点字段, 没有改折叠, 没有 `Lab`, 没有记号, 闭包定理没有按站新增专属前提 (三处节点一步是同一句话的实例). 严格增长是值的定理 (`TΛ 3 < TΛ 4`), 不是强度的序数值验收.

## 5 账

| 文件 | 行 (代码, 去空行与注释) | 内容 |
|---|---|---|
| `MonoPort5Rel` | 126 | 实例 3, `RelM`, $\sqsubseteq_1$, $\sqsubseteq_2$, `O₃`, `pre₃` |
| `MonoPort5Int` | 74 | `IntS`, `IntM` |
| `MonoPort5Chn` | 57 | `chainG` |
| `MonoPort5One` | 146 | `cl₁`, `brn₀`, `hAi₁`, `niS₁`, `snd₁` |
| `MonoPort5Two` | 134 | `brn₁`, `niS₂₁`, `niS₂₀`, `snd₂` |
| `MonoPort5Chain` | 62 | `HA-Step`, 起点, `mono₃`, `grow₃₄`, `grow₀₄` |
| 入口 | 8 | |
| 合计 | 607 | (上一组估计约 600) |

审计 (2026-11-05):

- 编译: 删掉本组 7 个 `.agdai` 后从入口重编, 退出码 0, 约 9 秒, 峰值常驻约 0.96G (`-M6G`). 七个文件各自退出码 0. 无禁用构造 (`postulate`, 洞, `TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext`, K 都是 0).
- 导入闭包 (`importclosure.py`, `--only` 取 `OCF.Free.Level`, `OCF.BTBO`, `OCF.Align.` 下的 `CumReadCF`, `TLRule`, `TLOpsW`, `SumOne`, `BrwMid`, `LayerTr`, `CvFold`, `CvHigh`, `CvLayer`, `NoCumLit`, `L1Val`, `DVal`, `HtGen`, `HtFeed`, `HtCross`, `KVal`, `MonoPort`, `StrRel`): 入口闭包 54 个模块 (本地 44, 库 10), 禁用表 0, `--only` 之外 0. 闭包里有 `DValCanon`: 由已有的 `MonoPort3Gen → MonoPortBridge` (只导入不使用 `smono`) 与 `MonoPortStep → MonoPortOne` 带进来; 本组的证明不用规范形.
- 定义级切片 (`depslice.py`): `mono₃` 到达 205 块, `grow₃₄` 286, `grow₀₄` 531, `snd₂` 259, 记号模块 0, 记号词 0; 正对照 `Om1HnAccept:label-term₀` 到达 1188 块, 记号模块 92, 记号词 58. 切片看不见模块应用 (`module CH2 = C2.Chain …`), 所以块数偏少; 记号无关由导入闭包保证.
- `grow₀₄` 经 `MonoPortOne.grow₀₁₂` (高度 0 到 2, 那一站用规范形) 与 `StrRelChain.grow₂₃ˢ` (结构版); 高度 3 到 4 这一站 (`mono₃`, `grow₃₄`) 不经规范形.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort5 where

open import OCF.Align.MonoPort5Chain using (mono₃; grow₃₄; grow₀₄; HA-Step) public
open import OCF.Align.MonoPort5Two using (snd₂; niS₂₁; niS₂₀; brn₁) public
open import OCF.Align.MonoPort5One using (snd₁; niS₁; brn₀; cl₁) public
open import OCF.Align.MonoPort5Int using (IntS; IntM) public
open import OCF.Align.MonoPort5Rel using (O₃; pre₃; module RelM) public
import OCF.Align.MonoPort5Chn
```
