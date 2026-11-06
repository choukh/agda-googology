# 结构关系, 第十四轮: 带不变量的语义, 跨坐标层节点规则归约, 律的定义域: 入口

> **判决: PARTIAL (构造一路).** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 不改树、折叠、合法性, 不改已有文件 (只新建 `StrRel14*`; 接口 `StrRel14If` 定稿后有一次增补, 见其变更记录).
>
> **对纲领与目标意味着什么 (判断).** 本轮全在第 4 层 (关系与语义), 不碰树. 得到的是一个结构事实和两条关于律的定义域的结论, 不是强度. (1) `StrRel12` 的八条规则只经三条律使用状态 (推出 `R∀c`, 经 `cv` 封闭, 经 `⊕` 封闭), 所以满足这三条律的任何状态不变量都能直接带进语义 (`semJ`). (2) 按 "律带公共上界" 检查: `StrRel12` 的 `κᴸ` 的分支对只有值上的 $c\le c'$. 它的定义域里有这样的节点对: 坐标层值相等而字面倒序, 种类对是 "左升右留" (`cpBad`). 所以跨坐标层的节点规则必须带字面证据. (3) StrRel13 判断 "第 0 格的走法路径可以对齐", 这被一条编译过的否定推翻 (`¬alCell0`), 顶层比较要错一格. 本轮没有给出 $T_\Omega<T_{\Omega+1}$, 也没有给出它的界.
>
> 交付 (按 `AGENTS.md` "交付拆成闭项与值"). (a) 构造: 接口 `StrRel14If`; `semJ` (一切不变量, 一切 $\Lambda$, 一切层); 不变量 `I₁` 及其封闭; 节点规则的归约 `node-red`; 实例 `cpBad`; 顶层的值引理 `shiftV`. (b) 值: `ne-pos` (满足 `NE` 的状态, 第 $0$ 层读数严格大于底) 与 `shiftV` (错一格的值比较) 是关于值的定理. **关于闭项的值 (严格增长或界), 本轮没有结果.**

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `Inv`, `SemJ`, `HAWJ`, `RelX`, `SemX`, `OAcX`, `R∀X`, `HAWX`, `CPᴸ`, `NodeObl`, `NodeObl⁼`, `NodeSound`, `TopOut`, `TopV` | StrRel14If | 接口 (只有类型) | 定义 |
| `sem-n0` … `sem-pr`, `WalkR.walkR`, `haw↾J` | StrRel14SemJ | `StrRel12Sem` 的六条规则与走法, 状态前提换成 `Inv` 的 `J` | 定理 (生成) |
| `NiS.sem-ni` | StrRel14NiJ | 同层节点规则, 带不变量 | 条件定理 (分支与坐标层的语义作模块参数, 由 `semJ` 填上; 生成) |
| `KpS.sem-κ` | StrRel14KpJ | `nκ` 规则, 带不变量 | 条件定理 (同上; 生成) |
| **`Sem.semJ`**, `semJ∀` | StrRel14J | 一切 `I : Inv`, 一切层: `Rel L x x′ → SemJ L x x′` | **定理** |
| `haw→J` | StrRel14J | `HAW` ⇒ `HAWJ` | 定理 |
| `I₀`, `I₁`, `NE`, `ne⊕`, `necv` | StrRel14J | 两个不变量; `NE` 经 `⊕`, `cv` 封闭 | 定义, 定理 |
| **`ne-pos`**, `¬NEY₀` | StrRel14J | `NE` ⇒ 第 0 层读数的和 $>\beta$; 空状态不满足 `NE` | 定理 (值) |
| `hY₁`, **`inst₁`** | StrRel14J | `NoΩ Λ` ⇒ $Y_1$ 满足 `I₁`; `semJ I₁` 对 $\Omega_\Lambda$ 给出 `OAc` | 定理 (前提可满足) |
| **`Red.node-red`** | StrRel14Rk | $k\sqsubseteq_\infty k'$ ⇒ 异质节点对的 `SemX` 由三种义务 (`OblRR⁼`, `OblKK⁼`, `OblKR⁼`) 给出 | 条件定理 (三种义务) |
| `kr-vac`, `Diag.krDiag` | StrRel14Rk | 坐标层相同时 `OblKR⁼` 空真 | 定理 |
| `κlit`, `κRk` | StrRel14Rk | `CPᴸ` 分支对 ⇒ $g\,c\sqsubseteq_\infty g\,c'$ ⇒ `rk-mono` 适用 | 定理 |
| **`cpBad`**, `tcBad`, `rkBadL`, `rkBadR`, `kL≡`, `kR≡` | StrRel14Bad | $\Omega^{\mathsf H}$: `CP` 分支对 $(\lim_n 0, 0)$ 上的两个分支节点, 在一对 `TC` 目标上是 "左升右留" | 定理 (实例) |
| **`¬alCell0`**, `avR≡` | StrRel14Top | `MonoStep Ωᴴ` 两边第 0 格的走法路径没有 `Al` 对齐 (对一切 $d'$, $L$, $L'$) | 否定 (定理; 只否定用 `Al` 对齐这两条路径) |
| **`shiftV`** | StrRel14Top | 错一格的值比较: $x$ 对 $b_0$, $a_n$ 对 $b_{n+1}$ ⇒ $\Sigma_\beta(x⨾\mathrm{nl}\,a)\le\Sigma_{\beta'}(n_0⨾\mathrm{nl}\,b)$ | 定理 (值) |
| `inst₂` | 本文 | `inst₁` 在 $\Lambda=2$ 上 | 定理 |

## 前提实例

- `semJ` 的 `I`: `I₀` (就是 `StrRel12` 的设定), `I₁` (加上 `NE`). 前提 `HAWJ` 与状态 `J`: `inst₁` 对一切 `NoΩ Λ` 全部填上 ($Y_1$, `haAct`, `cpOne`, `ΩR`); `inst₂` 是 $\Lambda=2$ 的情形.
- `NiS.sem-ni`, `KpS.sem-κ` 的模块参数: 由 `semJ` 的归纳填上 (同 `StrRel12`).
- `node-red` 的三种义务: 坐标层相同时, `OblKR⁼` 由 `krDiag` 给出 (空真). **`OblRR⁼` 与 `OblKK⁼` 没有实例.** 坐标层不同、目标层夹在中间时, `OblKR⁼` 要 "节点对极限", 而 `RelX` 没有这样的构造子 (判断; 对 `Rel` 的编译形式是 `StrRel13Kr.¬krX`). 所以对坐标层不同的节点对, `node-red` 目前没有可满足的前提, 只给出了义务的分解.
- `shiftV` 的两个前提: 任何逐段的值比较都可以. 例如 $x=n_0$, $a=b\circ\mathrm{suc}$ 时可由 `≤` 的单调得到 (判断, 未写).
- `κlit` 的 `LgH (hΩ g)`: 取 `Lg-Ωᴴ`. `cpBad` 是闭的实例.

## 1 第一个障碍 (判断, 依据 `node-red` 的义务与 `HtFeedFold.Chn` 的字面)

坐标层不同 ($k\sqsubseteq_\infty k'$, $k\ne k'$) 时看 `OblRR⁼` (两边都升): 两边的输出分别是坐标层 $k$ 与 $k'$ 的链的极限. 逐项比较这两条链要两样东西:

- (i) 链的起点 `yc (d Y) (tg self hk lW)` 对 `yc (d Y′) (tg self hk′ lW′)`, 即状态在**两个不同的目标层** $k$, $k'$ 上的读数相关;
- (ii) 链的每一步是上一步运行的输出在目标层 $k$ 对 $k'$ 上的读数.

`OAcX`/`R∀X` 只在同一目标层上比, 这两样都在它们的定义域之外. 若把输出关系推广到目标层对 $(t,t')$ ($t\sqsubseteq_\infty t'$), 种类对就不再只有三种. 例: 坐标层 $k=k'=0$, 目标层对 $(0,1)$ 上是 "左升右留" (判断, 未编译). 所以下一步要在接口里增补 "跨目标层" 的状态关系 (StrRel13 §3 的 (a)), 并重新检查它的定义域.

同一处还挡着 `κˣ`. `κˣ` 只要求 `CPᴸ` 分支对上的分支相关, 它的可靠性要求折叠走过的每个位置对都带字面的 $c\lhd c'$. 树世界相同、右边状态是左边状态的字面延长时, 位置对在对角线上 (判断); 一般情形未证. **`κˣ` 的可靠性本轮没有证.**

## 2 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `Inv` (三条律) | `StrRel12` 的证明里, 状态只经 `advRc`, `cvRc` 与两个分量进入 (`semJ` 逐字照抄后编译通过) | **树逼的** |
| `NE` | `Step` 的字面 (`ω⋅ (Ωd t ⨾ …)`); `StrRel13Later` 的反例状态是空状态 | **树逼的** |
| `RelX` 的 `niˣ` 带 $k\sqsubseteq_\infty k'$ | `rk-mono` 的前提; `cpBad` | **树逼的** (律的定义域) |
| `CPᴸ` ($c\lhd c'$) | `cpBad`; 由 `LgH` 的单调得到 `κlit` | **树逼的** (律的定义域) |
| `NodeObl⁼` (带等式的义务) | `RunNi` 在节点处是 `RKi … (rkT …)`; `kr-vac` | **树逼的** |
| `TopV`/`TopOut` 只比第 0 层的值 | `StrRel13Om.¬cpTop`; `¬alCell0` | **树逼的** |
| `shiftV` (错一格) | `κc` 的格路径: 左边多一步 $0\to1$ (`¬alCell0`) | **树逼的** |
| 生成脚本 `mk_semj.py` | 工程 (逐字照抄 + 换名) | 脚手架 (不进树) |

**归类: 提供信息.** 没有新的构造子或节点字段 (新增的构造子属于关系, 不属于树), 没有改树与折叠, 没有 `Lab`, 没有记号. `semJ` 是一个证明, 对一切不变量与一切层成立; 新增的字段都由律的定义域或折叠的字面逼出. 否定 `¬alCell0` 划出一个不能用的形状: 用 `Al` 对齐顶层第 0 格的两条路径. `cpBad` 划出一个不能有的律的定义域: 只带值的分支对上的跨坐标层节点规则. 这一站新用到的字段: `κc` 第 0 格的路径 `⊲-tr q₀ (sum-fst W (z Y))` 的构造子形状, `LgH (hΩ g)` 的单调分量, `RunNi` 的 `rkT` 参数.

## 3 接手清单

1. **坐标层为 $0$ 的跨层节点** (StrRel13Val 的 `xL`/`xR` 正是这一种). 左坐标层为 $0$ 时, `RelX hz k′` 的推导只用六条与层无关的规则 (第 $0$ 层没有节点, 也没有 `nκ`). 判断: `SemX hz k′` 只用这六条规则归纳即可得到. 做法: 照 `StrRel14SemJ` §3 写出 `SemX` 的六条规则 (两边的层分开), 再试 `OblRR⁼`, `OblKK⁼`.
2. 在接口里增补 "跨目标层" 的状态关系 (目标层对 $(k,k')$ 上的 `RelX k k′`), 检查它的定义域, 看它经 `⊕` 是否封闭 (这要求输出在 $(k,k')$ 上相关; 见 §1).
3. `OblKR⁼` (坐标层不同): 结论层要有 "节点 $\le$ 极限". 第 $0$ 层以外可以先加读法; 第 $0$ 层的 `genAl` 要给 `Al` 加构造子 (`StrRel13Kr.¬alLim0`), 或者写成否定.
4. `κˣ` 的可靠性 (`CPᴸ` 分支对): 先在 "树世界相同、状态是字面延长" 的情形证.
5. 顶层: 展开 `Walk` 的 `lim` 一句, 让 `MonoStep Ωᴴ` 两边的输出对上 `shiftV` 的形状. 错一格之后, 要比的是坐标 $c$ 的格对坐标 $c+1$ 的格 (坐标层 `emb c` $\sqsubseteq_\infty$ `hs (emb c)`), 又回到第 1 项.
6. 然后才轮到 `HAW Ωᴴ` 与 $\Omega^{\mathsf H}$ 处的 `MonoStep`, 再看 $T_\Omega<T_{\Omega+1}$.

## 4 审计 (2026-11-05)

- 冷编译: 删掉本组 9 个模块的 `.agdai`, 从入口重编: 退出码 0, 约 11 秒, 峰值常驻约 1.3G (`-M6G`). 代码块里 `postulate`, 洞, `TERMINATING`, `NON_TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext`, K 的出现次数都是 0. 终止全由结构检查给出.
- 生成文件: 重跑 `python3 probes/Survey/scripts/strrel14/mk_semj.py .`, `StrRel14SemJ`/`NiJ`/`KpJ` 逐字节相同 (md5 核对).
- 导入闭包 (`importclosure.py`; `--only` 同 `MonoPort7`/`9`: `OCF.Free.Level`, `OCF.BTBO`, 以及 `OCF.Align.` 下的 `CumReadCF`, `TLRule`, `TLOpsW`, `SumOne`, `BrwMid`, `LayerTr`, `CvFold`, `CvHigh`, `CvLayer`, `NoCumLit`, `L1Val`, `DVal`, `HtGen`, `HtFeed`, `HtCross`, `KVal`, `KNest`, `MonoPort`, `StrRel`): 入口闭包 68 个模块 (本地 58, 库 10). `If`, `J`, `Rk`, `Bad`, `Top` 各自单跑, 也都是禁用表 0, `--only` 之外 0.
- 定义级切片 (`depslice.py`): 到达块数 `inst₁` 305, `semJ` 277, `sem-ni` 225, `sem-κ` 220, `node-red` 149, `krDiag` 143, `κRk` 67, `rkBadR` 47, `¬alCell0` 39, `ne-pos` 38, `cpBad` 22, `shiftV` 21; 记号模块 0, 记号词 0. 正对照 `Om1HnAccept:label-term₀` 到达 1188 块, 记号模块 92, 记号词 58. 切片看不见模块应用, 块数偏少; 记号无关由导入闭包保证.

## 5 文件与行数

| 文件 | 行 (代码, 去空行与注释) | 内容 |
|---|---|---|
| `StrRel14If` | 141 | 接口 (手写) |
| `StrRel14SemJ` | 121 | **生成**: 六条规则, 走法 |
| `StrRel14NiJ` | 79 | **生成**: 同层节点 |
| `StrRel14KpJ` | 123 | **生成**: `nκ` |
| `StrRel14J` | 77 | `semJ`, `I₀`, `I₁`, `ne-pos`, `inst₁` (手写) |
| `StrRel14Rk` | 67 | `node-red`, `krDiag`, `κRk` (手写) |
| `StrRel14Bad` | 53 | `cpBad` (手写) |
| `StrRel14Top` | 37 | `¬alCell0`, `shiftV` (手写) |
| 入口 | 13 | |
| 合计 | 711 | 生成 323, 手写 388 |

## 0 模块

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel14 where

open import Data.Unit using (tt)
open import OCF.Align.HtFeedTree using (H; hz; hs)
import OCF.Align.StrRel14If
import OCF.Align.StrRel14J as J
import OCF.Align.StrRel14Rk
open import OCF.Align.StrRel14Bad public using (cpBad; tcBad; rkBadL; rkBadR; kL≡; kR≡)
open import OCF.Align.StrRel14Top public using (¬alCell0; avR≡; shiftV)

-- inst₁ 的前提可满足: 不含 Ω-极限的 Λ = 2
Λ₂ : H
Λ₂ = hs (hs hz)

module J₂ = J Λ₂ tt

inst₂ = J₂.inst₁ tt
```
