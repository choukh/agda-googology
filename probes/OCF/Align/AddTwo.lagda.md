# $S=\cdot2$: 一格 $\cdot\omega$ 能不能由高层节点的链补回

> 入口. **判决: PARTIAL.** 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 定义与定理 ([AddTwoSim](AddTwoSim.lagda.md)) 不读记号, 不读旧树. 这一轮没有验收文件: 没有新的序数值定理.
>
> 一句话: 要的引理写出来了, 而且编译过 (`simStep`: 一格 $\cdot2$ 后面接一个高层节点, 就盖住一格 $\cdot\omega$; `leafy`: 对没有节点的输入一路成立). 但它**只管一层**: 链里的输入是状态, 放不进链自己那一层以上的节点, 链自己那一层上的 $\cdot\omega$ 没有东西模拟. 补上要的是值上的吸收 (两条链的上确界相同, 逐项不可比), 结构关系 `Rel` 表达不了. 所以 $\cdot2$ 的下界, $+1$ 的严格差, $\psi_0(\Omega_{\Omega+1})$ 上 $\cdot2$ 与 $\cdot\omega$ 的比较, 都**未走通**; 没有否定.

## 定理表 (编译过)

| 定理 | 文件 | 说的是什么 |
|---|---|---|
| `TL`, `weakR`, `First.first`, `First.tlRun` | AddTwoSim | 输入有顶层叶子, 折叠的输出就至少有一格 $S(\Omega_t+Z_t)$; 顶层叶子走过折叠还在 |
| `Sim.simChain` | AddTwoSim | 节点 $N_j=\sum_{z:j}1$, 目标 $t\lhd j$, 状态在 $j$ 上有顶层叶子: $c\cdot\omega\trianglelefteq$ 节点的输出, 只要 $c\trianglelefteq\Omega_t+Y'_t$ |
| `Sim.simStep` | AddTwoSim | 同上, 输入是 $1$ 接 $N_j$, 不要另外的前提 |
| `Sim·2` | AddTwoSim | $S=\cdot2$ 的实例 ($S$ 只要 "膨胀" 并保持顶层叶子) |
| `Leafy.leafy` | AddTwoSim | 没有节点的输入 $x$: 世界 $j$ 里的 $\psi^{\omega}_t(x)\trianglelefteq$ 世界 $W\rhd j$ 里的 $\psi^{\cdot2}_t(x[1\mapsto 1+N_j])$, 对一切 $t\lhd j$ |

## 目标 1: $\cdot2$ 的下界

**未走通.** 走法和断点:

1. 一格: `simStep`. 左边一格 $\cdot\omega$ 在目标 $t$ 上是 $(\Omega_t+Y_t)\cdot\omega$. 右边一格 $\cdot2$ 后接 $N_j$ ($t\le j$): 节点对 $t$ 是链, 每一段的输入是状态在 $j$ 上的差, 有顶层叶子, 所以每一段至少一格 $\Omega_t+Y'_t$. 这是定理.
2. 传下去: `leafy`, 对 `⨾`, `nl`, 状态的累积都成立. 这是定理.
3. **断在链.** 左边输入里有节点 $\sum_{z:i}u$ 时, 目标 $t\le i$ 上它是链, 链的每一段是 `D i` 的树 (状态), 下一段是这一段在目标 $i$ 上的折叠. 右边对应的链也一样. 在目标 $i$ 上, 左边每片叶子乘 $\omega$, 右边每片叶子乘 $2$, 而 `D i` 里没有 $\ge i$ 的节点可以放, 第 1 步的模拟没有地方用. 换层 (左边第 $i$ 层对右边第 $e(i)$ 层, 例如 $e(t)=2t$) 也一样: 右边的链在自己那一层 $e(i)$ 上照样只有 $\cdot2$.
4. **差的是什么 (判断).** 链自己那一层上, $\cdot\omega$ 的链是 $\alpha\mapsto\Omega_i\cdot\omega^\alpha$ 的迭代, $\cdot2$ 的链是 $\alpha\mapsto\Omega_i\cdot2^\alpha$ 的迭代. 上确界相同 ($2^{2^\alpha}\ge\omega^\alpha$ 对大的 $\alpha$), 但逐项不可比: 左边第 $n$ 段的叶子要 $\omega$ 份, 右边任何有限段都只给有限份 (右边在这一层的 `nl` 只来自输入和 $\Omega_i$ 本身). 所以要的是**值上**的吸收引理, 例如 "两次 $\cdot2$ 的折叠在值上不低于一次 $\cdot\omega$ 的折叠, 当输入含一个无穷和", 不是 `Rel` 的一条规则.
5. **试过并放弃的规则 (判断).** 给 `Rel` 加 "$x\trianglelefteq\sum_z G(z)$ 若对某个 $z_0$, $x\trianglelefteq G(z_0)$". 对目标高于节点的情形对, 对链不对: 链只走到坐标的不动点, $z_0$ 可能在它之外, 这时 $G(z_0)$ 根本不在值里. 加上 "$z_0\trianglelefteq$ 状态在节点层的差" 的条件才对, 但那样关系要随状态变, 不是独立的归纳关系. 这与 `no-full` (不存在对全部分支严格单调的折叠) 同根, 但 `no-full` 只杀全分支的版本, 不杀带条件的.

**下界是不是假的.** 没有见证. 判断它成立, 依据是上面第 4 条的值的算术和 `TLRule` 的纸面算例 ($\psi^{\cdot2}_0(\Omega_1\cdot2)=\varepsilon_0=\psi^{\omega}_0(\Omega_1)$).

## 目标 2: $+1$ 严格小

**未走通.** 缺的是从大世界往小世界压的工具. `AddCloRel.Main` 只从 $W_1\lhd W_2$ 的小世界比到大世界; `simStep` 也是往上. 要证 $T^+\prec\psi_0(\Omega_\Omega)$, 至少要一个固定的值 $V\prec$ `BTBOᴵ` (例如 $\psi^{\omega}_0(\Omega_2)$), 和 "$\psi^+_0(\Omega_y)\le V$ 对一切 $y\le V$" (判断: $\psi^+_0(\Omega_y)$ 约 $\varepsilon_{y}$ 一类). 后者要把大世界的层 ($y$ 的全部可数层) 映进小世界的可数位置 ($\Omega_1$ 之下), 并让折叠沿这个映射往下比; 链在左边是 "上确界被压低" 的方向, `Rel` 同样表达不了. 没有写.

## 目标 3: $\psi_0(\Omega_{\Omega+1})$

`SumOneFold` 对 $S$ 参数化 (模块参数 `S`), 所以 $S=\cdot2$ 的 $T_1$ 是现成的闭项. **两侧都未走通**:

- $T_1^{\cdot2}\preccurlyeq T_1^{\omega}$ (上侧) 要 `Rel` 在 `SumOneFold` 上的单调. 这里比 `TLRuleSum` 多一件: 回灌 `κc` 的世界是 `sum W (z Y)`, 由状态的第 0 层输出算出. 两个 $S$ 的状态不同, 世界就不同; `Rel z z′` 只给 `sum W z ≤ sum W z′` 的值, 不给字面的 $\lhd$. 所以要折叠对层的值单调 (一般 $S$ 的 `Ψ-emb`), 现在只有旧树 $\cdot\omega$ 有. 字面的版本也走不通: 第 $n+1$ 个世界是 `sum v d₀`, 两边的 $v$ 已经不同, 要 $v\lhd v'\Rightarrow$ `sum v d ⊲ sum v′ d`, 左边这一半正是 `CumReadBase.no-⊞-left` (编译过) 否定的形状 (`sum` 与 `⊞` 同形). 它否定的是字面版本, 不否定值的版本, 也不否定整条路线.
- 下侧要目标 1.

## 目标 4: 结论

| 问 | 答 | 档 |
|---|---|---|
| 在 $\psi_0(\Omega_\Omega)$, $\cdot\omega$ 是不是带里的一个代表 | **是, 对已证的带.** 带 $\{S:\omega\trianglelefteq S\trianglelefteq\omega\}$ 里每个 $S$ 值相等 (`T-1+cω`, `T-c+cω`), 一步的值都恰是 $c\cdot\omega$ | 定理 (上一轮, `AddCloAccept`) |
| 带是否含 $\cdot2$ (从而含不加法封闭的 $S$) | 判断含. 下界的单层模拟是定理 (`simStep`, `leafy`), 链上的吸收没有定理 | 判断 |
| 带是否含 $+1$ | 不含: $\Omega_1$ 上值就不同 (`gap-Ω₁`); 这一站的严格差未走通 | 定理 ($\Omega_1$); 判断 (这一站) |
| 更高的站带是否只要选一次 | 判断: 是, 只要每一站的验收都走 "同一世界里比 $S$, 参照折叠换层" 的形状; 但 $\Omega_{\Omega+1}$ 起回灌的世界依赖 $S$ (`κc`), 这个形状不再直接适用 | 判断 |

所以: **这条约定在 $\psi_0(\Omega_\Omega)$ 是挑带里的一个代表, 这一句在 "带" 取 $\omega\trianglelefteq S\trianglelefteq\omega$ 时是定理; 带有没有宽到 $\cdot2$, 和更高的站是不是同一个带, 是判断.**

## 条件定理

没有.

## 有限测试

没有新增.

## 第一个障碍

见目标 1 第 3 条. 写的过程中没有停机或类型的报错卡住 (`TL` 的第一版把 $\Omega_t$ 当成叶子, 报 `n1 != (n1 ⨾ N.Dif t …)`, 改成 `tlL (tlL tl1)` 即过).

## 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `AddTwoSim` | 没有新的树字段, 没有证书. `TL` 是折叠逼出的 (链的每一段要有一格) | 树侧 |

**时间线.** 这一轮另读了 `SumOne`, `SumOneTree`, `SumOneFold` (陈述和折叠). 没有打开 `EBO`, `Correspond`, `Label`.

## 审计

见报告; 结果抄在下面.

- **导入闭包:** `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRule --only OCF.Align.AddClo --only OCF.Align.AddTwo OCF.Align.AddTwo`: 退出码 0, 禁用表 0, `--only` 之外 0.
- **定义级切片 (块数 / 记号块 / 词命中):** `AddTwoSim:simStep` 89/0/0, `AddTwoSim:simChain` 88/0/0, `AddTwoSim:leafy` 101/0/0. 正对照 `TLOpsAccept:label-TΩ` 1019/92/58.
- **禁用构造:** `AddTwo*` 没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, `--cubical`.
- 只保证不引用, 不说明没受记号启发.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AddTwo where

open import OCF.Align.AddTwoSim public using (TL; weakR; module First; module Sim; module Sim·2; Lf; emb₁; module Leafy)
```
