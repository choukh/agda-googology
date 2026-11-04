# `tH` 的基本列是树生成的, 还是抄记号的 (路线审查实验 1)

> **判决.** 分三句, 档次不同.
>
> 1. **不用新节点的原则版写得出来, 带证书, 严格过 `T⊤` (定理), 但与 `tH` 不同形; 值是判断: 只到下一批不动点, 不超过 $\psi_0(\Omega_{\Omega^2}\cdot2)$, 低于 $\psi_0(\Omega_{\Omega^2+1})$ 基本列的第 1 项.** 编译的依据是: 它严格高于 `T⊤`, 它是闭包点, 单个世界装不下那条链; 它与 $\psi_0(\Omega_{\Omega^2+1})$ 的关系没有定理.
> 2. **缺的一件就是对象层绑定: 叶子 `Ω̇ᵀ M 0` 要是数据树节点, 分支在更高的世界.** 依据: 折叠的叶子是本世界的 `Ω̇` (`leaf-ψ`), 把分支放进世界 $M$ 的两种写法都是类型错误 (下文), 把全部世界放进一个 `HtB` 被 `no-all-Ord`, `all-Ord→LPO` 否定. 这说明 "写不进现有数据树", **不是** 说明别的数据树也不行.
> 3. **这个绑定能由原则表述, 不引用记号的项.** "回灌闭包的分支可以把绑定的下标当作层": `tH` 就是 `Node` 的闭包放进数据树. 有了这片叶子, $\alpha\ge1$ 的基本列是现成规则生成的 (`TLOneLeaf`: 同一组折叠规则对叶子参数化; `TLOneTest`: 第 1 项与 `ψ̄ᵀ (ψᵀ zero (ιT zero (Ω̇ᵀ cz 0)))` 同形). **所以抄记号的不是基本列.** 第 0 支 `𝟏ᵀ` 是例外, 见翻译账. 这一条的证据到测试档, 且我写原则版时已经读过 `tH`, 不算盲.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 这不算树自足: 见文末.

## 时间线

1. 读 `AGENTS.md`, `probes/README.md`, `RouteReview` §1, §2, §4.3 实验 1, 以及 `TreeLangFeed`, `CrossMClosed`, `CrossMTop`, `CrossMNode`, `CrossM`, `CrossNext` 与树侧底座.
2. 写 `TLOneDef`, `TLOneV`, `TLOneThm`, `TLOneLeaf`, 编译.
3. 之后才打开 `CrossMAccept`, `CrossNextAccept`, `EBO`, 写 `TLOneAccept`.

**污染.** 第 1 步已看到: 任务书的 "要折叠 $\Omega_u$ 本身"; `RouteReview`, `CrossM`, `CrossNext` 转述的 `fs-ψΩ1-1`, `fs-2` 的结论; `tH` 的全部代码. 所以: `Tᶠ`, `Tᴬ`, `Tᴮ`, `Tᶜ` 只用现成规则, 不依赖这些, 但选择去试什么不是盲的; `L-self` 明确是看了 `tH` 之后的改写. 没有读记号的定义和基本列的算法.

## 定理 (编译过)

| 定理 | 陈述 | 文件 |
| --- | --- | --- |
| `dom-α` | 对一切 `HtB`: $a\preceq$ 第 $a$ 行的层号 | [TLOneV](TLOneV.lagda.md) |
| `V-≺`, `V-lim`, `Ω≺`, `ι-top` | 第 $a$ 行严格递增, 极限连续, 从 `ValueJudgeLadder` 移到 `HtB` | 同上 |
| `above-α` | `suc lv⊤ ≼ lv (Tᵖ M p (suc lv⊤))`, 对一切 $M$, $p$ | [TLOneThm](TLOneThm.lagda.md) |
| `above-h`, `above-ν` | `suc lv⊤ ≼ lv Tᴮ`, `suc lv⊤ ≼ lvᶜ` | 同上 |
| `next≻` | 迭代严格升 | 同上 |
| `T⊤≺T̃ᴬ`, `T⊤≺T̃ᴰ` | 字面 $\prec$ | 同上 |
| `below-chain` | 链 $C_n$ 上任何位置的第 0 行 $\prec$ `νT 𝒯 M₀` | 同上 |
| `dom-row` | 任何一行 (任何 $\alpha$) $\preceq$ 把它喂给高度之后的第 0 行 | 同上 |
| `fixᶜ-up`, `fixᶜ-dn`, `fixᶜ-out`, `fixᶜ-ht` | `Tᶜ′ x` 的输出与高度互相共尾, 对一切 $x$ | 同上 |
| `clo-up`, `clo-dn`, `Tᶜ≼T̃ᴰ` | `Sum` 闭包的链点与分支互相控制 | 同上 |
| `no-world` | 对任何节点, 没有码 $M$ 使一切 $C_n\subset M$ | 同上 |
| `no-lift` | $M\subset M'$ 而 $M$ `ᶜ+ ⌈η⌉` $\not\subset M'$ `ᶜ+ ⌈η⌉` | 同上 |
| `leaf-ψ`, `leaf-Ψ`, `top-new` | 折叠的叶子是本世界的 `Ω̇`; 新世界的顶高于旧世界的像 | 同上 |
| `Y` (定义) | 绑定被折叠后的输出落回世界 $M$, 没有新构造子 | [TLOneLeaf](TLOneLeaf.lagda.md) |
| `fs-0`, `fs-1`, `fs-2′`, `lt-a`, `lt-b`, `lt-c`, `lt-d`, `lt-3` | **只关于记号**, 见下 | [TLOneAccept](TLOneAccept.lagda.md) |

**否定的范围.** 这里的否定只有 `no-world`, `no-lift`, 只否定写明的陈述: 单个码含整条链; 分支只按 $\eta$ 索引时用 `⊂` 上移. 它们不否定别的上移办法, 也不否定别的数据树. 已有的 `no-all-Ord`, `all-Ord→LPO` (`LadderOrdNeg`) 只否定单一的高度类型; 前提的可满足性那边写了.

**字面的 `Tᶠ`.** `ψ̄ (Ω̇ (suc lv⊤))` 有证书 (`GᴺΩ̇`), 但**值没有定理**: `dom-α` 只证到带高度的树, `OCF/Free` 的树与它之间这里没有接桥. `above-α` 的 `Tᴬ` 是它在 `HtB` 上的同形写法. 判断: `Tᶠ` 也严格过 `T⊤`.

**上界.** 严格高于 `T⊤` 有定理; **再往上没有定理**: 我给不出 "原则版 $\preceq$ 某棵已知的树, 而 `Tᵀ cz 1` 严格更大", 因为 `Tᵀ cz 1` 没有证书, 没有值 (`CrossNext` 的 (c), $\alpha\ge1$ 未走通). 所以判决 1 的值的部分是判断. 能编译的上界只有两类: `below-chain` (第 0 行在闭包点之下) 和 `dom-row` (任何一行被高度控制).

## 有限测试 (不是证明)

[TLOneTest](TLOneTest.lagda.md). 比较器 `refl`, 看 `shape d`: 深度 $d$ 的形状树, 闭包节点看界, 起点, 第一支, `suc c` 处的分支. 盲区: 不看值, 分支只看一个 $\eta$, 极限只看前两项, 深度有限. `noCert₂` 的教训: 种类全过不算证据.

| 比的 | 结果 | 盲区 |
| --- | --- | --- |
| `Lo.Tᴸ` 与 `Tᵀ` (深度 5, $\alpha=0,1$) | 相同: 参数化没有改树 | 只到深度 5 |
| `Tᵀ cz 1` 第 0 项与 `Tᵀ cz 0` | 相同 | 同上 |
| `Tᵀ cz 1` 第 1 项与 `ψ̄ᵀ (ψᵀ zero (ιT zero (Ω̇ᵀ cz 0)))` | 相同: 基本列是链规则 | 同上 |
| 头 (深度 3) | `L-orig`, `L-self`, `L-row`, `zʰ` 第 0, 1 项都是闭包: **头分不开有没有绑定** | 头不看界 |
| 界 (深度 3) | `L-orig`, `L-self` 是 0; `L-row`, `zʰ` 不是 0 (`s ·`) | 界只是 `tH` 落成 `ŝ` 时的写法 |
| 起点 | `L-orig` 第 0 项的起点是极限 ($\omega$, 由 `𝟏ᵀ`), `L-self` 是闭包 | 不看链 |
| `L-cst lv⊤`, $\alpha$ 槽 `zᵃ` | 头三层都是极限, 没有闭包 | 同上 |
| `#z` 第 1 项 | `L-orig` 深度 9: 55; `L-row` 深度 9: 0; `zʰ`, `zᵃ` 深度 7: 0 | 界是 0 不等于绑定; 深度不同 |

**同形的结论.** 前两项: 高度槽原则版 `zʰ` (`Tᵖ (cs ⌈lv⊤⌉) end 1`) 与 `Tᵀ cz 1` 头同, 界不同, 第一支不同. 所以不是 "同形". `L-self` 与 `Tᵀ cz 1` 只差第 0 支. 它带绑定, 所以不算不新增字段的原则版.

## 读法与值 (判断)

记 $\beta$ = `T⊤`, 读作 $\psi_0(\Omega_u)$, $u=\Omega^2$ (这本身是判断, 没有标签).

**为什么 `Tᴬ` 一下就过了 $\beta$.** 字面的读法 "$\psi_0(\Omega_{\Omega\cdot\omega+\beta+1})$" 是错的. 这个序数在记号里低于 $\beta$, 而 `above-α` 说树严格高于 $\beta$. 树里 $\alpha$ 是参数, 不必进闭包: 它读作带常数的折叠. 这是 [CrossM](CrossM.lagda.md) 的 "读法在闭包点之上不成立" 对 $\alpha$ 槽的版本.

**上界的论证 (纸面, 没有编译).** 带常数 $M$ 的世界嵌入不带常数的 OCF: 把世界里的 $\psi_0(x)$ 映成 $\psi_0(\Omega_u+x)$, $\psi_\nu(x)$ ($\nu\ge1$) 不动. $\Omega_u$ 给出 $\beta$ 这个常数, $\nu\ge1$ 时常数本来就在闭包里. 这样 $\mathrm{row}(M,\alpha)\le\psi_0(\Omega_u+\Omega_{\Omega\cdot(1+M)+\alpha})$. `fs-2` (定理, 只关于记号) 说 $\psi_0(\Omega_u+\Omega_u)$ 是 $y\mapsto\psi_0(\Omega_u+\Omega_{\psi_1(y)})$ 的闭包, 所以它对上面的 $M$, $\alpha$ 封闭. 由此 `Tᴬ`, `Tᴮ`, `Tᶜ`, `Tᵏ′`, `T̃ᴬ`, `T̃ᴰ` 以及把它们再迭代有限或可数次的结果都不超过 $\psi_0(\Omega_u\cdot2)$. 嵌入保序这一步我只是认为成立, 没有检查细节.

**与 $\psi_0(\Omega_{\Omega^2+1})$ 的关系.** 判断: **严格低.** `lt-b`, `lt-c` (定理, 只关于记号): $\psi_0(\Omega_u\cdot2)<\psi_0(\psi_u(\Omega_u))<\psi_0(\Omega_{u+1})$, 而 $\psi_0(\psi_u(\Omega_u))$ 是后者基本列的第 1 项 (`fs-1`). 树与记号之间没有定理.

**直观.** $\Omega_u$ 高于世界里任何层, 被折叠之后 ($\psi_\nu(\Omega_u)<\Omega_u$) 能落回世界 (`Y`), 但 $\psi_0(\psi_\nu(\Omega_u))<\beta$, 不长高. 要 $\psi_0(\Omega_u+x)$ 以上, $\Omega_u$ 本身要作被加数, 作被折叠对象 (`⊞`, `ψᵀ`), 这就要它是数据. 世界内的原则版只是常数 $\beta$ 的折叠, 这是两件事.

**其他叶子.** `L-row`, `L-cst lv⊤`: 判断是低得多. $\psi$ 穿过低层节点, 只把叶子换掉, 后继变成乘 $\omega$, 所以是下一个 ε 数量级的算术. `L-self` 与 `L-orig`: 判断同一个闭包点, 没有定理; 起点不影响上确界是通常的情形, 这里没有验证.

## 第一个障碍

把 $\Omega_u$ 写进世界 $M$ 的数据树, 两种不新增构造子的写法都是类型错误.

分支直接是更高世界的第 0 行 (`qŝ zero 𝟏L (λ η _ → Ω̇ {M ᶜ+ ⌈η⌉} end zero)`):

```text
error: [UnequalTerms]
M ᶜ+ ⌈ η ⌉ != M of type Code
when checking that the expression 𝕎.Ω̇ {M ᶜ+ ⌈ η ⌉} end zero has
type
OCF.Align.LadderOrdTree.Q₊ (HB M) end zero ...
```

分支经 `↓ᴾ` 下移回世界 $M$ (`↓ᴾ (⊂+ M ⌈η⌉) end zero (Ω̇ {M ᶜ+ ⌈η⌉} end zero)`):

```text
error: [UnequalTerms]
end != up (⊂+ M ⌈ η ⌉) end of type Pos (cs (M ᶜ+ ⌈ η ⌉))
when checking that the expression 𝕎.Ω̇ {M ᶜ+ ⌈ η ⌉} end zero has
type L.B.Q (⊂+ M ⌈ η ⌉) (L.u (⊂+ M ⌈ η ⌉) end) zero _φ_10 _χ′_11
```

`top-new` 说第二个等式对 $\eta$ 的后继情形确实是假的, 新的顶严格高于像. 报错只说这两种写法不行.

**下一个障碍不变.** `Tᵀ` 的 $\alpha\ge1$ 没有证书, 见 [CrossNext](CrossNext.lagda.md) 的 (c). 这一轮没有碰, **未走通, 不是否定.**

**一个工程上的坑.** `Tᵏ zero = T⊤`, `lvᵏ zero = lv⊤` 这样两个子句的函数, 右边是闭项时, `TLOneDef` 本身 400 秒没检查完 (原因没查); 改成对起点参数化后 12 秒. 闭合世界上比较 `forceᴺ` 的不同写法同样爆, 全部定理都对变量证. 这是写法问题, 不是否定.

## 翻译账

`tH` 这一行新增了什么, 读自哪里. 依据是判断, 带编译依据的写明.

| 字段 | 来源 | 依据 |
| --- | --- | --- |
| `Ω̇ᵀ M 0` 是数据节点, 不是 `Z` 层的 `νZ` | **树逼的** | 折叠对数据树递归, 叶子进 `⊞`, `ψᵀ`; 两个报错 |
| 分支在更高世界 ($M'$) | **树逼的** | 第一个报错; `top-new`; `no-world` |
| Kripke 分支 (对一切 `e : M ⊂ M′`, 不只 `⌈η⌉`) | **树逼的** | `no-lift`, 上移算子 `↑T`, `⊞` 过 `tH` 时要 |
| `T₊` 对 $M$ 索引 | **树逼的** | 分支里 `W ⊞ row(M′)` 同时含 `W` 和 $M'$ 的行 (判断, 没有编译另一种设计的否定) |
| `tΩ` 的 Kripke, `tΩ↓`, `↑T`, `Raise`, `↓ᴾ`, `ΨT` 的 `tH` 行 | **树逼的** | 类型 |
| 新高度默认地板 `Fl` | **树逼的** | `CrossM` 已写 |
| $\alpha\ge1$ 的基本列 (`tΩ` 链) | **现成规则生成** | `Ω̇ (suc α)`, `ψᵒ` 的 `oΩ` 行的逐字移植; `TLOneLeaf`; 第 1 项测试 |
| 分支是 `stepT` (世界顶上第 0 行) | 与 `𝒯` 同一选择, **树的 `Node` 已用** | `branch≈`; "第 0 行" 这个选择本身账上读自记号 (`LadderOrdTree`) |
| 第 0 支 `𝟏ᵀ` | **读自记号** ($\gamma_0=1$, 经 `rowL` 的第 0 项) | `CrossM` 的自述; `L-self` 不用它也能写, 值的关系没有定理 |
| `ŝ` 的界取 0 | 工程 | `Sum` 的 `gc` 以 `z⊑` 用它 |
| `Q₊`, `ψᵠ` 的其余形状 | 账上读自记号 (`LadderOrdTree`) | 这里没有改, 没有回答 |

**不算树自足的原因.** 下一步的定义 (要不要 $\Omega_u$) 是看到值不够之后才知道的, 而 "值不够" 的判断用了记号的序 (`lt-b`). 树侧能独立说的只到: 第 0 行与高度互相共尾 (`Fix`), `row` 全被高度控制 (`dom-row`), 叶子不出世界 (`leaf-ψ`). 树侧还没有一个判据能说 "这里必须加绑定", 这正是下一个该补的东西.

## 壁垒

没有新的下标类型. `lv⊤` 是可数的 `Ordᴵ`. 比较都在一个世界内或 `Sum` 的字面前缀里. `Sum` 的链点不比较, `below-chain` 的比较在 $C_{n+1}$ 这个字面公共上界. 所以 `barrier`, `no-tri-code` 的前提都不被要求.

## 审计

记号只在 [TLOneAccept](TLOneAccept.lagda.md), 入口不导入它. 数字见下; 切片看不见模块别名, 看闭包.

- **导入闭包:** `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.LadderNF --only OCF.Align.LadderMono --only OCF.Align.LadderInf --only OCF.Align.LadderOrd --only OCF.Align.CrossM --only OCF.Align.CrossNext --only OCF.Align.TLOne OCF.Align.TLOne`: 退出码 0, 禁用表 0, `--only` 之外 0, 72 个本地模块. 正对照 `OCF.Align.TLOneAccept`: 禁用表命中 `EBO`, 退出码 1.
- **定义级切片 `depslice.py` (块数, 记号块, 词命中):** `Tᶠ` 1627, 0, 0; `Tᴮ′` 1084, 0, 0; `Tᶜ′` 1192, 0, 0; `above-α` 1235, 0, 0; `above-ν` 1216, 0, 0; `below-chain` 1195, 0, 0; `no-world` 63, 0, 0; `no-lift` 24, 0, 0; `L-self` 195, 0, 0; `Y` 374, 0, 0. `T̃ᴬ` 103, `T̃ᴰ` 103 也是 0, 0, 但这两个数偏小: 它们经模块别名 `ClᴬM`, `ClᴰM`, 切片看不见别名的实参, 看闭包. 正对照 `TLOneAccept:lt-b`: 53, 43, 2.
- **禁用构造:** 全部 `TLOne*` 没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, `--cubical`; 全部带 `--safe --without-K`.
- 闭包是编译器保证的不引用, 不说明定义没有受记号启发: 见上面的污染和翻译账.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOne where

open import OCF.Align.TLOneDef public
open import OCF.Align.TLOneThm using ()
open import OCF.Align.TLOneLeaf using ()
open import OCF.Align.TLOneTest using ()
```

## 导航

| 文件 | 内容 |
| --- | --- |
| [TLOneDef](TLOneDef.lagda.md) | 原则版, 理由, 时间线 |
| [TLOneV](TLOneV.lagda.md) | $\alpha$ 严格增长, `dom-α` |
| [TLOneThm](TLOneThm.lagda.md) | 定理 |
| [TLOneLeaf](TLOneLeaf.lagda.md) | 对叶子参数化的折叠, 四片叶子, `Y` |
| [TLOneTest](TLOneTest.lagda.md) | 有限测试 |
| [TLOneAccept](TLOneAccept.lagda.md) | 记号一侧 |
