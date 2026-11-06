# 第 1 层差树的值语义: 入口

> **判决: PARTIAL, 以否定为主.** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> 问题是: 用什么值语义比较第 1 层差树 (`D one W`), 才能让折叠 (`SumOneFold.Run`, $\psi_0(\Omega_{\Omega+1})$ 里的那一个) 对输入值单调. 现有的值是 `toB` 读成第 1 层布劳威尔树后的 $\preccurlyeq$ (`LayerTrBase`), 它对 `ni`, `nκ` 取分支的上确界. 本组的结论:
>
> 1. **(c) 三条编译过的否定, 都在真实场景里** (折叠 `SumOneClosed`, 动作 `Step`, 世界 $1$, 目标第 0 层; 链 `Chn` 在第 1 层上跑时顶层 `Ai` 归约到的就是 `Step`):
>    - `L1ValShape.¬Bis-mono`: 两棵树的 `toB` 逐分支字面一致 (`Bis`), 折叠一个 $\ge1$ 一个 $0$. 所以**任何经由 `toB` 的值语义都不行**, 不论 $\preccurlyeq$ 还是逐分支的结构关系: `toB` 只在 `dif y` 的位置调用分支, 折叠在 `Run` 的前缀上调用, 形状不同.
>    - `L1ValSup.¬mono-on-Mono`: $\sum_z1\preccurlyeq\sum_z z$ (`toB`), 两者分支都对坐标值单调 (`Mono`), 折叠一个 $\ge1$ 一个 $0$. 所以 **`ni` 不能用上确界比**, 而且 `Mono` (现有 `Kn-mono`, `KL-mono` 的判据) 不够.
>    - `L1ValKappa.¬toB-mono-κ`: 只含 `nκ` 的两棵树, 质量放在世界 $1$ 与世界 $2$, `toB` 左 $\preccurlyeq$ 右, 折叠一个 $\ge1$ 一个 $0$. 所以 **`nκ` 也不能用上确界比**. `LayerTr` §3 的 "极限世界读不回" 因此不是关键: 读回的是上确界的值, 那对折叠不够.
> 2. **两条一步定理, 对一切输入** (`L1ValBase`): 链一旦有一个链点没有 `n1`, 以后全部为零 (`chain-stall`); 回灌一旦有一格输出没有 `n1`, 以后全部为零 (`κ-stall`). 后两条否定的机制都是它: 目标第 0 层的折叠只在链点 / 回灌层之下读分支, 那里是零就停. 由此逼出一个判据 `Pos` (分支处处 $\succcurlyeq1$): 反例 $\sum_z z$ 不满足 (`x₂-not-pos`); 折叠在 $\psi_0(\Omega_{\Omega+1})$ 里真正产出的读坐标节点 `Kn` 满足 (`Kn-pos`).
> 3. **(a), (b) 没有做成.** 没有给出新的值前序, 也没有证出折叠对一般第 1 层输入的单调. 现在知道它们必须是什么形状 (§3), 所以这两项写作 "未走通", 不是否定. `CtxMonoAccept.accept-Ω+1` 的前提 `Up`, `Lo` 没有碰 (那是 `NoCumNode` 的树, 验收侧). $\psi_0(\Omega_{\Omega+1})$ 仍然只有下界 (`SumOneAccept.step-T₁`).

## 1 定理

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `low`, `zup`, `sep` | L1ValBase | `has1` 判出的第 0 层树和 $\ge$ 底 $+1$; 没有 `n1` 的树和 $\le$ 底; 两者不 $\le$ | 定理 |
| `RunZ`, `RunZA` | L1ValBase | 折叠走没有 `n1` 的第 0 层树, 或动作总给零, 输出没有 `n1` | 定理 |
| **`chain-stall`**, `stall-from` | L1ValBase | 链点 $\delta_n$ 没有 `n1` ⇒ 第 $n$ 段与 $\delta_{n+1}$ 都没有 | 定理 (一切输入, 一切动作) |
| `Walk-Z`, `sf-fst`, `sf-lg` | L1ValBase | 沿没有后继步的路径走层, 输出零; 零树的 `sum-fst` 路径与 `Lg-sum` 没有后继步 | 定理 |
| **`κ-stall`**, `κ-from` | L1ValBase | 回灌第 $n$ 格输出零 (且层的合法性无后继步) ⇒ 第 $n+1$ 格同样 | 定理 (一切 `nκ` 分支) |
| `Bis`, `Bis→≼`, `Bis-I`, `toB-Bis` | L1ValShape | `toB` 在 `dif` 的形状上从不经过坏形状; 两棵树 `toB` 逐分支字面一致 | 定理 |
| `big`, `small`, `fold-sep` | L1ValShape | 折叠: $x_b\ge1$, $x_0=0$ | 定理 (`big` 由检查器归约) |
| **`¬Bis-mono`**, `¬toB-mono`, `ub-not-mono` | L1ValShape | 否定; 反例分支不 `Mono` | 定理 (否定) |
| `up-low`, `up-high`, `mono₁`, `mono₂` | L1ValSup | $b+\uparrow z$ 就是加上 $z$ 的和; 两棵树分支都 `Mono` | 定理 |
| `toB-le` | L1ValSup | $\mathrm{toB}(\sum_z1)\preccurlyeq\mathrm{toB}(\sum_z z)$ | 定理 |
| `big`, `small`, `fold-sep` | L1ValSup | 折叠: $\sum_z1\ge1$, $\sum_z z=0$ (第 0 段归约, 以后 `chain-stall`) | 定理 |
| **`¬mono-on-Mono`** | L1ValSup | 在 `Mono` 的输入上 `toB` 单调也不成立 | 定理 (否定) |
| `Pos`, `x₂-not-pos`, **`Kn-pos`** | L1ValSup | 不停滞判据; 反例不满足; 折叠产出的 `Kn` 满足 (一切状态) | 定理 |
| `K-bd`, `KR-bd`, `g-bd`, `toB-le` | L1ValKappa | 质量在世界 $1$ 的 `nκ`, 一切世界、一切路径上的部分和 $\preccurlyeq1$; `toB` 左 $\preccurlyeq$ 右 | 定理 |
| `big`, `R0`, `small`, `fold-sep` | L1ValKappa | 折叠: $x_\kappa\ge1$, $x'_\kappa=0$ (第 0 格归约, 以后 `κ-stall`) | 定理 |
| **`¬toB-mono-κ`** | L1ValKappa | 只含 `nκ` 的输入上 `toB` 单调不成立 | 定理 (否定) |

**否定的范围.** 三条都只否定 "以 `toB` 为值、对 (相应一类) 全部第 1 层输入" 的单调. 不否定: 直接定义在差树上 (看得见坐标) 的关系; 加了判据的输入类 (例如 `Mono` 加 `Pos`, 或下面 §3 的逐分支关系); 目标第 $\ge1$ 层; 别的折叠. 前提都可满足: 反例是具体的项, `Bis`, `Mono`, `toB-le` 都是对它们证的.

**有限测试.** 无. `big` 三处与 `R0`, `seg0`, `d1` 是对具体项的归约 (`refl` 或由 η 解出的 `⊤` 元组), 算定理.

## 2 第一个障碍

值语义必须同时满足 (由 §1 逼出, 编译过的部分是否定, 下面的拼合是判断):

- 定义在**差树**上, 分支对**差树坐标** $w$ 给出, 不经 `toB` (`¬Bis-mono`); 或者限制到分支只依赖坐标值的输入 (`Mono` 在 `toB` 之外的版本).
- 对 `ni`, `nκ` **逐分支**比 (同一坐标, 同一世界与路径), 没有 "左边分支都 $\preccurlyeq$ 右边 ⇒ 节点 $\preccurlyeq$ 右边" 这条 (`i≼`, `κ≼`) (`¬mono-on-Mono`, `¬toB-mono-κ`). 形状同 `BTBOVal` 记录的 `Dn`: 极限节点只有 "同层逐分支" 与 "看链起点" 两条.
- 第 0 层的部分 (`n0`, `n1`, `⨾`, `nl`, `nw`) 仍按值比 (`CvLayerRun.cong0` 那样, 经规范形).

**第一个障碍**: 这种混合关系里, 两种比较要在同一棵树里交替出现 ($x ⨾ \mathrm{ni}\,u$ 对 $(x' ⨾ n0) ⨾ \mathrm{ni}\,u'$), 需要第 1 层的结构律 (单位、结合、`nl` 的部分和) 与逐分支规则相容; 在这之上证 "折叠单调" 的形状是 `CvLayerRun` 换掉值: 第 $k$ 层输入单调 ⟸ 分支的坐标单调 (按新关系) + `Int` 单调 + 对分支的同一命题. 没有写. 估计与 `CvLayerRun` 加 `CvHighCong` 同量级 (约 600 行), 判断.

## 3 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `L1ValBase` | 无. `Z`, `has1`, `SFP`, `SFL` 是零/一的结构判据; `Mono` 照 `Kn-mono` 的结论形状 | 提供信息 |
| `L1ValShape` | 无. 坏形状读自折叠 `Run` 与 `I` 的坐标记法之差 | 提供信息 |
| `L1ValSup` | 无. 两棵树是 $\Omega_1$ 的主体与 `CvLayerInst.xs`; `Pos` 由 `chain-stall` 逼出 | 提供信息 |
| `L1ValKappa` | 无. 质量的位置读自回灌 `κc` 的半开区间 $[W,v)$ | 提供信息 |

折叠与闭项用 `SumOneClosed` ($S=\cdot\omega$ 抄自旧折叠), 同 `CvFold`, `CvLayer`. 没有新构造子, 没有新折叠规则. 每条结果说出它新用到的字段: `¬Bis-mono` 用 `ni` 分支的**坐标形状** (`Run` 前缀对 `I` 位置); `¬mono-on-Mono` 用 `ni` 分支**在链点上的值**; `¬toB-mono-κ` 用 `nκ` 分支**在回灌层之下的世界**; `chain-stall` 用链点 $\delta_n$ (`Chn`), `κ-stall` 用回灌层 `v` 与路径 `av` (`Cl`).

## 4 审计

见报告. `importclosure.py --only` 树侧模块: 干净. `depslice.py`: `L1ValShape:¬Bis-mono`, `L1ValSup:¬mono-on-Mono`, `L1ValKappa:¬toB-mono-κ` 到达的记号定义为 0, 正对照 `Om1HnAccept:label-term₀`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.L1Val where

open import OCF.Align.L1ValBase using (Z; ZD; has1; low; zup; sep; RunZ; RunZA; chain-stall; stall-from; SFP; SFL; Walk-Z; κ-stall; κ-from; Mono; out; val) public
open import OCF.Align.L1ValShape using (Bis; Bis→≼; toB-Bis; toB-≈; ¬Bis-mono; ¬toB-mono; ub-not-mono) renaming (fold-sep to fold-sep-shape) public
open import OCF.Align.L1ValSup using (mono₁; mono₂; toB-le; ¬mono-on-Mono; Pos; x₂-not-pos; Kn-pos) renaming (fold-sep to fold-sep-sup) public
open import OCF.Align.L1ValKappa using (K-bd; g-bd; ¬toB-mono-κ) renaming (toB-le to toB-le-κ; fold-sep to fold-sep-κ) public
```
