# 结构关系, 第十五轮: 跨目标层的状态关系, 左坐标层为 $0$ 的跨层节点: 入口

> **判决: PARTIAL (构造一路).** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 不改树、折叠、合法性, 不改已有文件 (只新建 `StrRel15`, `StrRel15If`, `StrRel15Sem`, `StrRel15Node`, `StrRel15Fin`, `StrRel15Bar`).
>
> **对纲领与目标意味着什么 (判断).** 全在第 4 层 (关系与语义), 不碰树. 得到的是 (1) 跨目标层的状态关系下, 左坐标层为 $0$ 的跨层节点的升升与留留两种义务是定理, 并给出一条值的定理; (2) 第一个障碍的编译形式: 结论关系 `RelX` 缺 "节点对极限" 与 "极限对节点" 两种规则, 它们在折叠里实际出现 (左留右升, 左升右留), 而且后者让跨目标层的输出关系在折叠下不封闭, 与跨坐标层无关. 本轮没有给出 $T_\Omega<T_{\Omega+1}$, 也没有给出它的界; 接手清单第 (b), (c) 步没有开始, 理由是第 (a) 步的否定 (`StrRel15Bar`).
>
> 交付 (按 `AGENTS.md` "交付拆成闭项与值"). (a) 构造: 接口 `StrRel15If`; 两条状态律 `law⊕`, `lawcv`; 异质的六条规则; `semX0` (左层为 $0$ 的语义, 一切右层); `node-red²` (节点对归到四种义务); `Zero.oblRR`, `Zero.oblKK` (左坐标层为 $0$, 一切右坐标层与一切 $\Lambda$, 条件: 分支动作的 `HAW²` 与 `J²`); 实例 `rrInst`, `kkInst` (`xL`/`xR`, 前提全部填上). (b) 值: **`valRR`**: 实例上第 $0$ 层的读数和 $\Sigma_0(\mathrm{xL})\le\Sigma_0(\mathrm{xR})$ (`StrRel13Val.¬valX` 的同一不等式, 状态从 `Yv` 换成满足 `J²` 的 $Y_1$). **关于闭项的值 (严格增长或界), 本轮没有结果.**

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `TX`, `OA²`, `R²`, `J²`, `Law⊕`, `Lawcv`, `KLaw.LawKp`, `KLaw.LawKb`, `HAW²`, `SemX²`, `NodeObl²` (`OblRR²`, `OblKK²`, `OblKR²`, `OblRK²`), `NodeSound²`, `NodeSound²₀` | StrRel15If | 接口 (只有类型) | 定义 |
| **`law⊕`**, **`lawcv`** | StrRel15Sem | `Law⊕`, `Lawcv` | 定理 |
| `sem-n0` … `sem-pr` (`Six`) | StrRel15Sem | 异质的六条规则, 结论在目标层对上 | 定理 |
| **`semX0`** | StrRel15Sem | 一切 $L'$: `RelX hz L′ x x′ → SemX² hz L′ x x′` | 定理 |
| `z⊑`, `sOutX`, `haw↾²` | StrRel15Sem | $0\sqsubseteq_\infty k$; 从 `BelowX` 取坐标层的 `RelX`; 动作前提沿 `AP` 搬运 | 定理 |
| **`Red².node-red²`** | StrRel15Node | 节点对的 `SemX²` ⇐ 四种义务 (按实际种类, 对一切运行上下文) | 条件定理 (四种义务) |
| **`Zero.oblRR`**, **`Zero.oblKK`** | StrRel15Node | 左坐标层 $0$, 右坐标层 $k'$ 任意: `Top`, 分支动作 `HAW² hz k′`, `J²` ⇒ `OblRR²`; 后两者 ⇒ `OblKK²` | 条件定理 (`HAW²` 前提, `J²`) |
| `Fin`, `ΩRX²`, `stepOA²`, `hawAct²`, `hY₁` | StrRel15Fin | 有限的 $\Lambda$: $\Omega_t$ 跨层相关, `Act` 的 `HAW²`, $Y_1$ 的 `J²` | 定理 (前提可满足) |
| `hawAi`, **`rrInst`**, **`kkInst`** | StrRel15Fin | 实例 $\Lambda_2$, `xL`/`xR`, $Y_1$: 升升与留留义务 | 定理 |
| **`valRR`** | StrRel15Fin | $\Sigma_0(\text{xL 在 } Y_1 \text{ 上的输出})\le\Sigma_0(\text{xR 在 } Y_1 \text{ 上的输出})$ | **定理 (值)** |
| `¬Yv` | StrRel15Fin | `StrRel13Val` 的反例状态 `Yv` 不满足 `J²` | 否定 (定理) |
| `rr14`, `kk14` | 本文 | 同一实例上 `StrRel14If.NodeObl⁼` 的 `OblRR⁼`, `OblKK⁼` (同层目标) 成立 | 定理 |
| **`¬oblKR`**, **`¬oblRK`** | StrRel15Bar | 实例上 `OblKR²`, `OblRK²` 不成立 (输出头是 `ni`/`nl`, `RelX` 无此规则) | 否定 (定理) |
| **`¬semXLR`**, `¬NodeSound²`, `¬NodeSound²₀` | StrRel15Bar | `SemX² Λ₂ Λ₂ xL xR` 不成立; 接口的节点可靠性 (含左坐标层 $0$ 的特例) 不成立 | 否定 (定理) |
| **`¬semXLL`**, **`¬sem∀²`**, `relLL` | StrRel15Bar | `RelX xL xL` 成立而 `SemX²` 不成立; "`RelX` ⇒ `SemX²`" 对层 $2$ 不成立 | 否定 (定理) |
| **`¬J²Ω`**, `¬ΩΩ` | StrRel15Bar | $\Omega^{\mathsf H}$, 世界 $1$: $Y_1$ 不与自己 `J²` 相关; $\Omega_1$ 对 $\Omega_\Omega$ 不 `RelX` 相关 | 否定 (定理) |

## 前提实例

- `Zero.oblRR`/`oblKK` 的前提: `Top` 取 `cp00`; 分支动作的 `HAW² hz (hs hz)` 取 `hawAi` (分支是常数 `n1`, `Ai` 化成 `Act`, 由 `stepOA²` 填上); `J²` 取 `hY₁` (有限 $\Lambda$ 上一切世界对). 实例 `rrInst`, `kkInst` 全部填上.
- `node-red²` 的四种义务: 在 `xL`/`xR` 上升升与留留有实例; **左留右升与左升右留没有实例, 而且在这组参数上是假的** (`¬oblKR`, `¬oblRK`). 所以 `node-red²` 对这一对节点不可用.
- `SemX²` 的前提 (`¬semXLR`, `¬semXLL` 用到的): `cp00`, `hawAct² Λ₂ Λ₂`, `n0ˣ`, `hY₁ tt tt`, 都是定理; 否定不是空真.
- `Fin` 的实例: $\Lambda_2$ (`tt`). 不满足的例子: 含 $\mathbb N$-极限或 $\Omega$-极限的高度; 那里 `ΩRX²` 在 $\Omega$-极限处不成立 (`¬ΩΩ`).
- `¬J²Ω` 没有前提.

## 1 第一个障碍 (编译形式在 `StrRel15Bar`)

接手清单 (a) 的第二部分 ("再试升升与留留义务") 走通了 (`oblRR`, `oblKK`). 剩下两种义务与 (b) 卡在同一处:

- **左留右升** (目标对 $(t,t')$ 上左边留成节点, 右边升成链): 输出是 `ni …` 对 `nl …`. `RelX` 没有两边头是这样的构造子 (`¬oblKR`). 这是 `StrRel13Kr.¬krX` 在跨目标层接口里的再现.
- **左升右留** (只在目标层不同时出现): 输出是 `nl …` 对 `ni …`, 同样没有规则 (`¬oblRK`). **它对同一个节点与自己也出现** (`¬semXLL`): 坐标层 $j$ 的节点在目标层 $t\sqsubseteq j\sqsubset t'$ 上就是这样. 所以跨目标层的输出关系 `OA²` 在折叠下不封闭, "`RelX` ⇒ `SemX²`" 不成立 (`¬sem∀²`).

后果 (判断, 依据上面两条与 `oblRR` 的证明): (b) 推广到一般 $k\sqsubseteq k'$ 时, 链的每一步要 `SemX² k k′` (层 $k$ 的树有节点), 在最后的目标对上节点会落到左留右升或左升右留; 链上状态的 `J²` 要折叠的输出 `OA²` 相关, 而左升右留使它们不相关. 所以 (b) 在现有的结论关系里不成立的那一部分, 由 `¬semXLL` 的同一机制给出; 本轮没有写 (b) 的一般否定. (c) 另有一处: $\Omega^{\mathsf H}$ 上闭项的状态 $Y_1$ 不满足 `J²` (`¬J²Ω`, 因为 $\Omega_1$ 对 $\Omega_\Omega$ 是 `ni` 对 `nκ`), 所以 `HAW Ωᴴ` 一类的前提在本接口里对闭项不可满足.

**下一步要的东西 (判断, 未试).** 结论关系加两种规则: "节点 ≤ 链的极限" (左留右升) 与 "链的极限 ≤ 节点" (左升右留), 以及 `ni` 对 `nκ` (第 4 条). 它们的形状由 `RKi` 的两句字面给出 (树逼的), 但可靠性要对后续的运行再分情形: 例如 "极限 ≤ 节点" 的右边节点在更低的目标上会升成链, 两条链的段之间没有逐项的对应. `StrRel13Later.¬laterV` 在 `R∀c` (含空状态) 下否定过 "节点 ≤ 极限" 的读法; 在 `J²` (带 `NE`) 下没有试. 这是 (b) 之前必须先回答的问题.

### 与否定一路 `StrRel15N` 的对照, 与路线的选择

否定一路 (对着同一份定稿 10:48 的接口) 独立得到同一处: `RelX` 没有 (`nl`, `ni`), (`ni`, `nl`), (`nl`, `n0 ⨾ nκ`) 三种对, `NodeSound²`, `NodeSound²₀` 为假, `OblKR²`, `OblRK²` 实际出现时为假; `Law⊕`, `Lawcv` 成立 (与本路 `law⊕`, `lawcv` 一致); `OblRR²`, `OblKK²`, `LawKp`, `LawKb` 没有否定. 本路的 `oblRR`, `oblKK` 是前两者在左坐标层 $0$ 上的正面结果.

它给的两条出路, 本路**都没有实现**, 只做了选择上的判断:

- **出路二 (语义不在跨过节点坐标层的目标对上比输出): 判断不可取.** `oblRR` 的证明读的正是这样一对: 链的起点是状态在 (坐标层 $k$, 坐标层 $k'$) 上的读数 (`Zero.Chain.cs zero`), 对 `xL`/`xR` 就是目标对 $(0,1)$, 而坐标层 $0$ 的节点跨过它. 拿掉这类目标对, 升升义务就没有链起点的前提. `¬semXLL` 说 `xL` 与自己的两次运行的输出在 $(0,1)$ 上不 `RelX` 相关, 所以 `Law⊕` 不能把它们加进状态; 两者合起来, 出路二与升升义务冲突 (判断, 依据是 `oblRR` 的证明与 `¬semXLL`, 没有写成一条否定定理).
- **出路一 (给跨目标层的输出关系加规则并证可靠): 推荐, 未试.** 见下面 "下一步要的东西" 与接手清单第 1 项. 本路对接口没有改动 (变更记录不变); 加规则要新的关系, 按 "只增" 应另开接口或在本接口后增补一节.

## 2 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `TX` (目标层对带 $t\sqsubseteq_\infty t'$) | `RKi` 的 `rise` 句: 链从状态在**坐标层**目标上的读数起; 两边坐标层不同 ⇒ 两个不同的目标层 (`StrRel14` §1) | **树逼的** |
| `OA²`, `R²` | 同上; `Chn` 每步读运行输出在坐标层目标上的值 | **树逼的** |
| `J²` 的 `NE` | `StrRel14NegInv.inv-kill` (零树读数的状态对推出反例) | **树逼的** (否定) |
| 四种义务 (多出左升右留) | `rkT` 在两个不同目标层上分别取值; `¬oblRK` 说它实际出现 | **树逼的** |
| `Fin`, `ΩRX²` | `Ωd` 的字面 (`hs` 层是 `n1 ⨾ ni`) | **树逼的** |
| `z⊑` 作 `niˣ` 的证据 | `niˣ` 要字面 $\sqsubseteq_\infty$ (`StrRel14If`) | 脚手架 (关系侧) |

**归类: 提供信息.** 没有新构造子或节点字段, 没有改树与折叠, 没有 `Lab`, 没有记号. `oblRR`/`oblKK` 是对结构参数 (右坐标层 $k'$, 一切 $\Lambda$) 的一步定理, 这一站新用到的字段: `Chn` 的起点 `yc (d Y) (tg self hk lW)` 在两个**不同**目标层上的读数 (由 `J²` 给出), `BNi` 的状态 `cv p Y ⊕ Run z …`. 否定 `¬oblKR`, `¬oblRK`, `¬semXLL` 划出不能有的形状: 以 `StrRel14If.RelX` 为结论关系、在跨目标层的目标对上比输出的语义; `¬J²Ω` 划出: 含 $\Omega$-极限的层上以 `RelX` 写的跨目标层状态不变量不含闭项的状态.

## 3 接手清单

1. **结论关系的两条新规则** (§1 "下一步"): 给 `RelX` 的异质版加 "节点 ≤ 链的极限" 与 "链的极限 ≤ 节点" (形状取 `RKi` 两句的字面), 先在 $\Lambda_2$ 的 `xL` 对自己 (`¬semXLL` 的那一对目标) 上问: 加了之后语义能否成立. 最便宜的决定性实验: 写出 "极限 ≤ 节点" 规则后, 对 `xL` 在 $(0,1)$ 目标对上的两个输出, 再运行一次 (第 $0$ 层目标), 比第 $0$ 层的和 (仿 `StrRel13Later`).
2. 若 1 成立: 重做 `oblRR`/`oblKK` 的证明 (结论关系换了), 再证 `OblKR²`, `OblRK²`; 然后 (b) 一般 $k\sqsubseteq k'$.
3. `ni` 对 `nκ` 的规则 (`¬ΩΩ`), 让 $\Omega^{\mathsf H}$ 上闭项的状态进入不变量; 然后 (c).
4. `LawKp`, `LawKb` (接口 §3) 本轮没有证; 左层为 $0$ 时用不到 (没有 `nκ`).

## 4 审计 (2026-11-05)

- 冷编译: 删掉本组 6 个模块的 `.agdai` (逐个写模块名, 未动 `StrRel15N*`), 从入口重编: 退出码 0, 约 7 秒, 峰值常驻约 1.1G (`-M6G`). 代码块里 `postulate`, 洞, `TERMINATING`, `NON_TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext`, K 的出现次数都是 0. 终止全由结构检查给出 (`semX0` 对推导, `Chain.cs` 对 $n$).
- 导入闭包 (`importclosure.py`, `--only` 同 `StrRel14`: `OCF.Free.Level`, `OCF.BTBO`, 以及 `OCF.Align.` 下的 `CumReadCF`, `TLRule`, `TLOpsW`, `SumOne`, `BrwMid`, `LayerTr`, `CvFold`, `CvHigh`, `CvLayer`, `NoCumLit`, `L1Val`, `DVal`, `HtGen`, `HtFeed`, `HtCross`, `KVal`, `KNest`, `MonoPort`, `StrRel`): 入口闭包 72 个模块 (本地 62, 库 10), 禁用表 0, `--only` 之外 0.
- 定义级切片 (`depslice.py`): 到达块数 `oblRR` 189, `oblKK` 191, `node-red²` 140, `semX0` 169, `law⊕` 64, `valRR` 236, `rrInst` 220, `kkInst` 221, `¬semXLL` 184, `¬NodeSound²` 185, `¬J²Ω` 185, `rr14` 231; 记号模块 0, 记号词 0. 正对照 `Om1HnAccept:label-term₀` 到达 1188 块, 记号模块 92, 记号词 58. 切片看不见模块应用, 块数偏少; 记号无关由导入闭包保证.

## 5 文件与行数

| 文件 | 行 (代码, 去空行与注释) | 内容 |
|---|---|---|
| `StrRel15If` | 93 | 接口 (手写) |
| `StrRel15Sem` | 101 | `law⊕`, `lawcv`, 六条规则, `semX0` |
| `StrRel15Node` | 94 | `node-red²`, `Zero.oblRR`, `Zero.oblKK` |
| `StrRel15Fin` | 81 | `Fin`, `ΩRX²`, `hawAct²`, `hY₁`, `rrInst`, `kkInst`, `valRR`, `¬Yv` |
| `StrRel15Bar` | 74 | `¬oblKR`, `¬oblRK`, `¬semXLR`, `¬NodeSound²`, `¬semXLL`, `¬sem∀²`, `¬J²Ω` |
| 入口 | 24 | `rr14`, `kk14` |
| 合计 | 467 | 全部手写, 没有生成文件 |

## 0 模块

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel15 where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Align.HtFeedTree using (hz; hs; hself; n0; n1; accL)
import OCF.Align.CumReadCF as C
import OCF.Align.StrRel11Rk as Rk
import OCF.Align.StrRel14If as If
import OCF.Align.StrRel15If
import OCF.Align.StrRel15Sem
open import OCF.Align.StrRel15Node public using (module Red²; module Zero)
open import OCF.Align.StrRel15Fin public using (Fin; module FinΛ; module Z; hawAi; rrInst; kkInst; valRR; ¬Yv)
open import OCF.Align.StrRel15Bar public using (¬oblKR; ¬oblRK; ¬semXLR; ¬NodeSound²; ¬NodeSound²₀; relLL; ¬semXLL; ¬sem∀²; ¬ΩΩ; ¬J²Ω)
open import OCF.Align.StrRel13Val using (Λ₂; r₀; r₁)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel15Fin using () renaming (module FinΛ to F)

-- 与 StrRel14 的同层义务对接: 同一实例上, StrRel14If.NodeObl⁼ 的升升与留留成立
open Rk Λ₂ tt using (s∞)
module P₂ = At Λ₂ tt
module O14 = If.NodeObl⁼ Λ₂ tt {lV = tt} {lV′ = tt} r₀ r₁ (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL (hs hz))
                         C.self C.self hself hself P₂.Act P₂.Act n0 n0 (F.Y₁ Λ₂ tt tt tt) (F.Y₁ Λ₂ tt tt tt)

rr14 : O14.OblRR⁼
rr14 T T′ tc eL eR = rrInst T T′ (tc , s∞) eL eR

kk14 : O14.OblKK⁼
kk14 T T′ tc R R′ eL eR = kkInst T T′ (tc , s∞) R R′ eL eR
```
