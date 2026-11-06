# 结构关系, 第十九轮: `up` 作新构造子, 动作的语法 `ActS`, kZ 形的时间条件 (构造一路): 入口

> **判决: PARTIAL.** 决定性实验过: 折叠里实际运行的动作都定义性地属于 `ActS`, 而 `NegSR18Up.¬UpSoundR` 与 `NegSR17RkT.¬RkSoundT` 的反例所用的产生时动作 `Az` 不属于 (定理). `up` 让 `StrRel17Obs` 的障碍目标对可推导 (定理). 但 `up` 的可靠性 `UpSoundZ` 与 `rk⁺⁺` 的可靠性 `RkSoundZ hz (hs hz)` 都约化到一个新的第一个障碍 (约化定理): 再折叠目标对 $(T_1,T_1)$, 左边的层 $1$ 高于右边节点的坐标层 $0$, 右边节点再次保留, `up` 在那里用不上. 所以接手清单的第 3 步 (一般 $k\sqsubseteq k'$, $\Omega^{\mathsf H}$ 处 `MonoStep`, $T_\Omega<T_{\Omega+1}$) 没有开始. 值的一侧: kZ 形的时间条件在 `cv` 之后的再折叠状态上成立 (那里 `DomL` 不成立), 并给出 `xL` 那一对在 $(\tau_0,\tau_0)$ 上的值 (定理); 关于闭项的值: 没有. 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 不改树、折叠、合法性, 不改已有文件 (只新建 `StrRel19`, `StrRel19If`, `StrRel19Act`, `StrRel19Sem`, `StrRel19Up`, `StrRel19Val`).
>
> **对纲领与目标意味着什么 (判断).** 全在第 4 层 (关系与语义), 不碰树. (1) "规则前提的正证书" 的最便宜形式可行: 闭项从 `Act` 起, 折叠只在六处造新动作, 每处都是 `Ig↾` 或 `Ai`, 所以动作的语法 `ActS` 由折叠的字面给出, 不读记号, 作规则前提时是正的; 它排除了上两轮否定所用的读累计的外来动作 (`¬ActS-Az`). (2) 把右层改成指标后, `up` 作为构造子不撞严格正性 (接口编译通过). (3) 但结构关系里 "某物 $\le$ 节点" 的规则仍只有逐字取自折叠子句的 `rk⁺⁺` 与 `up`; 两者都要求左边低于同一节点的某个**上升**输出, 而坐标层为 $0$ 的节点只在第 $0$ 层目标上上升. 再折叠到第 $1$ 层目标时, 左边的层 $1$ 没有可用的上升目标. 判断: 缺的是一条不按折叠子句写的、统一的 "$x\le$ 节点" 规则 (例如 "$x\le$ 节点的某个分支输出 ⇒ $x\le$ 节点"), 不是更多的时间条件或动作限制.
>
> 交付 (按 `AGENTS.md` "交付拆成闭项与值"). (a) 构造: 接口 `StrRel19If`; `Sites` (六处加起点), `act-fκ`, `act-AiK`, `act-A²R`, `actNoZ₂`; `semS00` 与有限 $\Lambda$ 的 `hawsAct`, `hY₁⁺⁺`, `domZY₁`; `emb00`, `back00`; `obs⁺⁺`; `invNi⁺⁺`. (b) 值: `valZ`, `valZV`, `exCv` (`xL` 那一对, $(\tau_0,\tau_0)$, 含 `cv` 之后的再折叠状态). 关于闭项的值 ($T_\Omega<T_{\Omega+1}$ 或界): 没有.

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `ActS`, `LeX⁺⁺`/`RelX⁺⁺` (含 `up`), `OA⁺⁺`, `R⁺⁺`, `J⁺⁺`, `HAW⁺⁺`, `HAWS`, `SemS`, `DomZ`, `UpSoundS`, `UpSoundZ`, `RkSoundZ`, `OblRRZ`, `Emb⁺⁺` | StrRel19If | 接口 (只有类型), 定稿 2026-11-05 16:01 | 定义 |
| `Sites.top`, `siteAi`, `siteRKi`, `siteBNi`, `siteKp`, `siteKb`, `siteκΔ` | StrRel19Act | 闭项的起点与折叠造动作的六处, 类型逐字写折叠里的项, 输入属于 `ActS` ⇒ 输出属于 (一切 $\Lambda$) | 定理 |
| `Iκ.act-fκ`, `Iκ.act-AiK`, `I₂.act-A²R` | StrRel19Act | 闭项里的三个动作属于 `ActS` (`AiK` 是读累计的那个) | 定理 |
| `L2.noAi₂`, `L2.actNoZ₂` | StrRel19Act | $\Lambda_2$ 上第 $2$ 层没有 `sAi`; 第 $2$ 层的 `ActS` 动作满足 `NoZ` | 定理 |
| **`L2.¬ActS-Az`** | StrRel19Act | `Az` (第 $2$ 层, 世界 $0$) 不属于 `ActS` | **否定 (定理)** |
| `law⊕⁺⁺`, `ext⁺⁺`, `domZR`, `domZmono` | StrRel19Sem | `J⁺⁺` 对 `⊕` 封闭; `DomZ` 对两边与右边的延长封闭 | 定理 |
| **`Sem00.semS00`** | StrRel19Sem | `RelX⁺⁺ hz hz ⇒ SemS hz hz … Ok`, 对一切单调的 `Ok` | 定理 |
| `FinΛ⁺⁺.ΩRX⁺⁺`, `stepOA⁺⁺`, `hawAct⁺⁺`, `hawsAct`, `hY₁⁺⁺`, `domZY₁` | StrRel19Sem | 有限 $\Lambda$: `Act` 满足 `HAWS`; `J⁺⁺ Y₁ Y₁`; `DomZ` 在 $(Y_1,Y_1)$ 上 | 定理 |
| `emb00`, `back00` | StrRel19Up | 第 $0$ 层: `RelX⁺` 与 `RelX⁺⁺` 互相包含 | 定理 |
| **`obs⁺⁺`** | StrRel19Up | `RelX⁺⁺ hz (hs hz) ReL ReR` (`StrRel17Obs` 的障碍那一对) | **定理** |
| `noNi0`, `riseLe`, **`invNi⁺⁺`** | StrRel19Up | 含节点的树不低于第 $0$ 层的树; 上升 ⇒ 目标层在坐标层之下; 右边坐标层 $0$ 的节点、左边含节点的链极限 ⇒ `RkLeft` | 定理 |
| `posNi`, `pos?`, `posOutL` | StrRel19Up | `Act` 在第 $\ge1$ 层目标上把 `n1` 变成含节点的输出; `OutL` 的 `Pos0` 证明 (有限搜索在类型检查时算出) | 定理 |
| **`obsUpTT`** | StrRel19Up | `UpSoundZ ⇒ RkLeft tt StepT₁` | **定理 (约化)** |
| **`obsRkTT`** | StrRel19Up | `RkSoundZ hz (hs hz) ⇒ RkLeft tt LeftT₁` | **定理 (约化)** |
| **`valZ`**, **`valZV`** | StrRel19Val | kZ 形的时间条件 (`DomZ⁰`, 旧关系) ⇒ `xL` 那一对在 $(\tau_0,\tau_0)$ 上的再折叠 `RelX⁺ hz hz` 相关, 和 $\le$ | **定理 (值)** |
| `domZC`, **`¬domLC`**, **`exCv`** | StrRel19Val | $Y_C=$ `cv self` $Y_B$: kZ 成立, `J²⁺ Y_B Y_C` 不成立; 以 $Y_B$ 产生、$Y_C$ 再折叠, 和 $\le$ | 定理 (值); `¬domLC` 是前提范围的否定 |

## 前提实例

- `Sites`: `ActS` 的前提由 `sAct` 满足. `actNoZ₂`: `sAct`, `sIg↾`.
- `obs⁺⁺`: `sAct`, `refl`, `refl`, `StrRel16Val.valLK⁺` (经 `emb00`).
- `obsUpTT` 给 `UpSoundZ` 的参数: 节点 `r₀`, 分支 `n1`, `Act`, `n0`, $Y_1$, $(\tau_0, T_1)$, `ss hself`, `sAct`, `refl`, `refl`; 前提 `SemS hz hz … n1 OutL` 是 `semS00 oneL⁺⁺` (`domZmono`); 再折叠 `cp00`, `hawsAct`, `n0⁺⁺`, `hY₁⁺⁺`, `domZY₁`, 目标对 `(cp00 , s∞)`. 都是定理.
- `obsRkTT`: `StrRel18Obs.preY₁` (`RkPre`), `(cp00 , u∞ s∞)`, `refl`, `refl`, `sAct`, `sAct`, 再折叠同上.
- `valZ`: 实例 `exCv` 的前提 `hYC` (`lawcv⁺`), `domZC`; 都是定理.
- `UpSoundZ`, `RkSoundZ`, `OblRRZ`, `Emb⁺⁺` 本身: 没有实例, 也没有证明.

## 1 决定性实验 (`StrRel19Act`)

`HtFeedFold` §3 的 `Run` 在每个子句里把动作原样传下; 新的动作只在六处造出: `Ai` (分支以 `Ig↾ p A₀` 运行), `BNi` (输入以 `Ig↾ p (Ai …)` 运行), `RKi` 的 rise 句与 `Chn` (链以 `Ai …` 运行), `Kp` (`Ig↾ wu A₀`), `Kb` (`Ig↾ (⊲-tr wu p) A₀`), `κΔ` (`Ig↾ (wv c) A₀`). 闭项以 `Act` 起. 所以闭项里运行的每个动作都由 `sAct`, `sIg↾`, `sAi` 定义性地给出 (`Sites` 的类型逐字写出这六个项与起点; "只有这六处" 是读定义文本的判断).

`¬ActS-Az`: $\Lambda_2$ 上, 第 $2$ 层没有坐标层为 $2$ 的节点, 所以第 $2$ 层的 `ActS` 只由 `sAct` 与 `sIg↾` 生成, 都不读累计; `Az` 读累计. 对照: 在 $\Lambda_\kappa$ 上, `ActS` 里有读累计的动作 (`act-AiK`; `StrRel18Az.¬noZ-AiK`), 所以 `ActS` 排除的是 "外来的" 读累计动作, 不是一切读累计 (否定一路 `NegSR19Act` 有同一结论的否定形式).

## 2 `up` 解决了 $(\tau_0,T_1)$, 卡在 $(T_1,T_1)$ (`StrRel19Up`)

`obs⁺⁺`: 障碍那一对的左边 `ReL` 已低于同一节点 `O` 在 $\tau_0$ 上的上升输出 (`valLK⁺`), `up` 把它搬到 $T_1$ 上的保留输出 `ReR`.

再折叠目标对 $(T_1,T_1)$: `UpSoundZ` 的结论 (以 $x=$ `n1`, 节点 `xL` 为例) 要 `RelX⁺⁺ 1 1 StepT₁ RightT₁`, 左边 $\omega\cdot(\Omega_1⨾\ldots)$ 是链极限, 含 $\Omega_1$ 的节点; 右边是 `xL` 的保留节点 (坐标层 $0$) 在 $T_1$ 上再次保留. `invNi⁺⁺` 对推导求逆: `n0⁺⁺`, `ni⁺⁺` 形状不符; `in⁺⁺` 递归; `up` 要左边低于同一节点在某个上升目标上的输出, `riseLe` 说那个目标的层在坐标层 $0$ 之下, 即第 $0$ 层, 而含节点的左边不低于任何第 $0$ 层的树 (`noNi0`); 只剩 `rk⁺⁺`, 即 `RkLeft` (左边字面地是某个节点的上升输出). `RkLeft tt StepT₁` 没有证, 也没有否定 (判断: 左边是常数序列 `nl (λ _ → …)`, 上升输出的第 $n$ 项是链的第 $n$ 项的运行; 要命题相等需要函数相等, 在不用 `Funext` 时看不出能证).

`obsRkTT` 是同一机制在 `rk⁺⁺` 的可靠性上: 左边 `OutL` 的再折叠在 $T_1$ 上含节点 (`posNi`, `posOutL`).

## 3 值的一侧 (`StrRel19Val`)

`StrRel17Time.valT` 的时间条件是 `J²⁺ Y Y₂′` (累计 $z_Y\le z_{Y_2'}$); 经 `cv` 的再折叠状态累计是 `n0`, 它不成立 (`¬domLC`, 同 `NegSR17Time.¬domCv`). kZ 形 (`DomZ⁰`: $z_Y\le$ $Y_2'$ 在 $\tau_0$ 上的读数) 在 `cv` 之后仍成立 (`domZC`), 而 `valT` 的四步只在右边内部节点处的状态 $S_0\oplus\mathrm{Step}\,S_0$ 上用累计, 那个累计以 $\omega\cdot(1⨾\text{读数}(S_0))$ 结尾, 读数又以 $Y_2'$ 的读数为左前缀, 所以 kZ 够用 (`valZ`). 实例 `exCv`: 以 $Y_B$ 产生, 以 `cv self` $Y_B$ 再折叠, 和 $\le$.

## 4 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `ActS` (三个构造子) | `HtFeedFold` §3 造动作的六处与 `HtFeedClosed` 的起点 (`Sites`) | 树逼出 (折叠的字面) |
| `RelX⁺⁺` 的右层改为指标 | `up` 的两个目标层不同 | 树逼出 (正性) |
| `up` | `RKi` 的 rise/keep 两句 (同一节点两个目标), `StrRel18Up.upX`; 前提 `ActS` 来自 `NegSR18Up.¬UpSoundR` | 树逼出 (折叠子句的形状; 否定逼出前提) |
| `DomZ`, `DomZ⁰` | `cv` 清累计、留读数 (`StrRel18` 的 `kZ`) | 树逼出 (状态的两个字段) |
| `HAWS`, `SemS`, `semS00` 等 | `StrRel16Sem`, `StrRel16Fin` 的搬运 | 验收脚手架 (新关系需要) |
| `invNi⁺⁺`, `noNi0`, `riseLe` | `RelX⁺⁺` 的构造子表, `rkT` 的定义 | 树逼出 (约化) |

**归类: 提供信息.** 没有新构造子进树或折叠, 没有 `Lab`, 没有记号. 一步定理与新用到的字段: `¬ActS-Az` 用到节点的坐标层与层的第一位置 (`noAi₂`); `invNi⁺⁺` 用到 `rkT` 的上升条件与节点的坐标层 (`riseLe`); `valZ` 用到状态的读数字段经 `cv` 保留. 缺陷是否变深 (判断): 关系的 "$\le$ 节点" 规则第二次逐字取自折叠的子句 (`rk⁺` 取 `RKi` 的 rise/keep, `up` 取同一节点两个目标), 每一条都只覆盖一类再折叠目标对; 这一轮编译出下一类 ($(T_1,T_1)$, 左层高于坐标层). 继续按子句加规则会加深这一形态; 建议下一步换成不按子句写的规则 (见接手清单第 1 项).

## 5 接手清单

1. **"$x\le$ 节点" 的统一规则** (第一个障碍 `obsUpTT`/`obsRkTT`): 例如分支规则 "$x\le u\,p\,l_c\,y$ (某条路径、某个输入) ⇒ $x\le$ `ni r u`". 判断 (未编译): 在 $(T_1,T_1)$ 上, `StepT₁` $=\omega\cdot(\Omega_1⨾\text{读数}(Y_1))$ 与 `RightT₁` 的分支 (`BNi` 的输出, 也以 $\omega\cdot(\Omega_1⨾\ldots)$ 起头) 逐项可比, 读数的比较由 `cv` 保留差分量给出. 它的可靠性要在上升的再折叠目标上用链的某一项支配给定的分支输入; 先做最便宜的实验: 在 `xL` 上写出 `RelX⁺⁺ 1 1 StepT₁ (RightT₁ 的一个分支)`.
2. **`Emb⁺⁺` 可能不成立** (判断, 未编译): `ni⁺⁺` 的分支前提里坐标关系负出现, `up` 让低层关系变大, 旧的 `ni⁺` 推导不一定能搬过来. 用到 `Emb⁺⁺` 的地方先只用第 $0$ 层的 `emb00`.
3. **`UpStep` (`StrRel18Up`) 在新关系里**: 要把 `StrRel16Node.Z00.rr00` 搬到 `SemS`; 第 $0$ 层两个关系相同 (`emb00`, `back00`), 所以值的部分只差节点处的那一步.
4. `valZ` 推广到一般的产生动作 (`ActS`) 与一般的节点: `Core` 的四步对 `Act` 之外的动作.
5. 一般的 $k\sqsubseteq k'$, $\Omega^{\mathsf H}$ 处的 `MonoStep`, $T_\Omega<T_{\Omega+1}$: 没有开始, 在第 1 项之后.

## 6 审计

- **冷编译** (2026-11-05 16:22): 删掉本组 6 个模块的 `.agdai` (逐个写模块名: `StrRel19If`, `StrRel19Act`, `StrRel19Sem`, `StrRel19Up`, `StrRel19Val`, `StrRel19`; 未动 `NegSR19*`), 从入口重编: 退出码 0, 约 26 秒, 峰值常驻约 4.9 GB (`-M8G`). 之后接口只加了一条文字补注, 以 `--html` 重编入口: 退出码 0. 代码块里 `postulate`, 洞, `TERMINATING`, `NON_TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext`, K 都是 0.
- **导入闭包** (`importclosure.py`, `--only` 同 `StrRel18`: `OCF.Free.Level`, `OCF.BTBO`, `OCF.Align.` 下的 `CumReadCF`, `TLRule`, `TLOpsW`, `SumOne`, `BrwMid`, `LayerTr`, `CvFold`, `CvHigh`, `CvLayer`, `NoCumLit`, `L1Val`, `DVal`, `HtGen`, `HtFeed`, `HtCross`, `KVal`, `KNest`, `MonoPort`, `StrRel`, `NegSR16`, `NegSR17`): 入口闭包 96 个模块 (本地 85, 库 11), 禁用表 0, `--only` 之外 0; `If`, `Act`, `Sem`, `Up`, `Val` 各自单跑 (69, 89, 75, 91, 80 个模块) 都是 0, 0; 不加 `--only` 时禁用表也是 0.
- **定义级切片** (`depslice.py`, `--html` 由本组入口在编译通过后生成; 正对照 `Om1HnAccept` 及其闭包的 html 从 `StrRel18` 那一轮的 scratch 目录拷来, 未重生成): `¬ActS-Az` 217 块, `actNoZ₂` 116, `siteBNi` 112, `act-AiK` 125, `semS00` 202, `obs⁺⁺` 326, `invNi⁺⁺` 220, `obsUpTT` 314, `obsRkTT` 283, `valZ` 314, `exCv` 324, `UpSoundZ` 156, `RkSoundZ` 155; 记号模块 0, 记号词 0. 正对照 `Om1HnAccept:label-term₀` 1188 块, 记号模块 92, 记号词 58. 切片看不见模块应用, 块数偏少; 记号无关由导入闭包保证.
- **行数** (代码, 去空行与注释): If 145, Act 74, Sem 164 (其中约 120 行是 `StrRel16Sem`/`StrRel16Fin` 的搬运), Up 143, Val 44, 入口 10; 合计 580. 全部手写; 几处用 Python 做了字面替换 (加 `using` 项, 删不可达子句, 改一行的参数), 是一次性编辑, 没有生成的部分.

## 0 模块

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel19 where

open import Data.Unit using (tt)
open import OCF.Align.StrRel13Val using (Λ₂)
import OCF.Align.StrRel19If
open import OCF.Align.StrRel19Act public using (module Sites; module Iκ; module I₂; module L2)
open import OCF.Align.StrRel19Sem Λ₂ tt public using (law⊕⁺⁺; ext⁺⁺; OkMono; domZR; domZmono; module Sem00; module FinΛ⁺⁺)
open import OCF.Align.StrRel19Up public using (emb00; back00; obs⁺⁺; HasNi; noNi0; riseLe; invNi⁺⁺; oneL⁺⁺; semN1; StepT₁; RightT₁; obsUpTT;
  posNi; pos?; posOutL; LeftT₁; relRk; obsRkTT)
open import OCF.Align.StrRel19Val public using (DomZ⁰; valZ; valZV; YC; hYC; domZC; ¬domLC; exCv)
```
