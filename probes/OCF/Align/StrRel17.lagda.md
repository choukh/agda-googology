# 结构关系, 第十七轮: 带时间关系的语义 (B1): 入口

> **判决: PARTIAL (构造一路).** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 不改树、折叠、合法性, 不改已有文件 (只新建 `StrRel17`, `StrRel17If`, `StrRel17Val`, `StrRel17Time`, `StrRel17Obs`, `StrRel17Kap`).
>
> **对纲领与目标意味着什么 (判断).** 全在第 4 层 (关系与语义), 不碰树. (1) 时间条件在它管得到的地方够用: `rk⁺` 的一对输出 (`xL` 的链极限对节点) 以**一切**产生状态产生, 以**一切**满足时间条件的状态再折叠, 在右边上升的再折叠目标上 `RelX⁺` 相关 (**`valT`**, **`valLater`**); 产生状态是闭项的 $Y_1$ 时连时间条件都不要 (**`valY₁`**, 决定性实验 **`valLKN`** 是它的特例). (2) 时间条件管不到的地方是本轮的第一个障碍: 右边在再折叠时**保留**的目标对上, 结论要 "链极限的再运行 $\le$ 节点", `RelX⁺` 里能给出 (`nl`/…, `ni`) 的只有字面的 `rk⁺`; 编译的约化 **`obsT`/`obsRkT`/`obsRk16`**: 不管条件是什么, `rk⁺` 的可靠性都推出 "链极限的再运行字面地是某个节点的上升输出" (`RkLeft ReL`). (3) "ni 对 nκ" 按 `NegSR16` 的建议修补 (接口 §4), 修补排除了两个已知反例的设定 (`¬hawᴺAz`, `¬lead1κ`), 并在本来要的那一对 ($\Omega_1$ 对 $\Omega_{\Lambda_\kappa}$, 动作 `Act`, 状态 `YN`) 上值成立 (**`nkpΩ`**). 关于闭项 ($T_\Omega<T_{\Omega+1}$ 或界) 本轮没有结果.
>
> 交付 (按 `AGENTS.md` "交付拆成闭项与值"). (a) 构造: 接口 `StrRel17If`; 时间关系的小引理 (`later-tr`, `posLater`, `ne-later`, `lf→in`, `in-tr`); 再折叠的状态前提 `domY₁`, `domN`; 约化 `invNi`, `obsT`. (b) 值: **`valLKN`**, **`valLaterV`** (第 $0$ 层的和, 一切满足时间条件的状态), **`nkpΩ`**. 关于闭项的值: 没有.

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `Later`, `Laterᵈ`, `Cond`, `SemT`, `Any`, `DomL`, `RkSoundT`, `Pos0`, `Lead1`, `ActNZ`, `HAWᴺ`, `SemXᴺ`, `NKp`, `NKpV` | StrRel17If | 接口 (只有类型), 定稿 2026-11-05 12:12 | 定义 |
| `jN`, **`domY₁`** | StrRel17Val | `J²⁺ YN YN`; 一切非空 $S_0$: `J²⁺ Y₁ (S₀ ⊕ Step S₀)` | 定理 |
| `¬laterY₁YN` | StrRel17Val | `YN` 不晚于 $Y_1$ (`¬ Later Y₁ YN`) | 否定 (定理) |
| **`valLKN⁺`**, **`valLKN`** | StrRel17Val | `valLK` 的那一对以 `YN` 再折叠: `RelX⁺ hz hz`; $\Sigma_0$ 左 $\le$ 右 | **定理 (值)** |
| `lf→in`, `in-tr`, `lp-tr`, `later-tr`, `later⊕`, `later-refl`, `ne-later`, `PosLater.posLater` | StrRel17Time | 左脊是分量; 分量与左前缀传递; `RunIn.pos` 走到的状态晚于起点 | 定理 |
| `Core.Re.valC` | StrRel17Time | 一切产生状态 $Y$, 一切 `J²⁺ Y₂ Y₂′`: 右边内部第一个节点处的状态支配 $Y$ ⇒ 再折叠相关 | 条件定理 (`hS`) |
| **`valT`** | StrRel17Time | `J²⁺ Y₂ Y₂′` 且 `J²⁺ Y Y₂′` (时间条件 `DomL`) ⇒ `RelX⁺ hz hz` 相关 | 定理 |
| **`valLater`**, **`valLaterV`** | StrRel17Time | `J²⁺ Y Y` 且 `Later Y Y₂′` ⇒ 相关; 第 $0$ 层的和 $\le$ | **定理 (值)** |
| **`valY₁`** | StrRel17Time | 产生状态 $Y_1$: 一切 `J²⁺ Y₂ Y₂′` ⇒ 相关, 不要时间条件 | 定理 |
| `YB`, `hYB`, **`exBig`** | StrRel17Time | $Y_B=Y_1\oplus\mathrm{Step}\,Y_1$ 与自己 `J²⁺` 相关; 以 $Y_B$ 产生并再折叠, 第 $0$ 层的和 $\le$ (`valLaterV` 的实例) | 定理 (值, 前提实例) |
| `RkLeft`, **`invNi`** | StrRel17Obs | `RelX⁺ hz L′ x (ni R u′)` ⇒ $x$ 是 `n0` 或字面的 `RKi … rise` | 定理 |
| **`obsT`**, **`obsRkT`**, **`obsRk16`** | StrRel17Obs | 任意在 $(Y_1,Y_1)$ 上成立的条件下的语义 ⇒ `RkLeft ReL`; `RkSoundT hz (hs hz)` ⇒ 同; `StrRel16If.RkSound₀ (hs hz)` ⇒ 同 | 定理 (约化) |
| `riseO`, `keepO`, `chkL`, `chkRise`, `chkKeep`, `Up`, `upFix` | StrRel17Obs | 障碍那一对是 `valLK` 那一对的保留版 (同一节点同一组参数, `refl`); 有 `Up` 封闭性的关系族含障碍那一对 | 定理 (`upFix` 以 `Up` 为前提) |
| `AllΛ.actNZ`, `AllΛ.lead1Ω` | StrRel17Kap | `Act` 属于 `ActNZ`; 一切 `Ωd L` 以 `n1` 开头 (一切 $\Lambda$) | 定理 |
| `¬azNZ`, **`¬hawᴺAz`**, `¬lead1κ` | StrRel17Kap | `Az` 不属于 `ActNZ`; `NegSR16Sem.¬semΩ` 的动作不满足 `HAWᴺ`; `xK` 不以 `n1` 开头 | 否定 (定理) |
| `≤drp`, `domN`, `viaL`, `viaR` | StrRel17Kap | `drp` 不减和; 换世界后读数不变的状态再经一个 `n1` 支配 $\mathrm{YN}\oplus\mathrm{Step}\,\mathrm{YN}$ | 定理 |
| **`nkpΩ`** | StrRel17Kap | $\Lambda_\kappa$: $\Sigma_\beta(\Omega_1\text{ 的运行})\le\Sigma_{\beta'}(\Omega_{\Lambda_\kappa}\text{ 的运行})$, `Act`, `n0`, `YN`, 一切 $\beta\le\beta'$ | **定理 (值)** |

## 前提实例

- `valLKN`, `valY₁`, `nkpΩ`, `obsT` 的内部前提全部填上 (`cp00`/`cpTop`, `stepOA²⁺`/`stepOA⁺`, `n0⁺`, `jN`/`jN⁺`, `hY₁⁺`, 目标对 `(cp00 , s∞)`/`(cpTop , s∞)`, `refl`).
- `valT` 的前提 `J²⁺ Y₂ Y₂′`, `J²⁺ Y Y₂′`: 实例 $Y=Y_2=Y_2'=Y_1$ (`hY₁⁺`). `valLater` 的前提 `J²⁺ Y Y`, `Later Y Y₂′`: 实例 $Y=Y_1$, $Y_2'=Y_1\oplus\Delta$ (`later⊕`). 产生状态更大的实例: $Y_B=Y_1\oplus\mathrm{Step}\,Y_1$ (`hYB`, `exBig`).
- `Core.Re.valC` 的前提 `hS`: 两个来源都写出了 (`valT`, `valY₁`).
- `obsT` 的条件 `Ok`: `DomL tt Y₁` 由 `hY₁⁺` 满足, `Any` 由 `tt` 满足 (`obsRkT`, `obsRk16`).
- `upFix` 的前提 `Up R`: **没有实例** (`RelX⁺` 本身没有这条规则); 它是下一轮的候选, 见 §3.
- `¬hawᴺAz` 没有前提.

## 1 决定性实验 (`StrRel17Val`)

`StrRel16Val` 的那一对输出 (产生状态 $Y_1$) 以更小的 `YN` 再折叠 (`YN` 不晚于 $Y_1$, `¬laterY₁YN`): **通过** (`valLKN`). 原因 (定理 `domY₁`): `valLK` 第 $2$ 步要的是 "产生时的状态 $Y_1$" 被 "右边再折叠时内部节点 $N$ 处的状态" 支配, 而后者在 $N$ 之前总经过 `Ωd 1` 开头的 `n1`, 形如 $S_0\oplus\mathrm{Step}\,S_0$, 它对一切非空的 $S_0$ 都支配 $Y_1$. 所以 $Y_1$ 太小, 这个实验**不判定**时间条件对一般的产生状态是否必需.

接手清单说 "过: 说明 `RkSound` 有望对一切状态成立". 本轮把实验推广后 (§2) 的结论是分开的: 产生状态是 $Y_1$ 时对一切再折叠状态成立 (`valY₁`); 一般的产生状态, 本轮只在时间条件下证明 (`valT`). (否定一路 `NegSR17Rk` 的文件头报告了不带时间条件的反例: 产生状态较大, 产生时的动作不读状态; 本路只读了文件头, 未复核.)

## 2 时间条件够用的地方 (`StrRel17Time`)

设定: `xL` 以任意产生状态 $Y$ 运行, 输出 `OutLY` (第 $0$ 层目标, 上升) 与 `OutRY` (第 $1$ 层目标, 保留); 左边以 $Y_2$, 右边以 $Y_2'$ 再折叠, 动作 `Act`, 上下文 `n0`, 目标对 $(\tau_0,\tau_0)$ (右边上升). 证明是 `valLK` 的四步, 推广的两处: (i) 右边链的第一项是 $Y_2'$ 的读数, 一般的状态只知道它的左脊上有 $\omega\cdot(1⨾y)$ (`NE`), 路径由 `lf→in` 与 `RunIn.runIn` 给出; (ii) 第 $2$ 步的状态前提 "内部节点处的状态 $S_0\oplus\mathrm{Step}\,S_0$ 支配 $Y$" 由时间条件 `DomL` (`J²⁺ Y Y₂′`) 经 `RunIn.posOK` 一类的延长 (`posLater`, `jPfx⁺`, `ext⁺`) 得到. 这一站新用到的字段: `RunIn.pos` 的状态 (只经 `⊕` 与 `Rpt` 延长, `posLater`), `NE` 的左脊路径 (`Lf`), `RKi` keep 句里分支 `BNi` 的字面 (`brR`, `chkR`).

## 3 第一个障碍: 右边保留的再折叠目标对 (`StrRel17Obs`)

`RkSoundT` (与 `StrRel16If.RkSound`) 要对一切 `TX` 再折叠目标对给结论. 在 `rkAt` 那一对上取 $(\tau_0,T_1)$: 右边的节点 (坐标层 $0$) 在第 $1$ 层目标上**再次保留**. 编译的结论:

- `invNi`: `RelX⁺ hz L′ x (ni …)` 只能由 `n0⁺`, `in⁺` (经 `here`) 或 `rk⁺` 得到.
- `obsT`: 任意在 $(Y_1,Y_1)$ 上成立的条件 (时间条件都是, 因为那时再折叠状态就是产生状态) 下的语义, 都推出 `RkLeft ReL`: "链极限以 $Y_1$ 再运行一次" 字面地 (命题相等) 是某个节点的 `RKi … rise`.

本轮没有证明 `RkLeft ReL` 不成立: `rk⁺` 的参数 (动作 $A_0$ 任意) 存在量化, 本文不对它求逆. **所以不否定 `RkSoundT`; 写 "未走通".** 编译给出的事实是: 时间条件只约束状态, 这里的困难在结论关系的形状上, 与状态无关.

**下一步的候选 (判断, 未试).** `upFix` 说: 障碍那一对 (`ReL`, `ReR`) 与 `valLK` 那一对 (`LaterL`, `LaterR`) 左边相同, 右边是**同一个节点, 同一组参数**在两个目标上的 `RKi` (`chkRise`, `chkKeep`, 都是 `refl`). 所以一条 "同一节点: $x\le$ 它在低目标上的上升输出 ⇒ $x\le$ 它在高目标上的保留输出" 的规则 (`Up`) 会把障碍那一对化成 `valLK`. 它的形状由 `RKi` 的两句给出 (树逼的), 比 `rk⁺` 一般 (`rk⁺` = 升升义务 + `Up`, 判断). 它的可靠性没有证: 要么要 `RelX⁺` 的传递性 (没有证, 也没有否定), 要么要同一节点上的 `RkSoundT` (又回到本障碍). 加它要新的关系, 按 "只增" 应另开接口.

**否定一路的文件头 (本路未复核).** `NegSR17Time.¬domFromLaterᵈ`: 经过 `cv` 的再折叠得不到 `DomL` (累计被清零); 这与接口 "范围 (i)" 一致. 本路的 `valT` 只用同一世界的 `Later`; 经 `cv` 的情形 (折叠里 `BNi`, `Kp`, `Kb`, `κc` 都先 `cv`) 时间条件要另给, 是第二个障碍.

## 4 "ni 对 nκ" 的修补 (`StrRel17Kap`)

- 修补的两项限制都排除了 `NegSR16` 的反例: `¬semNK` 的那一对 (`xN` 对 `xK`) 不是 `NKp` 结论的形状 (`¬lead1κ`: `nκ` 前没有以 `n1` 开头的一段); `¬semΩ` 的动作 `Az` 不满足 `HAWᴺ` (`¬hawᴺAz`).
- **`nkpΩ` (值, 一个实例):** $\Omega_1$ 对 $\Omega_{\Lambda_\kappa}$, `Act`, `n0`, `YN`, 第 $0$ 层目标. 机制 (依据证明): 开头的 `n1` 让累计非空 (`Step YN` 的第 $0$ 层读数), 回灌的第 $0$ 格的世界是一个极限 $v$; 第 $0$ 格运行坐标层 $1$ 的节点, 它上升时链的第一项是换世界后的状态在第 $1$ 层上的读数, 读数里的 $\Omega_1$ 含坐标层 $0$ 的节点 $N'$; 左边的 $N$ 由 `rr00` 落在 $N'$ 的上升输出之下. 状态前提 `domN` 只用到 "换世界后差分量不变" (`Laterᵈ`) 与 $N'$ 前面的 `n1`, 不用累计的时间关系.
- 没有做: `NKp`/`NKpV` 本身 (一切 $x$, 节点, 分支, 一切 `ActNZ` 动作与 `J²⁺` 状态). 第一个障碍 (判断): 一般的状态下回灌第 $0$ 格的世界 $v=\Sigma(\text{累计})$ 不是字面的, `Walk` 不化简, 需要一条对一般 $v$ 的 "第 $0$ 格里有分支的运行" 的引理.

## 5 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `Later`, `Laterᵈ` | `HtFeedFold` 的 `_⊕⟨_⟩_` (向右加一段), `cv` (换世界读同一个函数) | **树逼的** |
| `SemT`, `DomL` | `valLK` 第 2 步实际用到的状态关系 (产生时对再折叠内部) | 树逼的 (语义的量化) |
| `RkSoundT` | `StrRel16If.RkSound` 加条件 | 脚手架 (缺的引理的类型) |
| `Pos0`, `Lead1`, `ActNZ`, `HAWᴺ`, `SemXᴺ`, `NKp`, `NKpV` | `NegSR16` §5 的建议; `RKy` 的回灌读累计, `Ωd` 的开头 `n1` | 树逼的 (形状); 是否可靠未定 |
| `valT`, `valY₁` 的证明路线 | `RKi` rise 句 (链从状态在坐标层上的读数起), `BNi` 的字面 (`brR`), `NE` 的左脊 | 树逼的 |
| `RkLeft`, `invNi`, `obsT` | `RelX⁺` 的构造子表; `RunNi`/`RKi` 的两句 | 树逼的 (约化) |
| `Up` (候选, 未进接口) | `RKi` 的两句: 同一节点在低目标上升、高目标保留 | 树逼的 (形状); 可靠性未定 |
| `nkpΩ` 的证明路线 | `RunK`/`RKy`/`κc`/`Walk` 的字面 (第 $0$ 格的世界, `Walk` 的 `asuc`/`alim` 两句), `drp` | 树逼的 |

**归类: 提供信息.** 没有新构造子进树或折叠, 没有 `Lab`, 没有记号. `valT` 是对产生状态与再折叠状态 (一切) 的一步定理, 新用到的字段见 §2; `invNi`/`obsT` 用编译的约化划出时间条件管不到的地方; 修补的两项限制各有一条编译的排除 (`¬hawᴺAz`, `¬lead1κ`). 缺陷是否变深 (判断): 接口新加的类型都是语义的量化或谓词, 不加深翻译; `RkSoundT` 仍以字面的 `rk⁺` 为对象, 它的形状读自折叠的两句 (同 `StrRel16`), 本轮的约化说明这一字面形本身是障碍.

## 6 接手清单

1. **`Up` (同一节点, 低目标上升 ⇒ 高目标保留) 的可靠性的定义域** (最便宜的下一步): 先写最小的否定实验: 在 `rkAt` 的参数上, 对 `Up` 结论的那一对 (`ReL`, `ReR`) 再折叠一次, 在 $(\tau_0,\tau_0)$ 与 $(\tau_0,T_1)$ 上比. 过: 新接口 (只增) 加一条 `Up` 规则 (新关系), 证 `rk⁺` 可由升升义务与 `Up` 得到; 不过: 写成否定.
2. `RelX⁺ hz hz` 的传递性 (第 $0$ 层): `Up` 的可靠性的一个来源. 先试有限的情形 (`n0`, `n1`, `⨾`, `nl`, `pr`, `in`), 注意 `in⁺` 与 `nl⁺` 交错的情形.
3. 经 `cv` 的时间条件 (第二个障碍, 否定一路 `NegSR17Time`): `DomL` 的累计分量在 `cv` 后不成立. 候选: 只要差分量与 `NE` 的条件 (累计只在 `nκ` 处用); 要看 `StrRel16Node.Zero²` 的证明是否只用差分量 (判断: 有限 $\Lambda$ 上是).
4. `NKpV` 对一般状态: 一条对一般世界 $v$ 的 "回灌第 $0$ 格里有分支的运行" 的引理 (`Walk` 的第一个 `asuc` 位置).
5. 一般的 $k\sqsubseteq k'$, $\Omega^{\mathsf H}$ 处的 `MonoStep`, $T_\Omega<T_{\Omega+1}$: 没有开始, 都在第 1, 3 项之后.

## 7 审计

- 冷编译 (2026-11-05 12:39): 删掉本组 5 个模块的 `.agdai` (逐个写模块名: `StrRel17If`, `StrRel17Val`, `StrRel17Time`, `StrRel17Obs`, `StrRel17Kap`; 入口原本没有), 从入口重编: 退出码 0, 约 28 秒, 峰值常驻约 3.7 GB (`-M8G`). 代码块里 `postulate`, 洞, `TERMINATING`, `NON_TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext`, K 都是 0.
- 工程记录: `StrRel17Obs.obsT` 起初写成 `with invNi (…)`, 8G 堆耗尽 (退出码 251); 改成普通辅助函数 `pick` 后约 0.7 GB (`EBOHandbook` 4.2 第 5 条的又一例).
- 导入闭包 (`importclosure.py`, `--only` 同 `StrRel15`, 另加 `OCF.Align.NegSR16` (`StrRel17Kap` 导入 `NegSR16Kap`, `NegSR16Sem`)): 入口闭包 87 个模块 (本地 77, 库 10), 禁用表 0, `--only` 之外 0; `If`, `Val`, `Time`, `Obs`, `Kap` 各自单跑 (68, 78, 79, 80, 78 个模块), 也都是禁用表 0, `--only` 之外 0.
- 定义级切片 (`depslice.py`, `--html` 由本组入口生成; 正对照的 `Om1HnAccept` 及其闭包的 html 从 `StrRel16` 那一轮的 scratch 目录拷来, 未重生成): `valLKN` 300 块, `valT` 307, `valLaterV` 309, `valY₁` 315, `obsRkT` 239, `invNi` 185, `upFix` 297, `nkpΩ` 235, `¬hawᴺAz` 162, `RkSoundT` 145, `NKp` 147; 记号模块 0, 记号词 0. 正对照 `Om1HnAccept:label-term₀` 1188 块, 记号模块 92, 记号词 58. 切片看不见模块应用, 块数偏少; 记号无关由导入闭包保证.
- 行数 (代码, 去空行与注释): If 82, Val 59, Time 129, Obs 79, Kap 101, 入口 8; 合计 459. 全部手写, 没有生成或文本替换得到的部分 (所以 `probes/Survey/scripts/strrel17/` 没有脚本).

## 0 模块

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel17 where

open import Data.Unit using (tt)
import OCF.Align.StrRel17If
open import OCF.Align.StrRel17Val public using (YN; jN; domY₁; ¬laterY₁YN; LaterLN; LaterRN; valLKN⁺; valLKN)
open import OCF.Align.StrRel17Time public using (lf→in; in-tr; later-tr; ne-later; module PosLater; module Core; valT; valLater; valLaterV; valY₁; YB; hYB; exBig)
open import OCF.Align.StrRel17Obs public using (ReL; ReR; RkLeft; invNi; obsT; obsRkT; obsRk16; riseO; keepO; Up; upFix)
open import OCF.Align.StrRel17Kap public using (module AllΛ; ¬azNZ; ¬hawᴺAz; ¬lead1κ; domN; nkpΩ)
```
