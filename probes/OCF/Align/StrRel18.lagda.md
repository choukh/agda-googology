# 结构关系, 第十八轮: 修补 (a)(c) (构造一路): 入口

> **判决: PARTIAL, 按简报停下交回.** (a) 在 $\Omega$-极限处为空 (定理: 折叠自己产生的保留节点的分支动作读累计). (c) 未走通: 三个变体里 `kZ` 同时含闭项的那一对、排除已知反例 (定理), 但 (a) 与 (c) 的每个变体都推出第一个障碍 `RkLeft tt ReL` (约化定理), 所以单靠 (a)(c) 证不出 `RkSoundT` 的修补版. 第一个障碍要 `Up`, 而 `Up` 只能是新关系 (约化定理); `Up` 的最小实验只做了前一半, 后一半卡在 `StrRel16If` 已写明的严格正性缺口 (`rk⁺` 的前提是旧关系). 顺带: 第 $0$ 层的 `RelX⁺` 是传递的 (定理, `StrRel17` 接手清单第 2 项). 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 不改树、折叠、合法性, 不改已有文件 (只新建 `StrRel18`, `StrRel18If`, `StrRel18Az`, `StrRel18Obs`, `StrRel18KZ`, `StrRel18Up`, `StrRel18Tr`).
>
> **对纲领与目标意味着什么 (判断).** 全在第 4 层 (关系与语义), 不碰树. (1) 修补 (a) "动作不读第 $0$ 层累计" 在有 $\Omega$-极限的 $\Lambda$ 上不被折叠满足: 闭项的第一步 $\Omega_{\Lambda_\kappa}$ 在第 $\Lambda_\kappa$ 层目标上产生的保留节点, 分支以 $\omega\cdot(\Omega_{\Lambda_\kappa}⨾\ldots)$ 起头, 含 `nκ`, 它在第 $0$ 层目标上回灌时从累计起走 (**`¬noZ-fold`**). 主线的终点在 $\Omega$-极限之上, 所以 (a) 不是可用的修补. (2) 修补 (c) 的有用形状是 "左边产生时的累计 $\le$ 右边保留分支运行时的状态在第 $0$ 层的读数" (`kZ`): `cv` 清掉累计但保留读数, `kZ` 要求清掉的东西已在读数里. 它含闭项的那一对 (**`domKZ₁`**), 排除 `NegSR17RkT` 的反例 (**`¬domKZ-P`**); 只比读数的 `kD` 留下反例 (**`¬RkSoundTKD`**), 比整个状态的 `kJ` 连闭项的那一对也排除 (**`¬domKJ`**). (3) (a)(c) 都只约束动作或状态; 第一个障碍在结论关系的形状上 (**`obsZ`**, **`obsKD`**, **`obsKZ`**). 它要 `Up`; `Up` 不能是 `RelX⁺` 已有的封闭性 (**`upX`**). (4) 关于闭项的值 ($T_\Omega<T_{\Omega+1}$ 或界): 没有.
>
> 交付 (按 `AGENTS.md` "交付拆成闭项与值"). (a) 构造: 接口 `StrRel18If`; `trans00⁺` (第 $0$ 层传递性), `canc` (加法左消去), `admH`, `alH` (对齐的横向复合); `chkKSt`; `domKZ₁`, `domKD₁`; `upHalf`. (b) 值: `upHalfV` (最小实验的前一半, 第 $0$ 层的和); 否定的值: `¬RkSoundTKD`, `¬domKZ-P`, `¬domKJ`. 关于闭项的值: 没有.

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `NoZ`, `AiNoZ`, `HAWᶻ`, `SemTᶻ`, `RkSoundTᶻ`, `KSt`, `KV`, `DomKv`, `RkSoundTK`, `RelT`, `UpClosed`, `OAR`, `SemR`, `UpSound`, `Trans00` | StrRel18If | 接口 (只有类型), 定稿 2026-11-05 14:22 | 定义 |
| `noZ-Act`, `noZ-Air` | StrRel18Az | `Act` 满足 `NoZ`; $\Omega_{\Lambda_\kappa}$ 的节点 (分支 `n1`) 的分支动作满足 `NoZ` | 定理 |
| `kindK`, `chkK`, `brK-shape` | StrRel18Az | 那个节点在第 $\Lambda_\kappa$ 层目标上保留; 保留输出 `K Y w = ni r (brK Y w)`; 分支是 $\omega\cdot(\Omega_{\Lambda_\kappa}⨾\ldots)$ (`refl`) | 定理 |
| `inFold`, `cellK` | StrRel18Az | 闭项第一步 (`Ωd Λκ`, `Act`, $Y_0$, `n0`) 在 `TΛ` 上的输出是 `a ⨾ (b ⨾ nκ tt fκ)`; `fκ self tt` 字面是某个 `K Y w` | 定理 |
| **`¬noZ-AiK`**, **`¬AiNoZ`**, **`¬noZ-fold`** | StrRel18Az | 一切产生状态与上下文: 保留节点的分支动作 (以 `Act` 运行) 不满足 `NoZ`; 律 `AiNoZ` 不成立; 闭项里的那个节点也是 | **否定 (定理)** |
| `Gen.chkKSt` | StrRel18Obs | `BNi … ≡ Ai … (KSt …)`, 一切 $\Lambda$ | 定理 |
| **`obsZ`** | StrRel18Obs | `RkSoundTᶻ hz (hs hz)` ⇒ `RkLeft tt ReL` | 定理 (约化) |
| **`¬domKJ`** | StrRel18Obs | `kJ` 在 `rkAt` 那一对 (产生状态 $Y_1$) 上不成立 | 否定 (定理) |
| `domKD₁`, `domKZ₁`, **`obsKD`**, **`obsKZ`**, `obsK` | StrRel18Obs | `kD`, `kZ` 在 `rkAt` 那一对上成立; `RkSoundTK kD`/`kZ` ⇒ `RkLeft tt ReL` | 定理 (约化) |
| `domKD-P`, **`¬RkSoundTKD`** | StrRel18Obs | `NegSR17RkT` 的反例满足 `kD`; `RkSoundTK kD hz (hs hz)` 不成立 | **否定 (定理, 值)** |
| `go`, `liftω`, `ω≤R`, **`¬domKZ-P`** | StrRel18KZ | 右边的再折叠输出 $\ge\omega$; `NegSR17RkT` 的反例不满足 `kZ` | 否定 (定理, 值) |
| **`upX`** | StrRel18Up | `UpClosed RelX⁺` ⇒ `RkLeft tt ReL` | 定理 (约化) |
| `upHalf`, **`upHalfV`** | StrRel18Up | 最小实验的前一半: `ReL` 的再折叠 $\le$ `riseO` 的再折叠 (`RelX⁺ hz hz`, 第 $0$ 层的和) | **定理 (值)** |
| `UpStep`, `upExp` | StrRel18Up | 缺的一半 (`riseO` 的再折叠 $\le$ `ReR` 的再折叠) ⇒ 实验的值 | 条件定理 (`UpStep`) |
| `comp`, `Tr.tr`, `trans00`, `invNw`, `trans→APH₀` | StrRel18Up | 分量的推导; `APH ⇒ Trans00`; `Trans00 ⇒ APH₀` | 定理 / 条件定理 (`APH`) |
| `canc`, `admH`, `alH`, `aph`, **`trans00⁺`** | StrRel18Tr | 加法左消去; `Adm`, `Al` 的横向复合; `APH`; **`Trans00`** | 定理 |

## 前提实例

- `¬AiNoZ` 的前提 `NoZ Act` 由 `noZ-Act` 给出; `¬noZ-AiK` 对一切产生状态 $Y$ 与上下文 $w$; `¬noZ-fold` 的节点由 `cellK` 从闭项取出.
- `obsZ`, `obsK`: `preY₁` (`RkPre`, 旧关系), `noZΛ₂`, `domKD₁`/`domKZ₁`, `(cp00 , u∞ s∞)`, `refl`, 再折叠一侧 `hawAct²⁺`, `n0⁺`, `hY₁⁺`, 目标对 `(cp00 , u∞ s∞)`.
- `¬RkSoundTKD`: `NegSR17RkT.preP`, `jYP`, `domKD-P`, `NegSR17Rk.hawC1⁺`; 都是定理.
- `upExp` 的前提 `UpStep`: **没有实例** (缺的引理). `trans00` 的前提 `APH`: 由 `StrRel18Tr.aph` 满足.
- `UpClosed`, `UpSound`, `RkSoundTᶻ`, `RkSoundTK` 本身: 没有实例 (`RkSoundTK kD` 是否定的).

## 1 决定性实验: (a) 在 $\Omega$-极限处为空 (`StrRel18Az`)

$\Lambda_\kappa=\mathrm{h\Omega}\,(\lambda\_\to1)$. $\Omega_{\Lambda_\kappa}=1⨾\mathrm{n\kappa}(c\mapsto\mathrm{ni}_c)$, 节点 $\mathrm{ni}_c$ 层 $\Lambda_\kappa$, 坐标层 $1$, 分支 `n1`. 闭项第一步在第 $\Lambda_\kappa$ 层目标上运行 `nκ` 时 (`Kb`), 在坐标 $0$ 上运行这个节点, 坐标层 $1\lhd\Lambda_\kappa$, 节点**保留**. 保留输出的分支是 `BNi` 的输出, 分支 `n1` 在 `Act` 下给 `Step`, 在第 $\Lambda_\kappa$ 层上就是 $\omega\cdot(\Omega_{\Lambda_\kappa}⨾\ldots)$, 含 `nκ`. 这个保留节点日后再折叠时, 链的动作是它的分支动作 `Ai`, 即以再折叠动作运行这棵含 `nκ` 的树; 在第 $0$ 层目标上 `nκ` 回灌, 第 $0$ 格的世界是 $W+\text{累计}$, 所以输出读累计 (`¬noZ-AiK`; 观察 `obs` 取第 $0$ 格里 `Walk` 的那一段: 累计 `n0` 时是 `n0`, `n1` 时是 `n0 ⨾ …`).

结论: (a) 的律 `AiNoZ` 不成立, 反例是闭项自己的节点 (`¬noZ-fold`). 原来的节点 (分支 `n1`) 的分支动作满足 `NoZ` (`noZ-Air`): 读累计的是**保留之后**的节点, 因为保留把 "目标层的 `Step`" 放进了分支, 目标层是 $\Omega$-极限时其中有 `nκ`. 与 `NegSR17` §5 的判断一致, 现在是定理. 只在分支不含 `nκ` 的折叠 (没有 $\Omega$-极限) 上 (a) 才可能成立, 那一半没有证.

## 2 (c) 的三个变体 (`StrRel18Obs`, `StrRel18KZ`)

`KSt`: 保留输出的分支收到输入后, 分支的树运行时的状态 (`BNi` 的字面, `chkKSt`): `cv p Y ⊕ Run (输入)`; 累计是 `n0 ⨾ …` (`cv` 清零), 差分量是 $Y$ 的差分量搬过来再接上.

| 变体 | 比什么 | `rkAt` 那一对 (闭项, $Y_1$) | `NegSR17RkT` 的反例 (`Az`, `YP`) | `RkSoundTK` |
|---|---|---|---|---|
| `kJ` | `J²⁺ Y (KSt)` | 不满足 (`¬domKJ`) | (未看) | 管不到闭项那一对 |
| `kD` | 差分量 `OA²⁺` 加 `NE` | 满足 (`domKD₁`) | 满足 (`domKD-P`) | **不成立** (`¬RkSoundTKD`); 且 ⇒ `RkLeft` (`obsKD`) |
| `kZ` | `z Y ≤ KSt 在第 0 层的读数` | 满足 (`domKZ₁`) | **不满足** (`¬domKZ-P`) | ⇒ `RkLeft tt ReL` (`obsKZ`); 是否成立未定 |

`kZ` 的机制 (判断, 依据证明): 反例里左边的值来自产生时的累计 $z_P$ (比右边的再折叠输出多 $1$), 右边的保留分支在 `cv` 之后运行, 读数只有 $\omega$ (差分量 `dN` 被保留); `kZ` 要求 $z_P\le\omega$, 而 `ω≤R` 说右边的输出 $\ge\omega$, 所以 $z_P>\omega$. 闭项的 $Y_1$ 的累计与它在第 $0$ 层的读数是同一棵树 ($0⨾\omega\cdot(1⨾0)$), `kZ` 由 `pr⁺` 直接给出.

## 3 (a)(c) 碰不到第一个障碍; `Up` 只能是新关系 (`StrRel18Obs`, `StrRel18Up`)

`StrRel17Obs.obsT` 的约化对任何在 $(Y_1,Y_1)$ 上成立的再折叠条件都成立; 本轮把它推到产生一侧的前提: `Act` 是 `NoZ` (所以 `obsZ`), `rkAt` 那一对满足 `kD`, `kZ` (所以 `obsKD`, `obsKZ`). 于是 `RkSoundTᶻ`, `RkSoundTK kD`, `RkSoundTK kZ` 都推出 `RkLeft tt ReL` ("链极限的再运行字面地是某个节点的上升输出"). 本轮仍没有否定 `RkLeft tt ReL` (`rk⁺` 的参数存在量化).

**经 `cv` 的再折叠 (判断, 回应否定一路的问题).** 本路没有走通 `RkSoundTᶻ` 或 `RkSoundTK kZ`, 所以没有 "如何避开 `cv` 之后的再折叠" 的构造. 字面上: `kZ` 是**产生一侧**的前提, 结论仍是 `SemT … (DomL lW Y)`, 即只对满足 `DomL` 的再折叠要求结论; 经 `cv` 的再折叠 `DomL` 不成立 (`NegSR17Time.¬domCv`, 产生时累计非 `n0` 时), 所以 `RkSoundTK kZ` 对这些再折叠**什么也不说** (空真), 不是避开而是不覆盖. 折叠里 `BNi`, `Kp`, `Kb`, `κc` 都先 `cv`, 这一块仍是 `StrRel17` 的第二个障碍. 判断: `kZ` 的形状 ("清掉的累计已在读数里") 提示把 `DomL` 的累计分量换成 "左边产生时的累计 $\le$ 右边再折叠状态的第 $0$ 层读数" (读数经 `cv` 保留); 这没有写进接口, 也没有试.

`upX`: 若 `RelX⁺` 自己对 `Up` 封闭, 也推出 `RkLeft tt ReL`. 所以 `Up` 要作为新关系的构造子加进去 (`Up` 的前提是同一关系在同一层对上, 正出现, 不撞严格正性), 语义要换成以新关系为输出的 `SemR`, 并证 `UpSound`.

## 4 `Up` 的最小实验与第一个障碍 (`StrRel18Up`)

实验: 把障碍那一对 $(\mathrm{ReL},\mathrm{ReR})$ 以 `Act`, `n0`, $Y_1$ 再折叠一次, 在 $(\tau_0,\tau_0)$ 上比. `ReR = keepO`, 它在 $\tau_0$ 上上升. 拆成两段: (i) `ReL ≤ riseO` 的再折叠 (**`upHalf`**, 由 `valLK⁺` 与 `semX00⁺`); (ii) `riseO` 的再折叠 $\le$ `keepO` 的再折叠 (`UpStep`), 两段由 `≤-trans` (或 `trans00⁺`) 接起来 (`upExp`).

**第一个障碍 (判断, 依据折叠的字面, 未编译).** (ii) 是 `StrRel17Time.valT` 的形状, 节点从 `xL` (分支 `n1`) 换成 `O` (`riseO` 与 `keepO` 的节点, 层 $1$, 坐标层 $0$, 分支 `CY.brR` = $\omega\cdot(\Omega_1⨾\ldots)$). `valT` 的第 2 步用 `Z00.rr00` 比较两个坐标层 $0$ 的节点的链极限, 要两个分支动作满足 `HAW²⁺ hz hz`. `keepO` 的链里能支配 `O` 的链极限的是保留后的 $N$ (记作 $N'$; 未保留的 $N$ 的分支动作是 `Step`, 比 `O` 的小); `O` 与 $N'$ 的分支动作都是 "以 `Act` 运行 $\omega\cdot(\Omega_1⨾\text{读数})$", 它们的 `HAW²⁺` 在目标对 $(\tau_0,T_1)$ 上要 "$N$ 的链极限 $\le$ 保留的 $N$", 只能由 `rk⁺` 给出, 而 `rk⁺` 的前提是旧关系 (`RkPre`), `HAW²⁺` 只提供新关系的输入. 这是 `StrRel16If` 文件头 "严格正性" 一段写明的缺口, 不是 (a)(c) 的问题.

## 5 第 $0$ 层的传递性 (`StrRel18Up`, `StrRel18Tr`)

`Tr.tr` 对两段推导的字典序归纳: `pr⁺`, `in⁺` 在左边时用分量引理 `comp` 把右边的推导移到分量上; 在右边时直接下降; `n0`, `n1`, `⨾`, `nl` 逐项; 第 $0$ 层没有 `ni⁺`, `κ⁺`, `nκ⁺`, `rk⁺` (`StH _ _ hz` 与 `NZ hz` 是空的). 只剩 `nw⁺` 对 `nw⁺`: 要对齐路径对横向复合 (`APH`), 中间世界的 `Lg` 证明只命题相等, 所以 `tr` 带一条等式. `trans→APH₀` 说这一步不可省. `APH` 由 `StrRel18Tr.aph` 证明: `Al` 的横向复合对两个推导归纳 (中间路径的形状排除不匹配的情形), `Adm` 的横向复合要两个领先量 $\delta_1\le\delta_2$, 由加法左消去 `canc` 从 $V_0'\oplus\delta_1\le V'\le V_0'\oplus\delta_2$ 得到.

## 6 若 (a)(c) 都不行: (b) 要改折叠的哪一处, 理由是否来自树侧

- **哪一处.** `HtFeedFold` 的 `BNi`: 它给保留分支的状态是 `cv p Y ⊕⟨ lW′ ⟩ …`, `cv` 把累计置为 `n0` (`HtFeedFold.cv` 的字面). (b) 要把它换成带上累计的状态 (例如差分量照旧搬运, 累计用 `drp (z Y)` 搬到新世界). `Kp`, `Kb`, `κc` 也经 `cv`, 是否一起改要另看.
- **理由是否来自树侧 (判断).** 现有的编译否定 (`NegSR17RkT.¬RkSoundT`, 本轮的 `¬AiNoZ`, `¬RkSoundTKD`) 都是**验收关系 (语义) 的可靠性**的否定, 不是折叠的合法性、壁垒、或闭项的序数值的否定; 没有一条指向折叠定义本身的缺陷. 按 `AGENTS.md` "第 4 层不反过来改前 3 层", 这样的理由只是验收方便, 不够. 另外: `kZ` 不改折叠就排除了已知的反例 (`¬domKZ-P`), 所以 (b) 不是被已知反例逼出的; 第一个障碍在结论关系的形状上, (b) 也碰不到它 (判断: 改 `BNi` 的状态不改 `RelX⁺` 里 "… ≤ 节点" 只有 `rk⁺` 这一点). 而且在 $\Omega$-极限处, 保留分支里的 `nκ` 读累计 (`¬noZ-fold`), 带上累计会让回灌多走, 改变闭项的值 (判断, 未编译).
- **所以本路不推荐 (b);** 是否改交作者.

## 7 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `NoZ`, `AiNoZ`, `HAWᶻ`, `SemTᶻ`, `RkSoundTᶻ` | `NegSR17` §5 的 (a); `HtFeedFold` 的 `St` (差分量与累计两个字段) | 树逼的 (状态的字段) |
| `KSt` | `HtFeedFold.BNi` 的字面 (`chkKSt`) | 树逼的 |
| `kJ`, `kD`, `kZ` | `J²⁺`, `OA²⁺` 的分量; `cv` 清累计、留差分量 | 树逼的 (三种比较对应状态的两个字段) |
| `UpClosed`, `OAR`, `SemR`, `UpSound` | `RKi` 的 rise/keep 两句 (同一节点, 两个目标) | 树逼的 (形状); 可靠性未定 |
| `Trans00` 的证明 (`comp`, `canc`, `admH`, `alH`) | `RelX⁺` 的构造子表, `StrRel4Walk.Al` 的构造子, `Adm` 的定义 | 树逼的 |
| `¬noZ-AiK` 的观察 | `RKi` keep 句, `BNi`, `Step`, `Ωd` 的 $\Omega$-极限句, `κc` 的第 $0$ 格, `Walk` | 树逼的 (否定) |

**归类: 提供信息.** 没有新构造子进树或折叠, 没有 `Lab`, 没有记号. 一步定理与新用到的字段: `¬noZ-AiK` 用到 `RKi` keep 句把目标层的 `Step` 放进分支, 与 `κc` 第 $0$ 格的世界 $W+z$; `¬domKZ-P` 用到 `cv` 保留差分量; `trans00⁺` 用到 `Al` 的五个构造子与 `Adm` 的领先量. 否定划出: 不能要求 "保留节点的分支动作不读累计" (`¬AiNoZ`), 不能只比差分量 (`¬RkSoundTKD`), 不能比整个状态 (`¬domKJ`). 缺陷是否变深 (判断): 接口新加的都是谓词与量化, `Up` 尚未成为构造子; 第一个障碍仍以字面的 `rk⁺` 为对象.

## 8 接手清单

1. **`Up` 作为新关系** (最便宜的下一步): `RelX⁺` 加一条构造子 (`UpClosed` 的形状, 正出现), 以它为输出关系的 `SemR`; 先证 `UpSound` 在 $(\tau_0,\tau_0)$ 上的值, 即 `UpStep` (本文 §4).
2. **`rk⁺` 的前提的严格正性缺口** (`UpStep` 的第一个障碍): 判断: 把动作前提 `HAW` (负出现) 换成正的证书, 例如只对折叠实际用到的动作 (由 `Act`, `Ig↾`, `Ai` 生成) 写一个语法 (深嵌入), 让 `rk⁺` 的前提能用新关系写. 最便宜的实验: 闭项里出现的动作是否都定义性地是这三种之一.
3. **`kZ` 下的上升-上升再折叠目标对** (`valT` 对一般节点): `Core` 的四步对一般的分支动作; `kZ` 的作用是比左边链里的累计与右边 `KSt` 的读数.
4. **$\Omega$-极限处的 `kZ`**: 闭项在 $\Lambda_\kappa$ 上的状态是否满足 `kZ` (本轮只在 $\Lambda_2$ 上); 否定一路可能已有结果.
5. 一般的 $k\sqsubseteq k'$, $\Omega^{\mathsf H}$ 处的 `MonoStep`, $T_\Omega<T_{\Omega+1}$: 没有开始, 在第 1–3 项之后.

## 9 审计

- **冷编译** (2026-11-05 14:39): 删掉本组 6 个模块的 `.agdai` (逐个写模块名: `StrRel18If`, `StrRel18Az`, `StrRel18Obs`, `StrRel18KZ`, `StrRel18Up`, `StrRel18Tr`; 入口原本没有; 未动 `NegSR18*`), 从入口重编: 退出码 0, 约 16 秒, 峰值常驻约 2.9 GB (`-M8G`). 代码块里 `postulate`, 洞, `TERMINATING`, `NON_TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext`, K 都是 0. 编译只有一处工程问题: `StrRel18Up` 的不可达子句警告 (第 $0$ 层的 `ni⁺`/`κ⁺`/`nκ⁺` 已被自动排除), 删去后无警告.
- **导入闭包** (`importclosure.py`, `--only` 同 `StrRel17` 加 `OCF.Align.NegSR17`: `OCF.Free.Level`, `OCF.BTBO`, `OCF.Align.` 下的 `CumReadCF`, `TLRule`, `TLOpsW`, `SumOne`, `BrwMid`, `LayerTr`, `CvFold`, `CvHigh`, `CvLayer`, `NoCumLit`, `L1Val`, `DVal`, `HtGen`, `HtFeed`, `HtCross`, `KVal`, `KNest`, `MonoPort`, `StrRel`, `NegSR16`, `NegSR17`): 入口闭包 93 个模块 (本地 83, 库 10), 禁用表 0, `--only` 之外 0; `If`, `Az`, `Obs`, `KZ`, `Up`, `Tr` 各自单跑 (69, 75, 87, 81, 82, 83 个模块), 都是禁用表 0, `--only` 之外 0.
- **定义级切片** (`depslice.py`, `--html` 由本组入口在编译通过后生成; 正对照 `Om1HnAccept` 及其闭包的 html 从 `StrRel17` 那一轮的 scratch 目录拷来, 未重生成): `¬noZ-fold` 130 块, `¬AiNoZ` 127, `obsZ` 251, `obsKZ` 253, `¬domKJ` 211, `¬RkSoundTKD` 285, `¬domKZ-P` 248, `upX` 304, `upHalfV` 328, `trans00⁺` 214, `RkSoundTK` 149, `UpSound` 147; 记号模块 0, 记号词 0. 正对照 `Om1HnAccept:label-term₀` 1188 块, 记号模块 92, 记号词 58. 切片看不见模块应用, 块数偏少; 记号无关由导入闭包保证.
- **行数** (代码, 去空行与注释): If 107, Az 76, Obs 94, KZ 29, Up 86, Tr 40, 入口 11; 合计 443. 全部手写; 两处用 Python 做了字面替换 (把 `(Y₁ tt)` 换成 `Y1`, 删不可达子句), 是一次性编辑, 没有生成的部分, 所以 `probes/Survey/scripts/strrel18/` 没有脚本.

## 0 模块

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel18 where

open import Data.Unit using (tt)
open import OCF.Align.StrRel13Val using (Λ₂)
open import OCF.Align.NegSR16Kap using (Λκ; lΛκ)
import OCF.Align.StrRel18If
open import OCF.Align.StrRel18Az public using (r; K; brK; chkK; brK-shape; kindK; inFold; cellK; noZ-Act; noZ-Air; ¬noZ-AiK; ¬AiNoZ; ¬noZ-fold)
open import OCF.Align.StrRel18Obs public using (module Gen; preY₁; noZΛ₂; obsZ; ¬domKJ; domKD₁; domKZ₁; obsK; obsKD; obsKZ; domKD-P; ¬RkSoundTKD)
open import OCF.Align.StrRel18KZ public using (ω≤R; ¬domKZ-P)
open import OCF.Align.StrRel18Up public using (upX; upHalf; upHalfV; UpStep; upExp; APH; APH₀; comp; module Tr; trans00; invNw; trans→APH₀)
open import OCF.Align.StrRel18Tr public using (canc; admH; alH; aph; trans00⁺)
```
