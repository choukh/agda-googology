# 值证明搬到下一站的折叠上 (YiNextVal)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-11 10:39 至 11:12 |
| 工具调用 / agda 编译 (粗数) | 37 / 8 |
| token (usage 字段，按消息去重) | 输出 206360；新写入缓存的输入 664400；读缓存的输入 6843427；其余输入 60 |
| 写过的仓库文件 | `YiNextValFin.lagda.md`, `YiNextValLgl.lagda.md`, `YiNextValPath.lagda.md`, `YiNextValRel.lagda.md` |
| 文件前缀 | `YiNextVal` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 值证明搬到下一站的一路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 转运定理做成；主线的 ChainP 推出下一站的闭项不低于 BTBO 的参照（条件定理）；下一站的闭项无条件地不低于 ψ₀(Ω_ω)；四件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 任务是 **把主线上的值证明搬到 "下一站" 那套折叠上**, 使得主线上一旦证出 `ChainP`, 下一站的闭项 `T⁺` 就立即有 "不低于 BTBO 的参照" 的定理. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 "第 4 层不反过来改前 3 层" (验收只新增关系与定理, 不改树, 折叠, 合法性的定义), Agda 一节 (选项, 文字预算, 退出码, 堆), "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 与 §5.4.
3. **回报原文**: `probes/Survey/Reports-2026-11-11/YiNext.md` (下一站的折叠是怎么写的), `YiLeanVal.md` (主线上的值证明是怎么写的).
4. 代码 (都已定稿, 可以导入, 不许编辑; 都在 `probes/OCF/Lean/`, 模块名 `OCF.Lean.<名>`):
   - **主线 (被搬的值证明所在)**: `YiLeanCore`, `YiLeanFold`, `YiLeanLegal`, `YiLeanTw3` (`F`, `pts`, `co`, `obs`, `T₃`); 验收 `YiLeanAccFin` (`read`, `fin`), `YiLeanValRel`, `YiLeanValAdd`, `YiLeanValFold` (`FOLD`, `FOLD⁰`, `lower-any`), `YiLeanValFin` (`lower-read`, `T₃-own`, `T₃-Ωω`, `ChainP`, `btbo-p`, `chainP₀`).
   - **下一站 (搬到这里)**: `YiNextCore` (与 `YiLeanCore` 的代码逐字相同, 但是另一个模块), `YiNextBase` (`Lv` 多一个构造子 `vΩ`, 与 `Up` 归纳—归纳; `cmp`), `YiNextFold` (`Ψ`, `Ψ-lgl`, `Up-mono`, `Ψ-cp`, `Ψ-dn` 互递归), `YiNextTop` (`F`, `P₃`, `T₃`, `T⁺`, `T⁺-term₀ : … ≡ T₃`, `T₃⊑T⁺`), 验收 `YiNextAcc` (`read`, `T₃≼T⁺`, `FromBTBO.btbo⁺`: 以 `D.BTBOᴵ ≼ read T₃` 为前提得 `D.BTBOᴵ ≼ read T⁺`).
   查签名用检索, 大文件不要整篇读.

#### 1 要交的, 按优先

1. **转运定理 (首选).** 主线的 `T₃` 与下一站的 `T₃` 按同样的规则造出, 但在不同的模块里. 证它们的链点读回结构互模拟:
   `∀ n → read (YiLeanTw3 的 co (pts n)) L.≅ read (YiNextTop 的 P₃ n 的坐标)` (两个 `read` 各自来自 `YiLeanAccFin` 与 `YiNextAcc`; 名字冲突用 `import … as`).
   然后由它与 `≼ᵖ` 对右边结构互模拟封闭 (若 `YiVmConExact` 里没有, 自己证: `x ≼ᵖ y → y L.≅ y′ → x ≼ᵖ y′`, `≼ˣ` 同理) 得到:
   ```agda
   chainP-transfer : YiLeanValFin.ChainP → ChainPⁿ      -- ChainPⁿ: 同一陈述, 链点换成下一站的
   btbo⁺-from-main : YiLeanValFin.ChainP → D.BTBOᴵ ≼ read T⁺      -- T⁺ 与 read 都是下一站的
   ```
   第二条要下一站上的 `btbo-p` (由第 2 项给) 与 `FromBTBO.btbo⁺`. 若转运定理做成而第 2 项还没做成, 也可以直接由主线的 `btbo-p` 加 "`read (主线 T₃) L.≅ read (下一站 T₃)`" 得到 `ChainP → D.BTBOᴵ ≼ read (下一站 T₃)`, 再接 `btbo⁺`; 两条路取更短的.
2. **下一站上的只带值的下界.** 把 `YiLeanValRel`, `YiLeanValAdd`, `YiLeanValFold`, `YiLeanValFin` 的结论搬到下一站的折叠上: 至少 `lower-any` (对可数层号, 即不经过 `vΩ` 的 `Lv`), `T₃-own`, `T₃-Ωω` (下一站的 `T₃`), 以及下一站上的 `btbo-p`. 若第 1 项的转运定理已经足够推出你需要的东西, 这一项可以只做 `T⁺` 一侧需要的部分; 说明取舍. 新的 `vΩ` 情形不必证 (`T₃` 只用可数层号); 若 `FOLD` 的归纳要处理它, 可以把定理限制到不含 `vΩ` 的 `Lv` (写一个谓词).
3. **能做就做.** `T⁺` 的一条比 `T₃-Ωω` 更强的无条件下界 (例如它链的第 1 项不低于什么); 只用已有的定理, 不要为它开新的证明体系.

搬运是机械的: 规则相同, 模块不同. 遇到下一站的定义与主线不同的地方 (互递归, `vΩ`, 模块划分), 写清怎么处理的.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (两个 `read` 的值是 `L.lim` 套不同的函数, 所以要结构互模拟 `L.≅`, 不要命题相等); 堆到 6G 仍耗尽 (先按手册 §4.2: 陈述逐字写, 大的项放 `opaque`, 隐式参数显式写出, 文件拆小).

#### 2 过程要求

- 读完上面的文件后尽快动手: 第一个文件 (转运定理的第一条引理) 在 20 分钟内写出并编译.
- 每写完一个文件就编译; 每次回复都要有工具调用, 不要在一次回复里只思考.

#### 3 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiNextVal` (模块名 `OCF.Lean.YiNextVal…`). 都是验收文件, 文首标 "验收文件"; 允许导入带记号闭包的 `OCF.Align.Value`, `OCF.Align.Level` 与旧验收文件. 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`. 同时在跑的另几路用前缀 `YiChain`, `YiChainNeg`, `YiFree` (都在 `probes/OCF/Lean/`), 不要动也不要依赖它们的文件.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`, 函数外延.
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/nextval`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做成了哪几项; 一段话说对纲领与目标意味着什么 (主线证出 `ChainP` 后, `T⁺` 的 BTBO 下界是不是立即可得).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值; 另报搬过来的值证明的代码行数, 与主线的 715 行并列.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型.
4. 办法: 转运定理怎么证的; 下一站与主线的定义不同处怎么处理的.
5. 第一个障碍 (若有), 偏离与事故.
强度写 ψ₀(Ω_x), 标明是定理还是读法; 下界不写成同值; 不用 "只差", "自然" 一类形容.

## 回报原文

#### 1 判决

第 1 项 (转运定理) 和第 2 项 (下一站上只带值的下界) 都做成了。第 3 项只做到一条便宜的下界。四个文件都冷编译通过，退出码全 0。

**对纲领与目标意味着什么。** 主线一旦证出 `ChainP`，`T⁺` 不低于 BTBO 的参照就立即可得，不用再做任何事：`btbo⁺-from-main : MV.ChainP → D.BTBOᴵ ≼ NA.read NT.T⁺` 是编译过的条件定理，前提就是主线 `YiLeanValFin` 里原样的 `ChainP`。反方向的 `chainP-back : ChainPⁿ → MV.ChainP` 也成立，所以链点那一条无论在主线上证还是在下一站上证，两边都通用。

- **强度。** 下一站 `T⁺` 现在有两条无条件的下界定理：
  - ψ₀(Ω_ω) ≼ `read T⁺`；
  - ψ₀(Ω_ω) + ψ₀(Ω_ω) ≼ `read T⁺`，这一条只是便宜的增长。
  - 它们都是下界，不是同值。`T⁺` 的 ψ₀(Ω_{Ω+1}) 仍只是读法；与 BTBO 持平仍是条件定理，缺的就是主线 `ChainP` 在 n ≥ 1 的部分。
- **纲领边界。** 这些都是验收文件，只新增关系与定理，没有改任何树、折叠、合法性的定义 (第 4 层规则)。这一路与 "树自足" 无关，是验收的搬运。

#### 2 文件表

都在 `probes/OCF/Lean/`。冷编译的做法：按字面路径删了这四个文件自己的 `.agdai`，再按 Rel、Path、Lgl、Fin 的顺序编译，每个日志只有自己那一行 `Checking`。代码行指 agda 代码块里的非空行。

| 文件 | 代码行 / 总行 | 冷编译退出码 | 常驻内存峰值 | 用时 |
|---|---|---|---|---|
| `YiNextValRel.lagda.md` | 174 / 233 | 0 | 1.45 GB | 7.7 s |
| `YiNextValPath.lagda.md` | 132 / 175 | 0 | 1.55 GB | 7.8 s |
| `YiNextValLgl.lagda.md` | 154 / 194 | 0 | 1.43 GB | 7.9 s |
| `YiNextValFin.lagda.md` | 182 / 253 | 0 | 1.49 GB | 8.7 s |

**行数，与主线值证明的 715 行 (`YiLeanVal` 的 Rel、Add、Fold、Fin 四个文件) 并列。**
- 共 642 行。
- 其中转运本身 531 行：Rel 174、Path 132、Lgl 154、Fin 的导入与 §1–2 共 71。
- 推出的结论 111 行：Fin §3–5。
- 我没有逐行重写那 715 行。主线已有和将来新增的、关于 `T₃` 链点读回的值定理，都可以经 `co≅`、`T₃≅`、`F≅` 直接搬到下一站。

**自查。** 检索 `postulate`、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`irrelevant-projections`、`--cubical`、洞、`Funext`、本机路径，结果都是 0。选项行都是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`，每个文件文首都标了 "验收文件"。

#### 3 定理表

下表中 MA = `YiLeanAccFin`，NA = `YiNextAcc`，MT = `YiLeanTw3`，NT = `YiNextTop`，NB = `YiNextBase`，MV = `YiLeanValFin`。`D` 取 `OCF.Align.YiBtValBT.D`，与主线 `ChainP` 用的是同一个。它与 `NA.D` 都是 `Diag.Diagonal Un.Uniform`，检查器把两者认作定义性相等。

**转运与封闭 (Fin)**

| 名字 | 逐字的陈述 | 白话 | 档 |
|---|---|---|---|
| `co≅` | `∀ n → MA.read (MT.Pt.co (MT.pts n)) L.≅ NA.read (NB.co (NT.P₃ n))` | 两边第 n 个链点的读回结构互模拟 (转运定理) | 编译定理 |
| `T₃≅` | `MA.read MT.T₃ L.≅ NA.read NT.T₃` | 两个 `T₃` 的读回结构互模拟 | 编译定理 |
| `F≅` | `∀ a l → MA.read (MT.F (toM a) (toM-lgl a l)) L.≅ NA.read (NT.F a l)` | 下一站任意合法的第 0 层树上的 `F`，与它搬到主线后的 `F` 互模拟 | 编译定理 |
| `≼ˣ-≅`, `≼ᵖ-≅` | `∀ {a b c : L.Ordᶜ L.zero} → a ≼ᵖ b → b L.≅ c → a ≼ᵖ c` (`≼ˣ` 同形) | 定义域对右边的结构互模拟封闭 (`YiVmConExact` 里没有，自己证的) | 编译定理 |
| `chainP-transfer` | `MV.ChainP → ChainPⁿ`，其中 `ChainPⁿ = ∀ n → Σ ℕ λ m → D.γ n ≼ᵖ NA.read (NB.co (NT.P₃ m))` | 主线的 `ChainP` 推出下一站的同一陈述 | 编译定理 (蕴涵) |
| `chainP-back` | `ChainPⁿ → MV.ChainP` | 反方向也成立 | 编译定理 (蕴涵) |

**BTBO 一环 (Fin)**

| 名字 | 逐字的陈述 | 白话 | 档 |
|---|---|---|---|
| `btbo⁺-from-main` | `MV.ChainP → D.BTBOᴵ ≼ NA.read NT.T⁺` | 主线证出 `ChainP`，`T⁺` 即不低于 BTBO 的参照 | 条件定理 |
| `btbo₃-from-main` | `MV.ChainP → D.BTBOᴵ ≼ NA.read NT.T₃` | 下一站的 `T₃` 同样 | 条件定理 |
| `btbo-pⁿ` | `ChainPⁿ → D.BTBOᴵ ≼ NA.read NT.T₃` | 照主线 `btbo-p`，只用下一站的链点 | 条件定理 |

上面三条条件定理的前提：`MV.ChainP = ∀ n → Σ ℕ λ m → D.γ n ≼ᵖ read (co (pts m))`，这里的 `read`、`co`、`pts` 都是主线的；`ChainPⁿ` 是同一陈述在下一站的链点上。可满足性：n = 0 是定理 (主线的 `chainP₀`)，n ≥ 1 没有证。

**下一站上无条件的下界 (Fin)**

| 名字 | 逐字的陈述 | 白话 | 档 |
|---|---|---|---|
| `lower-anyⁿ` | `∀ a (l : N.Lgl N.zero a) {κ} → Corr κ (MT.⌜ toM a ⌝) → L.ψ⁰ (L.Ω κ) ≼ NA.read (NT.F a l)` | 下一站上的 `lower-any`，对一切可数层号 | 编译定理 (下界) |
| `lower-readⁿ` | `∀ a (l : N.Lgl N.zero a) → L.ψ⁰ (L.Ω (L.toLevel (NA.read a) (HS-readⁿ a l))) ≼ NA.read (NT.F a l)` | 每个层号不低于它自己读成的层号上的参照 | 编译定理 (下界) |
| `T₃-ownⁿ` | `∀ n → L.ψ⁰ (L.Ω (L.toLevel (NA.read (NB.co (NT.P₃ n))) (HS-readⁿ _ (NB.lw (NT.P₃ n))))) ≼ NA.read NT.T₃` | 下一站的 `T₃-own` | 编译定理 (下界) |
| `T₃-Ωωⁿ` | `L.ψ⁰ (L.Ω L.ωᴵ) ≼ NA.read NT.T₃` | 下一站 `T₃` ≥ ψ₀(Ω_ω) | 编译定理 (下界) |
| `T⁺-Ωω` | `L.ψ⁰ (L.Ω L.ωᴵ) ≼ NA.read NT.T⁺` | `T⁺` ≥ ψ₀(Ω_ω) | 编译定理 (下界) |
| `T⁺-2T₃` | `(NA.read NT.T₃ L.+ NA.read NT.T₃) ≼ NA.read NT.T⁺` | `T⁺` 第 1 项的路上走到 `T₃ + T₃` | 编译定理，便宜的增长 |
| `T⁺-2Ωω` | `(L.ψ⁰ (L.Ω L.ωᴵ) L.+ L.ψ⁰ (L.Ω L.ωᴵ)) ≼ NA.read NT.T⁺` | 第 3 项：比 `T₃-Ωω` 强的唯一一条，不带新强度 | 编译定理，便宜的增长 |

`lower-anyⁿ` 的前提用的是主线的 `Corr`，作用在搬过去的树 `toM a` 上。它对一切合法的 `a` 可满足，由主线的 `corr-read` 给出；`lower-readⁿ` 就是这个实例。

**支撑定理 (编译定理，无前提)：**
- Rel：`ΨR`，两边的折叠把相关的输入折成相关的输出。还有 `addR`、`plusR`、`succR`、`psumR`、`chainR`、`nodeAtR`、`ΨnR`、`ΨNR`、`cmpR`、`shiftR`、`substR`，以及第 0 层相关的树读回结构互模拟的 `read≅`。
- Path：`addCpP`、`addWkP`、`succStepP`、`nodeAtDnP`、`ΨnDnP`、`ΨNDnP`、`ΨCpP`。
- Lgl：`ΨLglR`、`addLglR`、`plusLglR`、`succLglR`、`psumLglR`、`chainLglR`、`nodeAtLglR`、`ΨnLglR`、`ΨNLglR`。
- Fin：`shR`、`lvR`、`FR`、`FLR`、`ptR`、`T₃R`。

#### 4 办法

**跨模块的结构互模拟 (Rel)。**
- 层号的关系 `LR` 只含零、后继、ℕ 极限；位置的关系 `PR` 要求 ℕ 极限处编号相等。
- 树的关系 `RR k k′` 写成一个带参数的通用数据类型 `GR.Rel`，在每一对层号上取一次参数。结点处的分支要求 "相关的下标映到相关的树"，下标那一层的 `RR` 由 `LayRel` 沿位置走到。这样写避开了正性检查：`RR` 本身是函数，对层号递归。
- 派发的关系是 `WR`、`XR`。公共上界的关系 `VR` 只有 `v0`、`vs`、`vl` 三种情况，要求 ℕ 极限处两边的位置搬运把相关的位置送到相关的位置。
- `ΨR` 对 (`VR`, 树的推导) 做字典序递归。`cmp` 在 ℕ 极限处的 `subst₂` 由 `substR` 处理：对四个等式同时匹配 `refl`，端点都是变量，所以不需要 K。

**关键的一点：只有树的互模拟不够。**
- `lv η l` 在 ℕ 极限处的位置搬运 `sh` 是沿合法性证明里第一位置证明的路径走的。路径不同，搬运就不同，`cmp` 给出的槽位不同，输出的树也就不同。
- 所以还要让两边链点的合法性证明对应。做法 (Path、Lgl)：
  - 把第一位置证明记成路径 `List St`，步骤是 `D`、`S`、`C`、`L n`。
  - `LglR` 对树递归：ℕ 极限处要求每个 `Cp` 证明的路径相同；结点处对相关的合法下标逐支要求，单调证明只要求上端的下标相关。
  - 再证主线与下一站的 `add-lgl`、`succ-lgl`、`psum-lgl`、`chain-lgl`、`nodeAt-lgl`、`Ψn-lgl`、`ΨN-lgl`、`Ψ-lgl` 都保持 `LglR`。
- 有了这些，`ptR` 对 n 归纳，同时给出链点的树关系与合法性关系；`co≅`、`T₃≅` 由 `read≅` 得到。

**下一站与主线定义不同的地方，怎么处理的。**
- **`vΩ`。** `VR` 不含 `vΩ`。`T₃` 的各项只用可数层号 (`lv` 的输出)，下一站 `cmp` 与 `Ψ` 的 `vΩ` 子句从来不会被走到。
- **`Ψ` 与 `Ψ-lgl` 互递归。** 对引理没有影响：非 `vΩ` 的子句逐字相同，归约也相同。
- **模块划分。** 合法性引理在主线的 `YiLeanLegal` 里，在下一站的 `YiNextBase` 里；`Ψ-cp`、`Ψ-lgl` 在下一站的 `YiNextFold` 里。按名字分别引用即可。
- **下一站的 `T₃`。** 它经 `vΩ` 的 `top` 行定义性地化成 `lim (F (co (P₃ n)) …)` (即 `T₃-form` 的 `refl`)，`T₃R` 直接用这一形状。
- **`em`。** `RR` 不含 `em` 结点。从 `top` 出发的折叠与加法不产生 `em`，所以这是对关系的限制，不是对定理陈述的限制。
- **一般的合法树。** 第 2 项里的一般树先用 `toM` (带合法性与路径) 搬到主线，用主线的 `lower-any`、`lower-read`，再经 `F≅` 搬回。下一站的 `HS-readⁿ` 是照主线写的 12 行。

#### 5 第一个障碍、偏离与事故

- **障碍。** 检查器方面没有障碍。设计上的障碍是第 4 节说的 "合法性证明决定位置搬运"，这一层用 Path 与 Lgl 两个文件 (286 行) 补上了。
- **偏离一。** 没有逐文件搬 `YiLeanVal*` 的 715 行，第 2 项经转运得到。`lower-anyⁿ` 的前提用主线的 `Corr` 作用在 `toM a` 上，没有写下一站版本的 `Corr`。
- **偏离二。** 第 3 项只有便宜的 `T⁺-2T₃`、`T⁺-2Ωω`，没有新的强度。
- **编译错误，都已修好。**
  - `vlR` 与 `ll` 的隐式参数 `f` 没写类型，报 `SplitError.UnificationStuck`；补上类型后通过。
  - `BrR`、`BrL` 的类型里写了裸的绑定名，报 `ParseError`；改成带类型的绑定。
  - 主线 `Pt` 的字段要写 `MT.Pt.co`、`MT.Pt.lw`，原来写成了 `MT.co`。
- **事故：没有。** 没有改任何已有文件，没有碰 `src/`、`archive/`，没有动 `YiChain`、`YiChainNeg`、`YiFree` 的文件，没有提交。只按字面路径删过自己的四个 `.agdai`。

冷编译日志在：
- `<实验目录>/agents/nextval/cold-Rel.log`
- `<实验目录>/agents/nextval/cold-Path.log`
- `<实验目录>/agents/nextval/cold-Lgl.log`
- `<实验目录>/agents/nextval/cold-Fin.log`

Files are in `<仓库>/probes/OCF/Lean/`:
- `YiNextValRel.lagda.md`
- `YiNextValPath.lagda.md`
- `YiNextValLgl.lagda.md`
- `YiNextValFin.lagda.md`
