# (a) 把已证的第 2 站定稿成保底成品（记号无关）（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 09:33 至 09:47 |
| 工具调用 / agda 编译 (粗数) | 67 / 6 |
| token (usage 字段，按消息去重) | 输出 68849；新写入缓存的输入 201985；读缓存的输入 8420561；其余输入 124 |
| 写过的仓库文件 | `YiFNAccept.lagda.md`, `YiFNEntry.lagda.md` |
| 文件前缀 | `YiFN` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 保底成品定稿：入口与验收两个新文件（执行方起名 YiFNEntry、YiFNAccept；前缀与 11-15 的 YiFNTarget、YiFNUpper 撞名，是主审派发时没查重，主审已改名为 YiSHEntry、YiSHAccept）；主审冷编两件退出 0，入口导入闭包 OK，禁用构造 0；验收给出终点闭项不低于 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω) 的参照树与不低于 src 的 BTBO（序数值下界）；不新增数学；四层行数 89 / 485 / 849（层 4 读记号的验收另计）；导入闭包脚本的禁用表已按建议补 EboLean、EBOI 一族 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b86/Ship2.md`。先用 Read 工具完整读它，再逐条照做（含 "止损"、"规则" 与 "回报" 各节）。只新建简报允许的文件，不改其他文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

#### 回报：第 2 站保底成品定稿（前缀 YiFN）

**0. 一句话结论**
保底成品入口 `YiFNEntry` 已经写好，导入闭包里没有记号。它汇出层号与树的类型、折叠和表、终点闭项 `endᶻ`、合法性证据、内部 View、FGH 和大数 `bigᶻ = FGH endᶻ 99`。验收文件 `YiFNAccept` 给出两条编译定理：终点不低于 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω) 的参照树，也不低于 `src` 里 BTBO 的值。档位是序数值下界，不是互相 `≼`。没有改任何已有文件，也没有新增数学，`btbo-low` 只是把两条已有定理接起来。没有触发止损。

**1. 新文件与关键定理**（两件都是新建，删掉自己的接口后冷编，6G 堆，退出码 0）

- `<仓库>/probes/OCF/Lean/YiFNEntry.lagda.md`（成品入口，20 行代码；最大驻留 179MB）
  - 内容只有重导出和两个别名。文首写明 "读法 ψ₀(Λ) 只是读法，不是成品的声称"，并写明不声称到 EBO、ψ₀(Ω_{Ω₂}) 或第 3 站。
  - 对照 `YiPXFull` 补上的东西：
    - 层号与树：`L`、`Sh`、`Ch`、`Tr`、`T`、`Lt`、`Sig`，及构造子。
    - 塔与 Λ：`tw`、`Λ`、`↑`、`_⊕_`。
    - 折叠：`ψ`、`mono`、`Rb`、`RbS`、`rbᶻ`、`ψ₀ᶻ`。
    - 底与运算：`Base`、`B₀`、`Tr⁺`、`Ωt`。
    - 合法性：`Ok`、`OkS`、`Ok-tw`、`Ok-Λ`、`_≤_`、`z≤`、`Pth`。
    - View 与值：`view`、`VW`、`SigY`、`BrwView`、`V`、`val`、`_≼_`、`LegV`、`Part`、`Pt`、`Acc`、`ObjStep`。
    - FGH：`FGH`、`FGHᵥ`。
  - 沿用 `YiPXFull` 的有 `twᶻ`、`brwView`、`wf`、`vrec`、`objStep`、`val-leg`、`FGH-val`、`fghᶻ`。
  - 不再汇出 `EBOᶻ` 这个名字。
  - 两个别名：
    - `endᶻ : Tr zero`，`endᶻ = EBOᶻ`
    - `bigᶻ : ℕ`，`bigᶻ = FGH endᶻ 99`
- `<仓库>/probes/OCF/Lean/YiFNAccept.lagda.md`（验收文件，读记号，30 行代码；最大驻留 1.79GB）
  - `end-def : N.endᶻ ≡ MT.EBOᶻ`（`refl`）
  - `low : (h : E.HC (E.ψ [] (E.ψ (E.ψ (E.𝟏 ∷ []) [] ∷ []) [] ∷ E.ψ (E.𝟏 ∷ []) (E.ψ (E.ψ [] (E.𝟏 ∷ []) ∷ []) [] ∷ []) ∷ E.ψ [] (E.𝟏 ∷ []) ∷ []) ∷ [])) → RT.Rt h ≼ K.readRW MT.EBOᶻ`，证明是 `FY.target-low`。参照项逐字写成记号的构造子，即 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω)；参照树沿基本列抽取（`YiRefTw2.Rt`）。
  - `low-all`：同一参照项，换成 `SI.E.HC`，结论是 `SI.E.tree h ≼ K.readRW MT.EBOᶻ`（来自 `all-hc-low`）。
  - `inst : RT.Rt FY.hc-target ≼ K.readRW MT.EBOᶻ`，这是非空实例。
  - `btbo-low : tr₀ Ord-Ord.BTBO ≼ BR.readRW MT.EBOᶻ`，即 `≼-trans (proj₁ BTBOFull.BTBO≈) YiMTValue.btbo-EBOᶻ`。
  - 两个读回 `YiKVRel.readRW` 和 `YiBRValue.readRW` 是逐字相同的两份定义，各定理沿用各自来源的那一份。
  - ψ₁ 的读法写在文首，标为判断：ψ₁(Ω_ω) 在 Ω 的算术下没有闭式，照原样写。理由是参数 Ω_ω ≥ Ω₂，超出了 ψ₁(α)=Ω·ω^α 的适用范围；它的大小在 ε_{Ω+1} 与 Ω₂ 之间。

**2. 审计结果**

- **编译**：两件冷编退出码都是 0，日志里只有本模块的 `Checking` 行，无告警。
- **导入闭包**：`importclosure.py OCF.Lean.YiFNEntry` 退出 0，结果 OK，本地 13 个模块、库 8 个，禁用表命中 0。
  - 13 个本地模块：`BrwViewDef`、`YiMTTab`、`YiRWBlock`、`YiRWCheck`、`YiRWFold`、`YiRWOps`、`YiRWPath`、`YiTBRow`、`YiVWFGH`、`YiVWVal`、`YiVWView`、`YiVWWf`，加上入口本身。
  - `agda --dependency-graph` 得到的本地集合与脚本完全相同，都是 13 个；图里不含 `Axiom.Extensionality`。
  - 正对照：对 `YiFNAccept` 跑同一脚本得到 FAIL，命中 18 个，例如 `OCF.Align.EBO <- BTBOFull <- YiFNAccept`。
  - 工具局限（新发现）：禁用表的正则只匹配名字恰为 `OCF.Align.EBO` 的模块，`OCF.Align.EboLean*` 漏掉了。入口的 13 个模块我已逐个核对，没有这类模块；建议主审补这条正则。
- **定义级切片**（`depslice.py`，HTML 由 `YiFNAccept` 的闭包生成，退出 0）：
  - 以下各根到达的记号块与记号词都是 0：`endᶻ`（125 块）、`bigᶻ`（128）、入口全部重导出行 `<open>`（229）、`Ok-Λ`（54）、`Ok-tw`（52）、`mono`（97）、`brwView`（86）、`wf`（44）、`vrec`（99）、`objStep`（94）、`val-leg`（49）、`FGH-val`（39）。
  - 正对照：读标签的 `Correspond:FGH-Labω` 到达 72 块，其中记号块 47；`YiFNAccept:low` 到达 3267 块，其中记号块 198、记号词 176。
- **禁用构造扫描**：对 13 个闭包源码加两件新文件的代码块查了 postulate、TERMINATING、NO_POSITIVITY、trustMe、洞、K、`--cubical`、rewriting、Funext、本机路径，命中都是 0，且全部带 `--safe --without-K`。用含 Funext 的模块（`AdmWUip`）做正对照，扫描能查到。
- **Funext**：入口闭包里 0 处。

**3. 四层行数表**

口径：只数 agda 代码块里的非空、非注释行；按定义级切片去重，层间累计；不计标准库。

| 层 | 这一层加了什么（根） | 本层新增 | 累计 | 距标杆 1513 |
|---|---|---:|---:|---:|
| 1 纯定义 | 层号 `L`、各层的树与第一位置序、读回 `↑`、塔 `tw`、`Λ`（根 `YiRWBlock.tw`、`Λ`） | 89 | 89 | 1424 |
| 2 + 折叠与闭项 | 折叠 `ψ`（与 `mono` 互递归）、表 `rbᶻ`、底、运算、闭项 `twᶻ`/`EBOᶻ`/`endᶻ`、`FGH`、`fghᶻ`、`bigᶻ` | 396 | 485 | 1028 |
| 3 + 合法性证书（FGH 可算） | 证书 `Ok-tw`、`Ok-Λ`、`mono` 已在层 2 的闭包里（`ψ` 的类型要求 `Ok`），所以 +0；另加内部 View、良基递归、对象步进、值合法、FGH 值一致 | 364 | 849 | 664 |
| 4 + 值的定理 | `low`（即 `target-low`）+15650，累计 16499。其中记号侧 7757、树侧验收脚手架 5994、Level/Value/BTBOFull 参照框架 1726、src BTBO 108、成品模块里只有验收才用到的块 62、本文件 3。再加 `low-all`、`inst`、`end-def` +465，累计 16964。再加 `btbo-low` +2927，累计 19891 | 15650 / 465 / 2927 | 19891 | 不比标杆 |

- 与 YiPX（11-14）的 89 / 481 / 845 相比，逐模块数字一致，多出的 4 行是 `endᶻ` 和 `bigᶻ`。入口的重导出行另有 15 行，计入则层 3 为 864。
- 生成方法：用 `agda --html --html-highlight=all` 生成 `YiFNAccept` 闭包的 HTML。实验目录里的脚本执行仓库 `depslice.py` 主循环之前的部分（分块与超链接建图），从各层根做 BFS，累加到达块的行数；仓库脚本未改。这是块级语法近似，看不见隐式参数，数字可能略偏多。

**4. 成品说明（声称与不声称）**

声称（都是编译定理或编译构造）：
- 无公设、`--safe --without-K`、停机由检查器保证的闭项 `endᶻ : Tr zero`，以及塔 `twᶻ n`。
- 层号证据 `Ok-tw`、`Ok-Λ` 无前提。树的合法性在类型里：ℕ 极限带相邻步进，折叠输出非零，再加 `mono`。
- 内部 View（纲领第 1 条）：`brwView` 让每个对象在值上互相 `≼` 地看成零、后继、ℕ 极限或 Ω 极限；`wf`/`vrec` 沿 View 的部分良基递归；`objStep` 保证 ℕ 极限沿对象自身的第一位置步进；`val-leg` 是值的合法性。
- FGH：`FGH : Tr zero → ℕ → ℕ`，`bigᶻ = FGH endᶻ 99` 是闭的自然数项，`FGH-val` 说 FGH 与值上的 FGH 一致。
- 记号无关：编译器保证入口不引用记号，切片为 0。
- 值（读记号的验收，档位为序数值下界）：`endᶻ` 不低于 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω) 的参照树，对一切 `HC` 推导成立；也不低于 `src` 的 BTBO 的值。

不声称：
- 不声称到 EBO，ψ₀(Λ) 只是读法。
- 不声称 ψ₀(Ω_{Ω₂})，不声称第 3 站 ψ₀(Ω_{Ω_Ω})（即新终点）。
- 不声称上界、精确值或互相 `≼`；不比较 FGH 增长率。
- 不声称树自足，也不声称设计未受记号启发：导入闭包只保证不引用记号。

与 `src/OCF/BTBO.lagda.md` 的关系：
- 这是另一套树。层号本身是树，带 Ω 形状的层、塔 `tw`、`Λ = nd sL tw`；入口闭包里没有 `src` 的模块，也不改 `src`。
- 值的关系只有 `btbo-low` 一条，是非严格的 `≼`：终点不低于 `tr₀ BTBO`。严格高于没有在本文件里编译。`src` 自己把 BTBO 的标签 ψ(Ω_Ω) 写成估计，这里不替它定值。
- 两边基本列不同，FGH 不作比较。
- 进 `src/` 需要作者另行发起。

**5. 没有读、只凭转述引用的东西**

- 作者裁决原文与选项：只来自简报。
- `YiFRStations` 第 0 到 2 站（`k0`、`k1`、`k2`）：只读了文首和签名，没有重编。
- `BTBOFull.BTBO≈` 与 `YiMTValue.btbo-EBOᶻ`：只读了陈述，没读证明；类型由本轮编译 `btbo-low` 核对过。
- `YiTBRow`、`YiVWVal`、`YiVWView`、`YiVWWf`：只看了签名。
- RESULTS 里 "ψ₀(Ω_{Ω₂}) 没有任何闭项证到" 一行：读了原文，没有独立核实。
- YiPX 回报：读了，用作口径参照。
- 手册 §4：没读，因为没有遇到堆墙。
- ψ₁ 的读法（ψ₁(Ω₂)=ε_{Ω+1} 等）：是我按扩展 Buchholz 通常定义做的纸面判断，仓库里没有对应的编译定理。

实验产物（不进仓库）在 `<实验目录>/ship/`：
- 冷编日志 `YiFNEntry-cold.log`、`YiFNAccept-cold.log`
- 审计日志 `importclosure-entry.log`、`importclosure-accept.log`、`depslice.log`、`forbidden-scan.log`、`loc4.log`
- 依赖图 `YiFNEntry.dot`，HTML 目录 `html/`
- 脚本 `scan.py`、`loc4.py`

两个新文件都没有提交。
