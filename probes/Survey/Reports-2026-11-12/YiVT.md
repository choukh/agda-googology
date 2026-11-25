# 比较表那一行的值的搬运 (YiVT)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-14 10:18 至 10:56 |
| 工具调用 / agda 编译 (粗数) | 88 / 12 |
| token (usage 字段，按消息去重) | 输出 132699；新写入缓存的输入 372050；读缓存的输入 21545581；其余输入 174 |
| 写过的仓库文件 | `YiVTNorel.lagda.md` |
| 文件前缀 | `YiVT` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: 第四十三批 YiVT 返回并复核; 第四十三批全部返回 (主审)” 一节 |
| 主审复核后的一句结论 | 无前提: F2 对照块 YiVTFold (只改那一行的四个子句) 与新主线折叠逐层相关, 对一切层号 (YiVTRel); 闭项相关 (twᶻ-R, EBOᶻ-R); 原主线的值定理全部搬到新主线: 塔第 2 项 ≥ ψ₀(Ω_Ω+ψ₁(Ω₂)), 终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω)), tA≺EBOᴿ, btbo≺EBOᴿ; 另证塔第 2 项起 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω)) (tω≼twᶻ), 原主线同样 (tω≼tw2ᴿ, 不是比较表带来的); 新旧塔第 2 项直接比较未做; 32 件 (24 件副本, 约 4100 行验收脚手架) 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定与原则（2026-11-14，选项原文或原话）
- 主线 "经指定孩子" 那一行："改取最小比较表，原主线的值保留作参照 (Recommended)"。新主线折叠是 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`。
- 本批本路（选项原文）："(2) 比较表那一行的值 V168 (Recommended)"，说明是 "在 F2 一侧也写带表的那一行并重证下降引理，或按值比较不同孩子层上的折叠；把终点的高下界搬到新闭项，并看新塔第 2 项是否高于原来"。
- 原则："不能以'追求同步'为名反过来指导树的定义形状"；"第 4 层不反过来改前 3 层"（AGENTS）。本路只在验收一侧，不改新主线的树、折叠、合法性；F2 一侧若要新写带表的那一行，那是验收用的对照块，不是新定义。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

###### 已有的东西（主审复核过；先读，不重证）
- **新主线的值**：`YiMTValue`（`same-tw1ᶻ`、`btbo-twᶻ`、`btbo-EBOᶻ`、`k1ᶻ`、`K2-redᶻ`、`row-zz`、`B1-shape`、`br1-Rᶻ`、`norel`）、`YiMTRel`（`A`、`S`、`Am`、`Sm`，带 `NoΩ` 前提；`topΩ`）、`YiMTKeel`（`tw≼ᶻ`、`keelᶻ`、`row0ᶻ`）。回报 `probes/Survey/Reports-2026-11-12/YiMT.md`，§4 原文："精确到引理：`YiMTRel.S` 缺 'Ω 形状层号、路径经指定孩子（`wincΩ`）、树是嵌入' 这一条。`norel` 表明带 `rbᶻ` 时这一条照原陈述为假：新行给 `next⁺ 1`，F2 回退行给 1 + ω"。
  - 出路（执行方的判断）：在 F2 一侧也写带表的那一行，重证 F2 上对一切 `OKB` 底陈述的下降引理（`ψs-⊵`、`ok-dW`、`reach` 一族）；或按值比较不同孩子层上的折叠（`YiVRRead.GMono` 的带底形式）。
- **原主线的值是怎样来的**：`YiSMRel`、`YiSMValue`、`YiSMEnd`（兄弟孩子候选上的搬运，经 F2 上手造的底与 `btbo-B`、`reach`、`reach³`、`reachG`、`Ω≽0`、`Ω≽1`）；原主线 `YiANLim.tω≼EBOᴿ`、`YiTWEnd.tA≺EBOᴿ`、`YiEVEnd`、`YiPHEnd`、`YiANEnd`；F2 块 `YiLeg*`、`YiBR*`；`readRW` 在 `YiBRValue`。
- **新主线上那一行的触发位置**：`YiMTHit`（`hit-tw≥2ᶻ`、`hit-Λ1ᶻ`、`hit-Λ2ᶻ`）；塔上 c′ = c = 0。

###### 要做的（按序；推进的是 "新主线的编译值回到原主线的水平以上"）
0. **最小实例检查**，在临时目录：
   - 选一条出路，在最小的地方核对它可行：例如塔第 2 项的链元 2（`row-zz` 那一处）上，新的一支与 F2 一侧（或一个值上的参照）的关系能写出，第 0 项不再像 `norel` 那样错开。
   - 不可行就换另一条出路；两条都不可行就停下回报，精确到引理。
1. **搬运**：把 `tA ≼ tw 2`（ψ₀(Ω_Ω+ψ₁(Ω₂))）搬到 `twᶻ 2`；再把终点的各条（`tA`、`t₃`、`tN`、`tω`，即到 ψ₀(Ω_Ω+ψ₁(Ω_ω))）搬到 `EBOᶻ`。做到哪一步算哪一步。
2. **新旧比较**：新塔第 2 项是否不低于原塔第 2 项，并检查新塔第 2 项能否证到比原主线更高的记号下界。原主线塔第 2 项的最高下界见 `YiEVTw2.tA≼tw2ᴿ` 一类。证不了就交第一个挡住的引理。
3. 说明所用的 F2 对照块（若新写）与原 F2 的差别只在哪一行，以及它为什么不是新的定义。

**纪律**（作者同意的，必须照做）：
- 动手证一般形式之前，先用临时文件检查前提可满足。
- 已有引理先检索再写，不重证；搬来的证明在文首写明来源。
- 不改任何已有文件，包括 F2 的 `YiLeg*`。F2 一侧要带表的那一行就新建文件。
- 停止条件触发时，先停下回报；若你认为改题有价值，在回报里写成建议。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiVT`（模块名 `OCF.Lean.YiVT…`）。不碰 `src/`、`archive/`，不碰另一路的前缀 `YiLT`。验收文件（含 F2 对照块）文首标明 "验收文件"。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G（`YiMTHit` 一类文件冷编要约 7G，若你导入它请注意）。另一路也在编译，不用 `--ignore-interfaces`，只删自己模块的 `.agdai`。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量，执行前核对路径。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。
  - 堆墙：不要在具体推导上直接比较两个 `Rt`；具体参照树放 `opaque`；见 `probes/Survey/EBOHandbook.md` 第 4 节。
  - 沙箱里 `/usr/bin/time` 不可用，内存用 `+RTS -s` 看。
- 临时目录：`<实验目录>/agents/vt`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽；第 0 步两条出路都不可行。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：第 0 步选了哪条出路及结论；搬运到哪一步；新旧比较；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### YiVT 回报：比较表那一行的值 (V168)

##### 1. 判决

**第 0 步：选第一条出路（F2 一侧也写带表的那一行），可行。** 第二条出路（按值比较不同孩子层上的折叠）没有尝试。

- F2 对照块 `YiVTFold` 通过检查器（停机按层号）。
- 新主线的折叠 `YiTBRow.ψ` 配 `rbᶻ` 与它逐层相关，**对一切层号，没有 `NoΩ` 前提**（`YiVTRel.A / S / Am / Sm / cS / cL / cΩ`）。
- `norel` 那一处换成对照块后相关（`YiVTNorel.rel-x₁`）。
- 闭项相关：`twᶻ-R : (n : ℕ) → RelT zero F.zero (twᶻ n) (F.twᶜ n)`，`EBOᶻ-R`。所以 `readRW (twᶻ n) ≅ read (F′.twᶜ n)` 对一切 n 成立，终点同理。

**搬运：全部搬到（编译定理，无前提）。**
- 塔第 2 项：`tA≼tw2ᴿ`，即 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照 ≼ `twᶻ 2`。
- 终点 `EBOᶻ`：`tA`、`t₃`、`tN m`（一切 m）、`tω` 四条都到，即到 ψ₀(Ω_Ω+ψ₁(Ω_ω)) 的参照；另有 `tA≺EBOᴿ`、`btbo≺EBOᴿ`。新主线的编译值回到原主线的水平。

**新旧比较。**
- 新塔第 2 项能证到的记号下界高于原来记录的 `tA≼tw2ᴿ`：`tω≼twᶻ2`，即 ψ₀(Ω_Ω+ψ₁(Ω_ω)) 的参照 ≼ `twᶻ 2`；由 `tw≼ᶻ` 对第 2 项起的每一项成立（`tω≼twᶻ`）。
- **这不是比较表带来的差别。** 同一证明原样写在原 F2 与原主线闭项上也通过（`YiVTTw2HiOld.tω≼tw2ᴿ`）。原主线塔第 2 项此前只证到 tA，是没有走 "孩子 0, 0, 2" 与 "0, 0, m+2" 这两条路径，不是值低。
- "新塔第 2 项不低于原塔第 2 项"：**没有定理，也没有否定，未尝试直接比较。** 现有的是两边同一条下界（都到 tω 的参照）。

**对纲领与目标。**
- 只在验收一侧，树、折叠、表、合法性一行未改；纲领各条不受影响。
- 事实：`YiMT` 回报里 "新闭项值停在 ψ₀(Ω_Ω)" 是搬运方法的缺口，不是值的缺口，现在补上。
- 翻译账：没有新增定义；新增的是验收用的 F2 对照块与 24 个照搬副本（约 4100 代码行），属验收脚手架。
- 判断（非定理）：下降引理一族（`ψs-⊵`、`ok-d*`、`reach`、`reach³`、`reachG`）对那一行怎么写不敏感，只要那一行的输出 ⊵ 左项的折叠；敏感的只有依赖回退行输出形状的少数闭项引理（见下文手改清单）。

**问题表。**

| 问题 | 位置 | 档 |
|---|---|---|
| 新塔第 2 项 ≥ 原塔第 2 项（直接比较） | 无 | 未证未否定，未尝试 |
| 对照块上 `Hi (tw 1) Br0` 对一切路径（原 `YiEVEnd.hi0`）没有重证，只证了孩子 c₁ 的底的 `hi1` | `YiVTEVEnd` | 缺口；下游只用到 c₁，不影响已交定理 |
| `rowG`、`hiΩ` 只对字面是 ℕ 极限的孩子、目标第 0 层陈述 | `YiVTEmb`、`YiVTHi` | 范围限制 |
| 24 个副本与原文件重复，折叠若再改要重新生成 | `YiVT*` 副本 | 工程；建议见 §5 |
| K(2) 第 1 行 | `YiMTValue.Row₂ᶻ 1 m` | 未碰，仍未走通 |
| 原 F2 里依赖回退行形状、没有搬的文件 | `YiDropRow`、`YiInv`、`YiCeilRead`、`YiMWLow` 的见证 V 部分、`YiT2Mono` | 未搬，本路目标不需要 |

##### 2. 文件表

全部在 `<仓库>/probes/OCF/Lean/`，共 32 个，代码行合计 5066。删自己全部接口后按依赖序冷编，8G，退出码全 0，每个日志只有自己模块的 `Checking` 行；禁用构造、本机路径、`Funext` 检索为 0；没有改任何已有文件。`YiVTNorel` 写在冷编启动之后，单独首次编译（等于冷编）。

| 文件 | 性质 | 代码行 | 退出码 | 内存 MiB |
|---|---|---|---|---|
| `YiVTFold` | F2 对照块（新写一行，其余照搬） | 327 | 0 | 511 |
| `YiVTRel` | 关系（脚本自 `YiSMRel`，新写 `tb-R` 与三支） | 405 | 0 | 3963 |
| `YiVTTw` | 新写：闭项相关 | 28 | 0 | 2160 |
| `YiVTNorel` | 新写：最小实例 | 约 25 | 0 | 2415 |
| `YiVTEmb` | 新写：那一行在塔第 1 项顶层的值 | 55 | 0 | 1894 |
| `YiVTHi` | 新写：一般底上经 ℕ 极限孩子 ≥ BTBO | 32 | 0 | 1928 |
| `YiVTTw2Hi` | 新写：新塔第 2 项 ≥ tω | 59 | 0 | 2298 |
| `YiVTTw2HiOld` | 新写：原塔第 2 项同一条（对照） | 53 | 0 | 2148 |
| `YiVTLSFold` | 副本，改 1 处（`ψs-⊵` 那一行） | 679 | 0 | 4988 |
| `YiVTT2Frame` | 副本，改 2 处（`fallback` 加前提；删 `β₁-form`） | 113 | 0 | 1484 |
| `YiVTEVTw2` | 副本，改 `compβ` 与出口 | 55 | 0 | 2296 |
| `YiVTEVEnd` | 副本，改 `hi0`→`hi1`、`path₂`、出口 | 76 | 0 | 2305 |
| `YiVTPHEnd` | 副本，改 `path₃`、`hi1`、出口 | 129 | 0 | 2388 |
| `YiVTANEnd` | 副本，改 `G`/`shape`/`gk`/`pathN`、`hi1`、出口 | 165 | 0 | 2388 |
| `YiVTANLim` | 副本，改出口 | 116 | 0 | 2297 |
| `YiVTTWEnd` | 副本，改 `path₁`、`hi1`、出口 | 49 | 0 | 2225 |
| `YiVTLSTw1` / `EBShape` / `LSBtbo` / `EBBtbo` / `MEAnchor` / `MEStep` / `T2Desc` / `EXRow` / `MWPre` / `EVReach` / `PHBase` / `PHCtx` / `ANFam` / `ANKp` / `ANLv` / `ANReach` | 副本，只换导入，证明一字未改 | 115 / 61 / 189 / 104 / 204 / 80 / 114 / 83 / 115 / 89 / 113 / 367 / 214 / 226 / 588 / 40 | 全 0 | 1092–2435 |

副本的手改处在文内都有 "改:" 注释。冷编日志在 `<实验目录>/agents/vt/cold-YiVT*.log`，汇总在同目录 `cold.out`。

##### 3. 定理表（都是编译定理，无前提）

| 名字 | 陈述（逐字） | 白话 | 文件 |
|---|---|---|---|
| `A` | `∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′ → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′) → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′ → RelT zero F.zero (proj₁ (ψ⁰ ℓ o B zero (z≤ ℓ) β x)) (F.ψ⊥ ℓ′ ε ρ B′ x′) × RelD zero F.zero (proj₂ (ψ⁰ ℓ o B zero (z≤ ℓ) β x)) (F.nz⊥ ℓ′ ε ρ B′ x′)`，其中 `ψ⁰ ℓ o = ψ ℓ o (rbᶻ ℓ)` | 配表的折叠朝第 0 层与对照块相关，对一切层号 | YiVTRel |
| `S`（及 `Am`、`Sm`、`cS`、`cL`、`cΩ`） | 同 `YiSMRel` 的陈述，折叠换成 `ψ⁰`，F 换成 `YiVTFold` | 一般目标、单调、孩子的底同样相关 | YiVTRel |
| `tb-R` | `∀ {k h k′ h′} → ((c : Tr k) (c′ : F.Tr k′) → RelT k k′ c c′ → RelL (h c) (h′ c′)) → ∀ {c c′ c₁ c₂} → RelT k k′ c c₁ → RelT k k′ c′ c₂ → RelEnt (tbᶻ k h c c′) (F.tbᶠ k′ h′ c₁ c₂)` | 两边的表在相关孩子上给同一种条目 | YiVTRel |
| `rel-x₁` | `RelT zero F.zero (proj₁ (ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) zero (inc zero self) (Ωt zero) x₁)) (F.ψs (F.tw 1) (F.Ev-tw 1) (F.Rt-tw 1) (F.B₀ (F.tw 1)) F.zero (F.inb F.zero F.self) (F.Ωt F.zero) (F.Ωt-nz F.zero) x₁′)` | `norel` 的那一处现在相关 | YiVTNorel |
| `twᶻ-R` | `(n : ℕ) → RelT zero F.zero (twᶻ n) (F.twᶜ n)` | 新塔每项与对照块的塔相关 | YiVTTw |
| `EBOᶻ-R` | `RelT zero F.zero EBOᶻ F.EBOᶜ` | 终点相关 | YiVTTw |
| `ψs-⊵` | `(ℓ : LF) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : LF) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr ℓ) → j ⊢ β ⊴ ψs ℓ ε ρ B j w β nβ x` | 对照块上折叠不低于起点（那一行按表三支重证） | YiVTLSFold |
| `reach` | `∀ {ℓ} → two ⇐ ℓ → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → Lo ℓ ε ρ B` | 下降引理在对照块上成立（证明未改） | YiVTEVReach |
| `em-fold` | `∀ {ℓ} → NL ℓ → ∀ {t} → Em1 ℓ t → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (w : zero ≤ ℓ) (b : Tr zero) (nb : zero ⊢ zero ◃ b) → ψs ℓ ε ρ B zero w b nb t ≡ next b nb` | 没有 Ω 形状的层号上，嵌入的 1 朝第 0 层的折叠逐字是 `next b` | YiVTEmb |
| `rowG` | `(B : Base (tw 1)) (c : Tr zero) → IsLim c → (w : zero ≤ h₁ c) (b : Tr zero) (nb : zero ⊢ zero ◃ b) (x : Tr zero) → read (G x) ≼ read (rowT B c w b nb x)` | 孩子是 ℕ 极限时，那一行不低于标准底的 `G x` | YiVTEmb |
| `hiΩ` | `(c : Tr zero) → IsLim c → (w : zero ≤ h₁ c) (b : Tr zero) (nb : zero ⊢ zero ◃ b) → D.BTBOᴵ ≼ read (ψs (tw 1) (Ev-tw 1) (Rt-tw 1) B zero (inb c w) b nb (Ωt (tw 1)))`（模块参数 `B`、`OKB (tw 1) B`、`Start B`） | 一般底上经 ℕ 极限孩子朝第 0 层的折叠 ≥ BTBO | YiVTHi |
| `hi1` | `Hi (h₁ c₁) B₁` | 终点第 2 支里孩子 c₁ 的底的各分量 ≥ BTBO（替代 `hi-dW … hi0`） | YiVTEVEnd |
| `tA≼tw2ᴿ` | `(h : HC tA) → R2.Rt h ≼ readRW (twᶻ 2)` | ψ₀(Ω_Ω+ψ₁(Ω₂)) ≼ 新塔第 2 项 | YiVTEVTw2 |
| `tA≼EBOᴿ` | `(h : HC tA) → R2.Rt h ≼ readRW EBOᶻ` | 同上，对终点 | YiVTEVEnd |
| `btbo≺EBOᴿ` | `L.suc D.BTBOᴵ ≼ readRW EBOᶻ` | 终点严格高于 BTBO | YiVTEVEnd |
| `tA≺EBOᴿ` | `(h : HC tA) → O.suc (R2.Rt h) ≼ readRW EBOᶻ` | 终点严格高于 tA | YiVTTWEnd |
| `t₃≼EBOᴿ` | `(h : HC t₃) → R2.Rt h ≼ readRW EBOᶻ` | ψ₀(Ω_Ω+ψ₁(Ω₃)) ≼ 终点 | YiVTPHEnd |
| `tN≼EBOᴿ` | `(h : HC (tN m)) → R2.Rt h ≼ readRW EBOᶻ`（模块参数 `m : ℕ`） | 对一切有限 N | YiVTANEnd |
| `tω≼EBOᴿ` | `(h : HC tω) → R2.Rt h ≼ readRW EBOᶻ` | ψ₀(Ω_Ω+ψ₁(Ω_ω)) ≼ 终点 | YiVTANLim |
| `t₃≼twᶻ2` | `(h : HC t₃) → R2.Rt h ≼ readRW (twᶻ 2)` | 新塔第 2 项 ≥ t₃ | YiVTTw2Hi |
| `tω≼twᶻ2` | `(h : HC tω) → R2.Rt h ≼ readRW (twᶻ 2)` | 新塔第 2 项 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω)) | YiVTTw2Hi |
| `tω≼twᶻ` | `(n : ℕ) (h : HC tω) → R2.Rt h ≼ readRW (twᶻ (suc (suc n)))` | 第 2 项起每项如此 | YiVTTw2Hi |
| `tω≼tw2ᴿ` | `(h : HC tω) → R2.Rt h ≼ readRW (RW.twᶜ 2)` | 原主线塔第 2 项同样 ≥ tω（对照） | YiVTTw2HiOld |

前提可满足的实例：`inst-tw2`、`inst₃`、`instω`（`hA`、`h₃`、`hΩω` 是已有推导）。

##### 4. 第一个障碍，精确到引理

本路目标内没有挡住的引理。目标外的两处：

- **新旧塔第 2 项的直接比较。** 两个塔从链元 2 起不同（`YiMTValue.row-zz` 对 `row-zzᶜ`）。要比较 `readRW (RW.twᶜ 2)` 与 `readRW (twᶻ 2)`，需要 "折叠 `ψ (tw 2) …` 对分支下标（层号 `tw 1` 上的树）按值不降"，即 `YiVRRead.GMono` 的带底形式；没有证，没有尝试。
- **对照块上全路径的 `hi0 : Hi (tw 1) Br0`。** 原证明靠回退行的输出形状 `_ + ι zero (twᶜ 1)`。带表时那一处走 `self` 条目，分量变成层号 `tw 1` 上 Ω 树沿任意路径朝第 0 层的折叠；孩子字面是零或后继，以及 `ink`、`inu` 路径的情形，要 "`ψs` 沿任意路径到第 0 层的值不低于 BTBO" 这样一条，没有证。下游只用孩子 c₁（ℕ 极限），所以改证 `hi1` 绕开。

##### 5. 第 3 步、偏离与事故

**F2 对照块与原 F2 的差别。**
- 互递归块逐行 diff 只有 4 处（删 7 行，增 41 行），正是 `(Ωₗ k h, inb c′, up x c y)` 一行的四个子句（`ψs`、`nzs`、`monos` 的 `◃u` 与 `◃c`）。
- 另加表的定义 `z≤ᶠ`、`loᶠ`、`hiᶠ`、`tbᶠ`（`YiMTTab.tbᶻ` 在 F2 层号上的同文）与 `tW` 的分情况。`Base`、`chB`、`kp`、`kp-ind` 从 `YiLegFold` 原样重导出，所以 `YiBRRel / BRLem / BROps / BRFold / BRTw` 的关系引理直接可用。
- 它不是新定义：新主线的折叠是 `YiTBRow.ψ` 配 `rbᶻ`，对照块只是让 `RelT` 能逐层成立的参照，文首标了 "验收文件"。

**对照块上值的形状变了的地方**（副本里手改，都有 "改:" 注释）：
- 塔第 1 项顶层，经 ℕ 极限孩子朝第 0 层：分支字面是零的一行由 `1 + G zero` 变成 `next b`（`rowG`）。
- 终点第 2 支里链的起点由 `β₁ + twᶜ 1` 一类变成以 `next 1` 起头的树，所以 `path₂`、`path₃`、`pathN`、`path₁` 的孩子编号改了（由类型检查确认，属有限测试档的形状事实）。

**偏离。**
- 第一条出路没有 "重证全部下降引理"：16 个文件只换导入就通过；实际重证或新写的是 §2 表里标出的几处。
- 多做了简报没有要求的两个文件 `YiVTTw2Hi`、`YiVTTw2HiOld`（第 2 步 "能否证到更高"）。后者是在原 F2 与原主线闭项上的新定理，放在本路前缀下；主审若认为不该放在这里可移走。
- 副本去掉了原文件的讲解文字，只留代码与一行来源说明（文字预算）。
- 生成脚本在临时目录（`genfold.py`、`mkfold.py`、`genrel.py`、`copy.py`、`patches.py`、`tw2hi.py`），没有进仓库。

**建议（判断）。** 若新主线定稿，可把 F2 的折叠改成对表参数化的一个文件，原 F2 是空表实例，免去 24 个副本；这要改已有文件，交作者定。

**事故。**
- 没有堆耗尽、超时、内部错误。
- `rm` 只删了自己前缀的文件：中途弃用的四个副本源文件（`YiVTCeilRead`、`YiVTInv`、`YiVTDropRow`、`YiVTT2Mono`）与 `probes/_build/2.8.0.2/agda/OCF/Lean/YiVT*.agdai`。
- 第 0 步没有另写一个单独的最小实例临时文件；临时文件 `VT0.agda` 只查了折叠的停机，关系直接在 `YiVTRel` 上对一般形式编译，最小实例事后补成 `YiVTNorel`。

**没有读、只凭转述或文首引用的。**
- `YiVRRead.GMono` 的陈述。
- `YiMTHit`、`YiMTKeel` 的正文（只用了 `tw≼ᶻ` 的签名）。
- `YiPHCtx`、`YiANKp`、`YiANLv`、`YiANFam`、`YiMWPre`、`YiMEAnchor` 的证明正文（副本直接通过，没有读）。
- `YiSMEnd`、`YiSMValue` 的正文：没有照它的手造底做法，走的是原主线 `YiEV / PH / AN / TW` 一链的副本。
- 台账 V168 只读了检索到的一行。
