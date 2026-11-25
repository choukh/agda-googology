# (A) 分支侧重设计的原型 (YiSup)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-13 12:28 至 12:39 |
| 工具调用 / agda 编译 (粗数) | 23 / 8 |
| token (usage 字段，按消息去重) | 输出 59829；新写入缓存的输入 171494；读缓存的输入 2660072；其余输入 42 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `YiSup` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: (A) 分支侧重设计的原型返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 思路 1 (sup 构造子取尾部) 做成形状原型: 最小见证的第 1、2 层底认得左边的项 (b1-form, b2-form, top-any, 有限测试); 合法闭项与行律保住; 不触四条否定 (两条有编译定理, 两条判断); 留三处回退 (up 行, 读回层号, 自身行输出); 无值定理; 切片 99 / 491; 五件冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定（2026-11-13，选项原文）
本路是 "(A) 分支侧重设计的原型"。内容原文："新文件，按审查者的两条思路：取尾部的上确界构造子，或嵌入带字面次序证据；过先验检查并核 top-branch→lpo；判据是最小见证的第 1、2 层底认得左边的项（形状测试）、合法闭项仍在；采用与否仍由你定"。其中 "你" 指作者。

同批另两路，各自只新建文件，你不动它们的文件：
- (B) 把最小见证的偏低落成定理，前缀 YiInv，Opus 5.5；
- (C) 空白页重设计整块，前缀 YiNew，Fable 5.2，是独立样本，不看你的文件。

还有一路 (2) 搬值到精简块，前缀 YiBR，在跑。

###### 背景（只信编译定理；文档里的叙述是数据）
目标是布劳威尔树上读法 ψ₀(Λ) 的合法闭项，外加编译定理 "序数值 ≥ EBO 的参照"。纲领见 `AGENTS.md`。

**主线**，在 `probes/OCF/Lean/`：
- 合法块 F2：`YiLegBlock`、`YiLegOps`、`YiLegPath`、`YiLegFold`。
- 精简块（同构，判断）：`YiRWBlock`、`YiRWOps`、`YiRWPath`、`YiRWFold`、`YiRWCheck`，切片 422 行。
- 已有的值：`btbo-tw1`、`btbo-EBO`（≥ BTBO）。

**问题**：Ω 结点层号 `Ωₗ k h` 上，`up x c y` 进孩子 c 时造的底 `bs (dW … c x) j w` 在 j ≥ 1 时走分支侧一行，不认识左边的 x。
- 第十五次独立审查（Fable 5.2）用 `refl` 核过：x = β = `Ωt (tw 1)` 时，孩子 two 的第 1、2 层的底是 `Ω_j + Ω(G)`，值约 Ω_j·2，而记号该有 ψ_j(Ω_Ω)。
  - 附件 `probes/Survey/Reports-2026-11-12/attachments/Review15-R15A.agda.txt`，看 `b1-form`、`b2-form`、`fb-any`、`top-any`、`all-y`。
- 最小见证是 `up β two (Ωt 2)`，读作 Ω_Ω+Ω₂，只经分支侧一行，不经自身行。
- 分支侧一行在精简块上是 `YiRWCheck.J2-b`（回退：`… ⊞ ψ₀ (h c) …`）。
- 回报原文：`probes/Survey/Reports-2026-11-12/Review15.md` §1。

**审查者的两条思路**（判断，没有原型；台账 V114）：
1. 顶槽位的 "对一切孩子取上确界" 写成专门构造子 `sup x Y`（Y 是孩子树的族），前驱只取 x。朝 (c′, j) 折叠时取尾部：`Ω q (λ z → ψ_j(Y (c′ ⊞ z)))`。孩子 `c′ ⊞ z` 与 c′ 有字面路径 `h c′ ≤ h (c′ ⊞ z)`，在塔上由对 z 的递归给出，同 `⊑lift` 的写法，作为层号证据的一个字段。
2. 普通的 `up x c y` 带字面的次序证据：和式里孩子层号不升，证据在构造时存下。进孩子 c 时，对左边每一项都有路径 j ≤ h c ≤ h c″，走正常递归。
3. 审查者自己说没有核对的：`sup` 结点的第一位置合法性；尾部取值与全体取值同上确界（要 Y 沿 ⊞ 值单调）；规范域是否对这两个构造子封闭；与 `probes/OCF/Align/YiOmNegBranch.lagda.md` 的 `top-branch→lpo : TopBranch → LPO` 的关系。

**已编译的边界**，新写法必须避开：
- `YiAbsFrame`：`hand→wdec`、`branch→wdec`。
- `YiAbsObs`：`obs→dec`、`full→dec`。
- `YiLNBranch`、`YiLNFlat`：在合法块上，反例在规范域。
- `YiOmNegBranch.top-branch→lpo`：请读它的陈述，说明新写法是否落在它的前提里。
- 层号比较写法（`YiAlt*`，`Fold true`）只修了摊平，对分支侧在 `tw 1` 上不对症（审查判断，有 `same-lev` 的 `refl`）。

**先验检查**（作者 2026-11-13 采纳为工作规则，见 `AGENTS.md`）：每个写法都要过三条，写进回报：
- 目标是指定孩子的还是一致的；
- 孩子下标类型上有没有证据函数；
- 有没有按存在性保留。

###### 要做
1. **实现思路 1 与 / 或思路 2**：新文件，可以复制精简块成你自己的 `YiSup*` 文件再改块与折叠。保住：
   - 塔与 Λ 的合法闭项；
   - 嵌入一致的其余各行、单调、非零；
   - 导入闭包干净（`importclosure.py` OK）。
2. **便宜的编译判据**（形状测试，`refl` 或小定理）：在新块的最小见证（`up β two (Ωt 2)` 的对应物）上，孩子的第 1、2 层底认得左边的项。例如底的第 1 层分量依赖 x：两个不同的 x 给出不同的底，或底里出现 x 的折叠。对照 R15A 的 `b1-form`、`b2-form`。
3. **核否定**：逐条说明新写法不满足 `branch→wdec`、`hand→wdec`、`full→dec`、`top-branch→lpo` 的前提。能编译的给定理，例如 "任何布尔观察不分离"，对照 `YiAltCheck.no-sep`；其余写清。
4. 写清代价：新构造子、新证据字段、行数（同一切片口径：从闭项出发的定义级切片），与精简块的 422 行比。

###### 注意
- 这是原型：只新建文件，不替换主线；采用要作者定。
- 不证值的下界。可以做值的有限测试，标 "有限测试"。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiSup`（模块名 `OCF.Lean.YiSup…`）。不改任何已有文件，不碰 `src/`、`archive/`。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"。无关参数可以用。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G。
  - 冷编只删自己模块的接口，写字面路径；不删别人的 `.agdai`，不用 `--ignore-interfaces`。`rm` 的目标不要写成 shell 变量。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
- 临时目录：`<实验目录>/agents/sup`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器（例如正性或停机）；6G 仍耗尽。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：哪个思路做成了，最小见证的底是否认得左边的项，是否避开四条否定；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 候选表：写法、先验检查三条、保住的行律、判据结果、代价、行数。
3. 文件表：代码行、冷编退出码、内存、importclosure。
4. 定理表：名字、逐字的陈述、一句白话、文件、档。
5. 翻译账：新写法哪些来自记号的规则，哪些由树的要求逼出。
6. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

### YiSup 回报：分支侧重设计的原型（思路 1：取尾部的上确界构造子）

#### 1. 判决

- **做成的是思路 1**（`sup` 构造子加尾部路径证据）。思路 2（`up` 带字面次序证据）没有做，见 §6。
- **最小见证的底认得左边的项（形状，有限测试，`refl`）**：新块的塔第 1 项上，孩子 2 在 x = `Ωt (tw 1)` 之后的第 1、2 层的底是顶槽位推下来的结点，第 z 支是 x 的尾项 `Ωt (h₁ (2 + z))` 朝该层的折叠（`b1-form`、`b2-form`）。对任意孩子树族 Y 也一样（`top-any`）。对照 R15A：旧块上是 `Ω_j + Ω(G)`，各支只含可数加项。
- **合法闭项仍在**：`twᶜ`、`EBOᶜ` 类型即合法；`Ok-tw`、`Ok-Λ` 无前提；`mono` 补了 `◃p` 的四行，停机与正性一次通过。
- **四条否定**：新写法不提供它们的前提，其中两条有编译定理支持，两条是写清的判断（§2 下方逐条）。
- **对纲领与目标的意义**：
  - 纲领 1 到 4 不受影响：仍是布劳威尔树，无公理，`sup` 的前驱只取 x（第一位置），导入闭包只有标准库与自身。
  - 对 "让树自足"：尾部路径 `h c ≤ h (c + z)` 是树侧的合法性证据，由对 z 的递归给出（`↑+`），不读记号。但 "该有 ψ_j(Ω_Ω)" 这个目标形状来自记号的诊断。
  - **值没有证**。这只是形状原型，不能说 Ω_Ω+Ω₂ 的值已经对了。

问题表：

| 问题 | 位置 | 档 |
|---|---|---|
| `up x c y` 的分支侧一行逐字未动，仍回退。左边的项若是 `up` 形（如 x = `up β c y`），底仍只多一个可数加项 | `YiSupCheck.J2-b` | 编译定理（形状） |
| 读回层号（`a ⊕ ↑c` 里的 Ω 形状）不带尾部路径，`sup` 在那里回退。R15 判断塔第 2 项起这类层号起作用 | `YiSupCheck.tl-⊕`、`sup-fb` | 编译定理（形状） |
| 自身行（`Up`）把 `sup` 输出成普通 `Ω` 结点，不是 `sup`；之后朝指定孩子折叠时走旧的结点行。规范域对新构造子不封闭 | `YiSupOps.Up`、`YiSupCheck.sup-self` | 编译定理（形状）加判断 |
| 尾部取值与全体取值是否同上确界（要 Y 沿 `+` 值单调）没有核 | — | 未做 |
| 尾部证据是可选字段（和类型），折叠按它派发；不是对一切合法层号成立的律 | `YiSupPath.Tl` | 设计选择 |
| `sup-head` 只对 `w ∙ lift` 一族路径；"任何布尔观察对 c′ 不分离" 对 `sup` 行证不出（输出按设计随 c′ 变） | `YiSupCheck.sup-head` | 判断 |
| `YiRWKall`、`YiRWSame` 没有搬到新块 | — | 未做 |
| 切片行数低估了增量：新增的折叠行很长（折叠文件代码字符 7186 → 11553） | §3 | 计数 |

#### 2. 候选表

| 项 | 思路 1：`sup q x Y e` |
|---|---|
| 写法 | 签名加字段 `Q`（只在 Ω 形状层号有居留）；树加构造子 `sup`（x 加孩子树族 Y 的上确界），序加 `◃p : x ◃ sup q x Y e`；`Ωt (nd (sΩ k) h)` 改成 `sup tt zero (λ c → Ωt (h c))`；Ω 形状的层号证据加可选字段 `Tl k h = ⊤ ⊎ ((c z : Tr k) → h c ≤ h (c + z))` |
| 折叠四行 | 自身：顶槽位结点，逐孩子上折。一致路径、下标层侧：顶槽位的结点行，第 z 支折 `Y z`。分支侧 (c′, v)：有尾部路径时第 z 支折 `Y (c′ + z)`，路径 `v ∙ tl c′ z`；没有时回退 |
| 先验检查 1：目标 | 指定孩子的。但行对一切 c′ 同一公式（`sup-tail`），不比较 c′ 与任何孩子下标，Y 只在 `c′ + z` 处读 |
| 先验检查 2：证据函数 | 有：`tl : (c z) → h c ≤ h (c + z)`。它是全函数，给路径，不是 `Maybe (c ≡ c′)` 一类的同支证据；`c + z` 是构造出来的，不是测试出来的。派发只看 `tlΩ o`，对孩子是常值 |
| 先验检查 3：按存在性保留 | 没有。不新增保留判定，复用 `kp`，槽位由路径末端算出 |
| 保住的行律 | `J2-u`、`J2⊥`、`J2-k`、`J2-s`、`J2-lim`（及 fwd、bwd）、`J2-b`、`self-up`、`node`、`kp-z`、`node⊥`、`kp-fwd`、`kp-bwd`、`kstep`、`tw-Nx`、`req-child`、`adj-Λ`，及原有限测试，全部在新块上重新编译通过；单调 `mono`；非零是值的类型 |
| 判据结果 | 通过（形状）：`b1-form`、`b2-form`、`b1-first`、`top-any`、`wit` |
| 代价 | 1 个签名字段，1 个构造子，1 条序，1 个可选证据字段，引理 `↑+`；折叠 4 行，单调 4 行 |
| 切片行数 | 块 99，加折叠与闭项 491。精简块同一脚本重算是 89 / 422。增量 +10 / +69 |

逐条对否定：

- **`branch→wdec`**（前提：某观察在 c₀ 支为真，在一切字面不同的支为假）。
  - `up` 行：x 是零时输出与 c′ 及其路径无关（`up-const`，`refl`），所以 `on` 与 `off` 不能同时成立（`up-no-sep`，编译定理）。
  - `sup` 行：没有编译的 "不分离"。有的是：对一切 c′ 同一公式（`sup-tail`）；在下一站 `w ∙ lift` 一族路径上头部对一切 c′ 都是 ℕ 极限（`sup-head`，编译定理）。判断：行里没有孩子下标的比较，分离只能来自调用者给的路径族。
- **`hand→wdec`**（前提：`Hand` 交接等式加可观察的回退）。新写法不主张 `Hand`：`up` 行对一切 c、c′ 仍是回退（`J2-b`），含 c = c′。`sup` 不是 `up` 形，`Hand` 的陈述不涉及它。
- **`full→dec`**（前提 `Full`：目标里有该层号的槽位，输出就以它为根）。`sup` 行不新增保留判定，槽位由 `kp` 沿字面路径算出；`sup-head` 给出一族 "不保留" 的实例。与主线结点行的关系相同。档：判断，加 `sup-head`。
- **`top-branch→lpo`**（读了陈述。前提 `TopBranch`：`branch q η` 对一切分支 η 有定义，且只要层号在目标层的某个位置上（`At`，存在性）并有 `Link`，像就是保留结点）。
  - 新写法不在前提里：分支侧只对尾部 `c′ + z` 给出像，不对任意 η；不主张按 `At` 的保留律。
  - 定理证明里用的是固定的坐标 2 那一支对任意目标 `qα α` 的像；`sup-tail` 的右边不读这样的支，除非它字面上是 `c′ + z`。
  - 档：判断。`TopBranch` 在另一个块（`OCF.Align` 的 `G`、`Raw`）上，没有编译的对应。

#### 3. 文件表

全部在 `<仓库>/probes/OCF/Lean/`。删自己五个接口后 6G 冷编，日志各只有自己模块的一行 `Checking`。禁用构造检索为 0，无函数外延，无本机路径。

| 文件 | 代码行 | 冷编退出码 | 最大驻留 / 总内存 | importclosure |
|---|---|---|---|---|
| `YiSupBlock.lagda.md` | 111 | 0 | 126 MB / 237 MiB | OK |
| `YiSupOps.lagda.md` | 116 | 0 | 140 MB / 236 MiB | OK |
| `YiSupPath.lagda.md` | 164 | 0 | 157 MB / 262 MiB | OK |
| `YiSupFold.lagda.md` | 143 | 0 | 190 MB / 330 MiB | OK（闭包本地 4 个，全是 YiSup） |
| `YiSupCheck.lagda.md` | 271 | 0 | 1.6 GB / 3321 MiB，约 10 秒 | OK（本地 5 个） |

切片用主审的 `slice_roots.py`（根 `tw`、`Λ`；`twᶜ`、`EBOᶜ`），HTML 在 `<实验目录>/agents/sup/html`，日志在同目录上一级。

#### 4. 定理表

| 名字 | 陈述（逐字，长的省去绑定） | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `↑+` | `(k : L) (c z : Tr k) → ↑ k c ⊑ ↑ k (c + z)` | 读回层号沿右加有字面路径 | YiSupPath | 定理 |
| `Ok-tw`、`Ok-Λ` | `(n : ℕ) → Ok (tw n)`；`Ok Λ` | 塔与 Λ 的证据是闭项，塔带尾部路径 | YiSupPath | 定理 |
| `mono` | 同 `YiRWFold.mono` 的陈述 | 折叠单调，含 `◃p` | YiSupFold | 定理 |
| `sup-tail` | `… (tl : (c z : Tr k) → h c ≤ h (c + z)) → tlΩ o ≡ inj₂ tl → ψ (nd (sΩ k) h) o B j (inc c′ v) β (sup tt x Y e) ≡ node⁺ (kp (nd (sΩ k) h) o top (inc c′ v)) (λ z → ψ (h (c′ + z)) (proj₂ o (c′ + z)) (cb o B (c′ + z) x) j (v ∙ tl c′ z) (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) (Y (c′ + z))) (λ z → fbS o B x Y (c′ + z))` | 分支侧取尾部，底带着 x | YiSupCheck | 定理 |
| `sup-tail-tw` | 同上，层号 `tw (suc n)`，证据 `Ok-tw (suc n)`，无前提 | 塔上无前提 | YiSupCheck | 定理 |
| `sup-fb` | `tlΩ o ≡ inj₁ tt → ψ … (inc c′ v) β (sup tt x Y e) ≡ ψ … (inc c′ v) β x ⊞ limc⁺ (λ n → ψ₀ (h (fbN o Y n)) (proj₂ o (fbN o Y n)) (Y (fbN o Y n)))` | 无尾部证据时回退 | YiSupCheck | 定理 |
| `sup-self`、`sup-u`、`sup-k` | 三行的形状，`refl` | 其余三行 | YiSupCheck | 定理 |
| `tl-tw`、`tl-Nx`、`tl-⊕` | `tlΩ (Ok-tw (suc n)) ≡ inj₂ (tlN (tw n))`；`tlΩ (Ok⊕ a (nd (sΩ k) h) oa ob) ≡ inj₁ tt` | 塔带尾部，读回层号不带 | YiSupCheck | 定理 |
| `Ωt-sup` | `proj₁ (Ωt (nd (sΩ k) h)) ≡ sup tt zero (λ c → proj₁ (Ωt (h c))) (λ c → proj₂ (Ωt (h c)))` | 规范 Ω 树用新构造子 | YiSupCheck | 定理 |
| `sup-mono` | `j ⊢ proj₁ (ψ (nd (sΩ k) h) o B j w β x) ◃ proj₁ (ψ (nd (sΩ k) h) o B j w β (sup tt x Y e))` | `sup` 的第一位置合法 | YiSupCheck | 定理 |
| `b2-form` | `proj₁ (BW L2 self) ≡ Ω q2 (λ z → proj₁ (ψ (h₁ (two + z)) (proj₂ o¹ (two + z)) (B₀ (h₁ (two + z))) L2 (self ∙ tlN zero two z) (Ωt L2) (proj₁ (Ωt (h₁ (two + z))))))` | 孩子 2 第 2 层的底：各支是 x 的尾项的第 2 层折叠 | YiSupCheck | 有限测试 |
| `b1-form` | 同形，层 `L1`，槽位 `q1`，路径 `inc tt self ∙ tlN zero two z` | 第 1 层同上 | YiSupCheck | 有限测试 |
| `b1-first` | `isLim (proj₁ (ψ (h₁ two) … L1 (inc tt self ∙ tlN zero two zero) (Ωt L1) (proj₁ (Ωt (h₁ two)))))` | 第一支是 Ω₂ 朝第 1 层的折叠，头是 ℕ 极限 | YiSupCheck | 有限测试 |
| `top-any` | `(Y …) (e …) → proj₁ (cb o¹ (B₀ (tw 1)) two (sup tt zero Y e) L1 (inc tt self)) ≡ Ω q1 (λ z → proj₁ (ψ (h₁ (two + z)) (proj₂ o¹ (two + z)) (B₀ (h₁ (two + z))) L1 (inc tt self ∙ tlN zero two z) (Ωt L1) (Y (two + z))))` | 对任意族 Y，底读 Y 的尾项的第 1 层折叠 | YiSupCheck | 定理（塔第 1 项、孩子 2 的实例） |
| `wit` | `(y : Tr L2) (e : L2 ⊢ zero ◃ y) → ψ₀ (tw 1) o¹ (up βΩ two y e) ≡ ψ L2 (proj₂ o¹ two) BW zero (z≤ L2) (ψ₀ (tw 1) o¹ βΩ) y` | 最小见证的值就是以 `BW` 为底的折叠 | YiSupCheck | 定理 |
| `witᶜ-lim` | `isLim witᶜ` | 最小见证的闭项的根是 ℕ 极限 | YiSupCheck | 有限测试 |
| `up-const` | `ψ (nd (sΩ k) h) o B j (inc c′ v′) β (up zero c y e) ≡ ψ (nd (sΩ k) h) o B j (inc c″ v″) β (up zero c y e)` | `up` 行在 x 为零时与指定孩子无关 | YiSupCheck | 定理 |
| `up-no-sep` | `… hd (proj₁ (ψ … (inc c₁ (w c₁)) β (up zero c y e))) ≡ true → hd (proj₁ (ψ … (inc c′ (w c′)) β (up zero c y e))) ≡ false → ⊥` | 任何布尔观察在这族探针上不分离 | YiSupCheck | 定理 |
| `top-drop` | `qOf (kp (Nx a) (Ok-Nx a oa) top (inc c′ (wL a w c′))) ≡ nothing` | `w ∙ lift` 路径上顶槽位对一切 c′ 不保留 | YiSupCheck | 定理 |
| `sup-head` | `isLim (proj₁ (ψ (Nx a) (Ok-Nx a oa) B j (inc c′ (wL a w c′)) β (sup tt x Y e)))` | 这族路径上 `sup` 行的头对一切 c′ 是 ℕ 极限 | YiSupCheck | 定理 |

前提可满足：`sup-tail` 的前提由 `tl-tw` 满足，`sup-fb` 的前提由 `tl-⊕` 满足。

#### 5. 翻译账

- **来自记号的**：目标形状 "底该是 ψ_j(Ω_Ω) = sup_z ψ_j(Ω_z)" 读自记号（R15 用记号做的诊断）。把 Ω 形状层号的 Ω 树写成 "对孩子取上确界" 的专门结点，也是照这个读法。
- **由树的要求逼出的**：
  - 取尾部 `c′ + z` 而不是全体孩子：因为 c 与 c′ 不可比较（`branch→wdec`、`hand→wdec`），只有 `c′` 与 `c′ + z` 之间有字面路径。
  - 尾部路径字段与 `↑+`：折叠要路径 `j ≤ h (c′ + z)`。
  - 字段 `Q`：让 `sup` 只在 Ω 形状层号上存在，否则第 0 层与后继、ℕ 极限形状都要补行。
  - `◃p` 只取 x：单调四行只需要 "x 的折叠 ◃ 第一支的折叠"。
- **新增脚手架**：可选的尾部字段是为了读回层号仍带证据（`OkO↑`）；它不是序数值需要的，是 "读回层号没有沿 `+` 的单调" 带来的。
- **验收**：只用形状（`refl`），没有用 `Lab`，也没有值。
- **这一步的性质（判断）**：没有为闭包定理加专属前提；但只修了 "左边是 `sup` 形" 的情形，另留三处回退（§1 表前三行）。

#### 6. 偏离与事故；没有读的东西

- **思路 2 没有做**。纸面判断：证据是 "x 的每个左加项的孩子层号 ≥ h c"，要写成对树 x 的谓词并存进 `up` 结点，一般签名 `Sg` 里要加路径关系，树与该谓词要一起归纳定义；Ω 结点的分支也要带证据。没有试编译，只写 "未做"。
- 第一次冷编用了 `/usr/bin/time -l`，沙箱拒绝 `sysctl`，`time` 自己返回 1（agda 日志正常）。删自己的接口后改用 `+RTS -s<文件>` 重跑，上表是这一次的结果。
- 为校准切片脚本，对 `YiRWFold` 跑了一次 `--html`（输出到自己的临时目录）。没有删也没有用 `--ignore-interfaces`；它只读已有接口。
- 四个块文件是把 `YiRW*` 复制后用脚本改的，`YiSupCheck` 的前半是 `YiRWCheck` 的复制加三处模式修改。
- 没有做值的有限测试。
- **没有读、只凭转述的**：`YiLNBranch`、`YiLNFlat` 的代码；`YiAltCmp`、`YiAltFold`、`YiAltTest`（只读了 `YiAltCheck` 文首与 `no-sep` 附近）；`YiAbsObs` 只读了 `Sep`、`Row` 的字段、`Slot.full→dec` 与文首；`YiOmNegBranch` 读了全文，但它依赖的 `Link`、`At`、`Kept`、`K₂ω` 的定义没有读；IdeaLedger 的 V114 条目；F2 的 `YiLeg*`。记号侧的事实全凭 R15 回报。
- 没有碰同批其他路的文件，没有提交。
