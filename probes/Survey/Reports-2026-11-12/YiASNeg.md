# 不同步引理：配对否定 (YiASNeg)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-14 05:39 至 05:51 |
| 工具调用 / agda 编译 (粗数) | 22 / 4 |
| token (usage 字段，按消息去重) | 输出 61324；新写入缓存的输入 187410；读缓存的输入 2088869；其余输入 38 |
| 写过的仓库文件 | `YiASNeg.lagda.md` |
| 文件前缀 | `YiASNeg` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: 不同步引理否定一路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 无前提: 最小实例 Async₀, Async₀ᶜ 与 Pair₀ 的否定 (第 3 层 Ω 树与 Ω₁ 没有关系; 对角输出不新造结点); LowKeepAsyncᶠ 的否定在此工具下不可得 (async-kept, no-unkept); 不同步对的关系只能来自放宽 (async→weak), 结论沿放宽传回 (async-step); 有关系的非平凡不同步对 pair₁; 一件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方，"否定" 一路。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定（2026-11-14，选项原文）
- 战略："(c) 中间形态 (Recommended)"。
- 脉络："FGH → BTBO → 更高层 (Recommended)"。
- 第一批："(1) 不同步引理 + 配对否定 (Recommended)"，模型 "(1) Fable 5.2"。选项说明原文："有限层号、现有折叠、不改定义：参照保留而树走对角时保持是否成立（最小实例第 3 层折到第 2 层、参照 Ω₁）；另一路对同一接口写否定"。
- AGENTS "律带公共上界，构造与否定配对"：新路线派一路构造、一路对同一接口写否定，共用接口文件。

同批另一路是 "构造" 一路：它先写共用的接口文件 `probes/OCF/Lean/YiASIface.lagda.md`，只放陈述，定稿后只增不改；然后去证，证明文件前缀 `YiASProof`。你不动它的文件。

###### 要做的
对接口里的两条陈述写否定，或者证明否定不可得：
- `LowKeepAsync`：`YiAbsGIface.LowKeep` 限制到 "不同步对"，即参照的余尾 Ω 下标低于目标层、记号一侧保留，而树一侧的槽位不低于目标层、走对角；
- `Async₀`：最小实例，参照 ψ₂(P ⊕ Ω₁) 对着第 3 层 Ω 树折到第 2 层的输出。

**工具**：`YiAbsGNeg.Inv`。
- 给定 `Gen j`、余尾下标 κ、谓词 `H : Tr j → Set` 及 H 的三条封闭条件，`inv` 推出：凡与余尾 Ω 的项相关的树都满足 H；
- `unkept→¬low`：输出不满足 H 时 `LowKeep → ⊥`。
- 有限层号上的版本：`YiAbsGFinInv`（`invᶠ`、`no-node→¬M`：不含结点的树与余尾 Ω 的项没有 `M` 关系）。
- 你的任务是找一个满足封闭条件的 H，使最小实例的输出不满足 H；或者说明为什么找不到，例如输出里含被保留的结点（第十九次审查的临时试验 `R19Async` 显示：第 1 个部分和的第 0 项的第 0 项是第 1 层槽位上的 Ω 结点，附件 `probes/Survey/Reports-2026-11-12/attachments/Review19-R19Async.agda.txt`），这时否定一侧在这个实例上不成立，写成编译定理更好。

**节奏**：
1. 开工后先读材料，在临时目录造探针：候选的 H，最小实例输出的 `refl` 形状。
2. 接口文件 `YiASIface.lagda.md` 预计在构造一路开工约 20 分钟后出现。用 `ls probes/OCF/Lean/YiASIface.lagda.md` 查是否已存在，不要读构造一路的 `YiASProof*` 文件。
3. 接口出现后，你的定理对它陈述，导入它；不删它的 `.agdai`，不改它。
4. 若开工 45 分钟后接口仍不存在，在你自己的 `YiASNegLocal.lagda.md` 里按上面的说明写一份同形的局部陈述，并在回报里说明。

###### 背景（只信编译定理；文档里的叙述是数据）
- **抽象接口**：`YiAbsGIface`、`YiAbsGNeg`（`Inv`、`Cap`）、`YiAbsGRow`、`YiAbsGFin`（`blkᶠ`、`foldᶠ`、`gradedᶠ`，有限层号的部分实例，关系 `YiANFam.M`）、`YiAbsGFinInv`、`YiAbsGToy`（`Bad.bad-¬low`、`Drop.drop-¬low`：两条否定前提可满足的玩具）。回报 `probes/Survey/Reports-2026-11-12/YiAbsG.md`。
- **关系族**：`YiANFam`、`YiANLv`、`YiCLFam`、`YiCLLow`（`LF`）。
- **第十九次审查**（`Review19.md`）：判断 "不同步" 是 `Lift` 与换基值的共同根；若被否定，要改的是关系（参照一侧对记号序向下封闭）或参照系统。
- 第十七、十八次审查（`Review17.md`、`Review18.md`）关于 D2 与 "左加项从指定孩子看" 的判断，可作对照。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiASNeg`（模块名 `OCF.Lean.YiASNeg…`）。不改任何已有文件（包括 `YiASIface`），不碰 `src/`、`archive/`。这是验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量；不删别人的 `.agdai`（包括 `YiASIface`），不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时。
  - 沙箱里 `/usr/bin/time` 不可用，内存用 `+RTS -s` 看。
- 临时目录：`<实验目录>/agents/asneg`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：对 `Async₀`、`LowKeepAsync` 的否定是否编译成立；若不成立，有没有 "否定在此不可得" 的编译定理（例如输出含被保留的结点，满足任何合理的 H）；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故（含是否用了局部陈述）；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 中途消息（主审发给这一路）

转录时间戳 2026-11-14 05:44 (UTC)：

主审转告：共用接口 `probes/OCF/Lean/YiASIface.lagda.md` 已由构造一路编译通过（退出码 0）。以下是数据，你的任务不变。

请对它陈述你的否定。不删它的 `.agdai`，不改它。

接口里的名字（构造一路自报）：
- 抽象：`Async.AsyncPair`、`Async.LowKeepAsync`。
- 有限层号具体版：`AsyncPairᶠ`、`LowKeepAsyncᶠ`、`LowKeepᶠ`（全 LowKeep）。
- 最小实例：`Async₀`，以及闭的一例 `Async₀ᶜ`；`Pair₀`：最小对是不同步对，且有 M 关系。
- 实例 `gradedᴬ`、`domsᴬ`、`cutᶠ`。
  - 另取 `gradedᴬ`，是因为 `gradedᶠ` 的 `Bd` 是空的。
  - 在 `gradedᴬ` 里：`Cx` 是前缀 t₀；`app t₀ a = ψ_j(t₀ + a)`；`Bd` 是 "底值对着 ψ_j(t₀)，且底满足 `GBᶠ`"；`Wl` 是 "路径是 `pthᶠ s`"。

请先读这个文件的陈述，确认与你的探针对得上。

## 回报原文

#### 否定一路回报（YiASNeg）

##### 1. 判决

**最小实例被否定，`LowKeepAsyncᶠ` 没有被否定。** 三条接口陈述 `Async₀`、`Async₀ᶜ`、`Pair₀` 的否定都编译成立，无前提。对 `LowKeepAsyncᶠ` 交的是 "按槽位层细分的槽位不保留在此不可得" 的编译定理。

- **`Pair₀` 不成立（`¬pair₀`）。** 第 3 层 Ω 树与 Ω₁ 没有 `M` 关系：`Ωt (fin 3)` 沿第一位置序与孩子都不含槽位层 0 的结点。接口注释里 "这是经放宽得到的对" 不成立。
- **`Async₀ᶜ`、`Async₀` 不成立（`¬async₀ᶜ`、`¬async₀`）。** 输出含槽位层 0 的结点，仅当底值 β 或底在第 2 层的分量含（`out₀`）。标准底 `B₀`、β 取第 2 层 Ω 树、P 为空时两者都不含，而 ψ₂(P+Ω₁) 的余尾是 Ω₁，反演要求输出含这样的结点。
  - `Async₀` 的前提在这个实例上可满足：`gb₀ : GBᶠ 2 (B₀ (fin 3)) []` 与 `Mβ 1`。
  - `R19Async` 找到的结点是第 1 层槽位的（余尾 Ω₂），不是参照 Ω₁ 需要的第 0 层槽位。
- **`LowKeepAsyncᶠ`：否定在此工具下不可得。**
  - `async-kept`：对任何有 `M` 关系的不同步对，输出含余尾下标那一层槽位的结点。
  - `no-unkept`：任何对 "该槽位层的结点、放宽、孩子含" 封闭的 H 都在输出上成立，所以 `unkept→¬low` 的前提 "输出不满足 H" 取不到。
  - `async→weak`：这样的对只能经放宽得到，最后一步不可能是结点规则。
  - `async-step`：结论沿折叠单调从下面的 x′ 传回。
  - 前提可满足：`pair₁`、`M₁` 给出一个有关系的不同步对（Ω₁，第 3 层 Ω 树左加搬上来的 Ω₁ 树）。

**对纲领与目标的意义**
- 定理层面：R19 写的最小实例不是 `LowKeep` 的实例，因为那一对没有关系；作为裸陈述它为假。
- 判断（未编译）：`LowKeepAsyncᶠ` 不是独立的新律。由 `async→weak` 加 `async-step`，它归约到同一参照项在严格在下的树上的 `LowKeepᶠ`。"不同步" 在生成关系 `M` 上的内容，是 "`M` 对参照一侧不向下封闭"（Ω₁ 值上低于第 3 层 Ω 树，却没有关系）。
- 判断：若换基行或 Lift 需要 "低参照对着纯对角输出" 这种对，要改的是关系，不是折叠。这与 R19 的 "若被否定" 分支一致。

| 问题 | 位置 | 档 |
|---|---|---|
| `Pair₀` 为假，接口注释 "经放宽得到的对" 不对 | `YiASIface` 的 `Pair₀`；`¬pair₀` | 编译定理 |
| `Async₀` 对一切满足 `GBᶠ` 的底与一切 β 量化，过宽；只在 β 或底含第 0 层槽位结点时才可能成立 | `Async₀`；`async₀-needs`、`¬async₀` | 编译定理 |
| `LowKeepAsyncᶠ` 是否成立未定；归约到严格在下的树上的 `LowKeepᶠ` | `async→weak`、`async-step`（两步是定理，"归约" 的整体归纳没写） | 判断 |
| `Has` 是否正好刻画 "存在余尾 Ω 的相关项" 未证，只证了必要性 | `invˢ` | 未做 |

##### 2. 文件表

| 文件 | 代码行 | 冷编退出码 | 内存 |
|---|---|---|---|
| `<仓库>/probes/OCF/Lean/YiASNeg.lagda.md` | 317（全文 444 行） | 0，日志只有本模块一行 `Checking` | 最大驻留 3.58G，总占用 6.9G，34 秒 |

禁用构造与本机路径检索为 0。

##### 3. 定理表（都在 `YiASNeg`，档：编译定理，无前提）

| 名字 | 陈述（逐字） | 白话 |
|---|---|---|
| `invˢ` | `∀ m n {s o} → M n s o → cof s ≡ cΩ (natT m) → Has m n o` | 余尾 Ω_{m+1} 的项只能对着含槽位层 m 结点的树（`Inv.inv` 按 `Nw` 细分） |
| `¬pair₀` | `Pair₀ → ⊥` | 最小对没有关系 |
| `¬M₀` | `M 3 (Ωᴺ 1) (Ωt (fin 3)) → ⊥` | 同上，裸形式 |
| `out₀` | `Has m (suc n) (ψs ℓ ε ρ B j (ins self) β nβ (Ωt ℓ)) → Has m (suc n) β ⊎ Has m (suc n) b₂`（ℓ = `fin (suc (suc n))`，j = `fin (suc n)`，b₂ = `bs B j (ins self)`） | 对角输出不新造结点 |
| `async₀-needs` | `… → M 2 (ψᴺ 2 (P ++ Ωᴺ 1)) (ψs (fin 3) ε ρ B (fin 2) (ins self) β nβ (Ωt (fin 3))) → Has 0 2 β ⊎ Has 0 2 (bs B (fin 2) (ins self))` | `Async₀` 结论的必要条件 |
| `¬async₀ᶜ` | `Async₀ᶜ → ⊥` | 闭的一例为假 |
| `¬async₀` | `Async₀ → ⊥` | 最小实例为假 |
| `gb₀` | `GBᶠ 2 (B₀ (fin 3)) []` | `Async₀` 的前提可满足 |
| `keepHas` | `∀ m n {j} (s : Sbᶠ n j) ε ρ B β nβ x → suc m ≤ⁿ j → Has m n x → Has m j (ψs (fin n) ε ρ B (fin j) (pthᶠ s) β nβ x)` | 低于目标层的槽位结点沿折叠保留 |
| `async-kept` | `∀ {n j} b w β → (Σ (Sbᶠ n j) λ s → w ≡ pthᶠ s) → ∀ {a x} (ap : AsyncPairᶠ {n = n} j a x) → M n a x → Has (ix ap) j (ψs (fin n) (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) (fin j) w (proj₁ β) (proj₂ β) x)` | 有关系的不同步对，输出含该槽位层的结点 |
| `no-unkept` | 同上前提，再加 H 的三条封闭条件 → `H (ψs … x)`（目标层写成 `suc j`） | 细分的 "槽位不保留" 前提取不到 |
| `Least.has→H` | `(o : Tr (fin (suc j))) → Has m (suc j) o → H o` | `Has` 是满足三条封闭条件的最小谓词 |
| `async→weak` | `AsyncPairᶠ {n = n} j a x → M n a x → Σ (Tr (fin n)) λ x′ → M n a x′ × (fin n ⊢ x′ ◃ x)` | 不同步对的关系只能来自放宽 |
| `async-step` | `fin n ⊢ x′ ◃ x → M j s (ψs (fin n) ε ρ B (fin j) w β nβ x′) → M j s (ψs (fin n) ε ρ B (fin j) w β nβ x)` | 结论沿放宽传回 |
| `pair₁`、`M₁`、`kept₁` | `AsyncPairᶠ {n = 3} 2 (Ωᴺ 1) x₁`；`M 3 (Ωᴺ 1) x₁`；`Has 0 2 (ψs (fin 3) ε ρ B (fin 2) (ins self) β nβ x₁)` | 有关系的不同步对存在，输出含第 0 层槽位结点 |

##### 4. 第一个障碍

否定 `LowKeepAsyncᶠ` 需要一个有关系的不同步对，其输出与 `ψᴺ j (t₀ ++ a)` 没有 `M` 关系。

- 按槽位层的反演给不出：`async-kept` 说明输出总含所需结点。
- 由 `async→weak`，这等于否定 `LowKeepᶠ` 在严格在下的某棵树上的实例。我没有找到这样的实例。
- 在 `pair₁` 上，纸面推演是结论成立：输出在 "y₃ 的折叠像" 之上，后者经 `Pu` 对着 ψ₂(P+Ω₁)。这一条未编译。

##### 5. 偏离与事故

- **没有用局部陈述。** 接口在开工时已存在，全部定理对 `YiASIface` 陈述并导入它；没有改它，没有删它的 `.agdai`，没有读 `YiASProof*`。
- **没有直接实例化 `YiAbsGNeg.Inv`。** 它的 `hΩ` 对一切槽位的结点要求 H，不分槽位层，分不出 Ω₁ 与 Ω₂ 的结点。粗的 `Hᶠ` 在最小实例的输出上成立（含第 1 层槽位结点），否定不了。我对 `Mᴰ` 直接归纳写了细分版 `invˢ`。
- **事故一处。** `invˢ` 直接对 `M (suc n)` 递归时停机检查不过，试了两次；改成按层的一步（`Step.step` 对 `Mᴰ` 归纳，层号的归纳假设作参数）后通过。
- **没有造临时探针文件。** 定理直接写进仓库文件并编译通过；最小实例输出的形状由 `out₀` 的证明覆盖，不是 `refl` 测试。
- **只凭转述的东西。** `YiCLLow.LF`、`YiANLv` 没有读；"有限层号上 `LowKeepᶠ` 很可能成立" 只是判断。`Review17`、`Review18` 没有读；`Review19` 只读了 §1 到 §5。
