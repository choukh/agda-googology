# 封闭关系加 ℕ 极限规则 (YiMH)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-14 08:11 至 08:22 |
| 工具调用 / agda 编译 (粗数) | 32 / 12 |
| token (usage 字段，按消息去重) | 输出 44122；新写入缓存的输入 159069；读缓存的输入 2959870；其余输入 50 |
| 写过的仓库文件 | `YiMHFin.lagda.md`, `YiMHLean.lagda.md`, `YiMHRel.lagda.md` |
| 文件前缀 | `YiMH` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: 第四十批 YiMH 返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 无前提: 带 ℕ 极限规则的封闭关系 M̂ (对任意基础关系); 孩子取 ω 时兄弟孩子那一支对着 ψ₂(Ω_ω) (synˢ, 另 synᵗ); 精简块上 Leaf, 折到低层与折到自身的保持 (leaf̂, lowKeep̂, selfKeep̂); F2 块上接口的 Lim, Leaf, LowKeep 与带条件出口 (limᴴ, leafᴴ, lowKeepᴴ, exitᴴ); 记号引理是已有等式的组合 (cof-app, fsn-app); 出口条件在合成的推导折到第 0 层时不成立 (¬ex-low0: 见证项 ψ₀(ψ₂(Ω₃)) 非标准形); 三件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定与原则（2026-11-14，选项原文或原话）
- 主线 "经指定孩子" 那一行："兄弟孩子 c′ + c (Recommended)"，即 `probes/OCF/Lean/YiRBSib` 的折叠。
- 本批本路是 "(1) 封闭的关系加 ℕ 极限规则 (Recommended)"，选项说明原文："台账 V161：把 ω 处的逐项结论合成一条，并核接口的 Leaf、LowKeep 与出口是否仍成立；验收一侧，不改定义"。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"。本路只在验收一侧。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

###### 已有的东西（主审复核过；先读，不重证）
- **关系**：`YiCLFam.M n`，精简块上层号 `fn n` 的记号直连关系，与折叠无关。
  - 未封闭时太严：`YiRLNeg.negˢ`（孩子取 1 处判据为假）、`YiASProofPair.no-leaf`。
  - 按项序封闭的形状：F2 块上 `YiDCRel.M̃ n s x = Σ t, (s ≤ᵀ t) × M n t x`，配 `leafᴰ`、`lowKeepᴰ`、`app≤`；出口 `YiDCExit.exitᴰ`（见证项是可数标准形时），`nf-low`。
- **逐项结论**（兄弟孩子，精简块）：`YiRLCrit.ω̃ˢ : ∀ {c} → Can c → M⁰ ωᵀ c → ∀ k → Σ E.T λ t → (fsn (ψᴺ 2 (E.Ωt ωᵀ)) k ≤ᵀ t) × M 2 t (proj₁ (gˢ c))`；还有 `fiñˢ`、`limSL`、`fsnω`。
- **新折叠上的保持**：`YiRBFam`（`Self.PF`、`LF`、`sΩ-LF`）。
- **抽象接口**：`YiAbsGIface`（`Laws`：`Leaf`、`LowKeep`）；带条件出口的充分性 `YiExSuff`（`Exit₀`）及实例 `YiExInst`。
- 回报：`probes/Survey/Reports-2026-11-12/YiRL.md`、`YiDC.md`；台账 `probes/Survey/IdeaLedger.md` V156、V161。

###### 要做的（按序；推进的是 "封闭关系上的律与出口"）
0. **最小实例检查**，在临时目录，几十行：
   - 写出带 ℕ 极限规则的封闭关系（暂名 `M̂`）：基础情形是 `M̃` 那样的项序封闭；极限情形是 `cof s ≡ cω → (∀ k → M̂ n (fsn s k) x) → M̂ n s x`。
   - 确认：由 `ω̃ˢ` 得 `M̂ 2 (ψᴺ 2 (E.Ωt ωᵀ)) (proj₁ (gˢ c))`（对 `Can c`、`M⁰ ωᵀ c`）这一步类型正确、可证。
   - 检查折到低层的保持要的记号引理在小实例上成立：`fsn (ψᴺ j (t₀ ++ a)) k` 与 `ψᴺ j (t₀ ++ fsn a k)` 在 `cof a ≡ cω` 时的关系。先查 `OCF/Align/EboLean*` 里有没有现成的。
   - 若某条不成立，就停下回报。
1. **合成**：交 "孩子取 ω 时那一支对着 ψ₂(Ω_ω)" 在 `M̂` 上的定理（兄弟孩子）。
2. **律**：在 `M̂` 上证 `Leaf`，以及折到低层的保持（由 `YiRBFam.LF` 与记号引理组合）。
3. **出口**：第 0 层的 `M̂ 0 s x` 推出参照值不高于 `read x`，条件照 `exitᴰ`（标准形等），极限情形用推导 `HC` 的 `hω`。能接进 `YiExSuff.Exit₀` 就接。
4. 说明与已有结果的关系：新的还是重证。

**纪律**（作者同意的，必须照做）：
- 动手证一般形式之前，先用临时文件检查前提可满足。
- 已有引理先检索再写，不重证。
- 若某一步要改树、折叠或合法性的定义，停下回报。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiMH`（模块名 `OCF.Lean.YiMH…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰在跑的另两路的前缀 `YiLR`、`YiSM`。验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。另两路也在编译，不用 `--ignore-interfaces`，只删自己模块的 `.agdai`。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量，执行前核对路径。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时。
  - 堆墙：不要在具体推导上直接比较两个 `Rt`；具体参照树放 `opaque`；见 `probes/Survey/EBOHandbook.md` 第 4 节。
  - 沙箱里 `/usr/bin/time` 不可用，内存用 `+RTS -s` 看。
- 临时目录：`<实验目录>/agents/mh`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽；第 0 步触发的停止条件。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：第 0 步的结论；合成、律、出口各到哪一步；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 1. 判决

**第 0 步（临时文件 `T0.agda`，退出码 0）**：三项都成立，没有触发停止条件。
- 带 ℕ 极限规则的封闭关系 `M̂` 写得出，由 `ω̃ˢ` 加一步极限规则得到 `M̂ 2 (ψᴺ 2 (E.Ωt ωᵀ)) (proj₁ (gˢ c))`，类型正确。
- 记号引理是等式，不必新证：`cof a ≡ cω` 时 `cof (ψᴺ j (t₀ ++ a)) ≡ cω`，且 `fsn (ψᴺ j (t₀ ++ a)) k ≡ ψᴺ j (t₀ ++ fsn a k)`。它是 `YiMENote` 的 `cofψω`、`cof++ω`、`fsnψω`、`fsn++` 的组合，`YiRBFam.LF` 的 `mL` 情形已在用。
- 没有要改树、折叠或合法性定义的地方。

**各步到哪里**（都是编译定理，无前提）：
- **合成**：做成（`synˢ`，另有目标层 ⊕ c 的 `synᵗ`）。
- **律**：`Leaf`、折到低层的保持、折到自身的保持、沿 `◃` 放宽都做成；极限律就是构造子 `l̂`。F2 块上把 `Lim`、`Leaf`、`LowKeep` 填进了 `YiAbsGIface.Laws`。
- **出口**：带条件的出口做成（`exit̂`、`exitᴺ`），极限情形用 `hω`；F2 块上接进了 `YiExSuff.Exit₀`（`exitᴴ`）。条件 `Ex` 对推导递归：每片叶子上参照与见证项是标准形、见证项可数。
- **条件的可满足性**：有一例成立（`exit-ω̂`），也有一例编译否定（`¬ex-low0`）：`synˢ` 以空前缀折到第 0 层的那个推导上 `Ex` 不成立。

**对纲领与目标的意义**：全部在验收一侧，树、折叠、合法性一行未改，不进成品。V161 的 "合成一条" 与 "律是否仍成立" 两问答案是肯定的。出口仍是带条件的，条件在与 ψ₂(Ω_ω) 有关的推导上没有任何成立的实例；障碍还是 V157 (ii)，没有推进。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| `Ex` 在 `synˢ` 以空前缀折到第 0 层的推导上不成立（见证项 ψ₀(ψ₂(Ω₃)) 不是标准形） | `YiMHLean.¬ex-low0` | 编译定理；只否定这一个推导上的条件 |
| 使这类见证项成为标准形的前缀要不低于 Ω_ω，而有限层号的关系族里底的条件 `GB n B t₀` 在这样的前缀上能否成立 | 无 | 判断，未检查 |
| `M̂` 对项序向下封闭没有证（极限情形要记号一侧的共尾引理；`YiCFCofin.cofin` 可能可用） | `YiMHRel` 文首 | 未做 |
| 精简块没有 `Graded` 实例，所以精简块上的律是照接口形状写的具体陈述，`Exit₀` 只在 F2 块上接了 | `YiMHLean`、`YiMHFin` | 事实 |
| 保持律里底与底值的前提仍用未封闭的 `M` 陈述（与 `gradedᴰ` 的 `Bd` 相同） | `lowKeep̂`、`selfKeep̂`、`gradedᴴ` | 事实 |
| `Lift`、ℕ 极限层号上的 `Rd`、其余律（`Zero`、`Succ`、`Node`、`Emb`、`UpKeep`）没有做 | 无 | 未做 |

#### 2. 文件表

三个文件都在 `<仓库>/probes/OCF/Lean/`，删自己的接口后按依赖顺序冷编，日志里各只有自己模块的一行 `Checking`；禁用构造与本机路径检索为 0。

| 文件 | 代码行（非空） | 总行 | 冷编退出码 | 内存（`+RTS -s`） |
|---|---|---|---|---|
| `YiMHRel.lagda.md` | 69 | 116 | 0 | 2350 MiB |
| `YiMHLean.lagda.md` | 79 | 129 | 0 | 2479 MiB |
| `YiMHFin.lagda.md` | 35 | 61 | 0 | 2343 MiB |

日志在 `<实验目录>/agents/mh/`（`*.cold.log`）。

#### 3. 定理表（全部是编译定理，无前提）

**`YiMHRel`（对任意基础关系 `R : E.T → X → Set`）**

| 名字 | 陈述 | 白话 |
|---|---|---|
| `M̂` | `ĉ : s ≤ᵀ t → R t x → M̂ R s x`；`l̂ : cof s ≡ cω → (∀ k → M̂ R (fsn s k) x) → M̂ R s x` | 项序封闭加 ℕ 极限规则 |
| `cof-app` | `∀ j t₀ a → cof a ≡ cω → cof (ψᴺ j (t₀ ++ a)) ≡ cω` | 记号引理，余尾 |
| `fsn-app` | `∀ j t₀ a k → cof a ≡ cω → fsn (ψᴺ j (t₀ ++ a)) k ≡ ψᴺ j (t₀ ++ fsn a k)` | 记号引理，基本列 |
| `keep` | `∀ j t₀ {x y} → (∀ {a} → R a x → R′ (ψᴺ j (t₀ ++ a)) y) → ∀ {a} → M̂ R a x → M̂ R′ (ψᴺ j (t₀ ++ a)) y` | 基础关系上的保持提升到 `M̂` |
| `weak` | `(∀ {t} → R t x → R t x′) → ∀ {s} → M̂ R s x → M̂ R s x′` | 放宽提升到 `M̂` |
| `All`、`all-keep⁻`、`all-keep⁺` | `All P (keep {R′ = R′} j t₀ f m)` 与 `All (λ s t → P (ψᴺ j (t₀ ++ s)) (ψᴺ j (t₀ ++ t))) m` 互推 | `keep` 之后的叶子是 (ψ_j(t₀+s), ψ_j(t₀+t)) |
| `Ex` | `Ex = All Leafᴺ`，`Leafᴺ s t = NF s × NF t × Ctbl t` | 出口条件 |
| `exit̂` | `(v : X → L.Ordᶜ L.zero) → (∀ {t x} → R t x → (h : HC t) → Rt h ≼ v x) → ∀ {s x} (m : M̂ R s x) → Ex m → (h : HC s) → Rt h ≼ v x` | 第 0 层出口，极限处用 `hω` |

**`YiMHLean`（精简块，`M̂ᴺ n = M̂ (YiCLFam.M n)`）**

| 名字 | 陈述 | 白话 |
|---|---|---|
| `synˢ` | `∀ {c} → Can c → M⁰ ωᵀ c → M̂ᴺ 2 (ψᴺ 2 (E.Ωt ωᵀ)) (proj₁ (gˢ c))` | 孩子取 ω 时兄弟孩子那一支对着 ψ₂(Ω_ω) |
| `synᵗ` | `∀ {c} → M⁰ ωᵀ c → M̂ᴺ 2 (ψᴺ 2 (E.Ωt ωᵀ)) (proj₁ (gᵗ c))` | 同上，目标层 ⊕ c 的写法 |
| `weakᴺ` | `∀ n {s x x′} → M̂ᴺ n s x → fn n ⊢ x ◃ x′ → M̂ᴺ n s x′` | 沿第一位置序放宽 |
| `leaf̂` | `∀ {m} n → m ≤ⁿ suc n → M̂ᴺ (suc n) (Ωᴺ m) (proj₁ (Ωt (fn (suc n))))` | `Leaf`，含松弛的层号 |
| `lowKeep̂` | `∀ {n j} (o : Ok (fn (suc n))) (r : Rb (fn (suc n))) (s : Tp n j) (t₀ : E.T) (B : Base (fn (suc n))) → GB n B t₀ → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β) → ∀ {a x} → M̂ᴺ (suc n) a x → M̂ᴺ j (ψᴺ j (t₀ ++ a)) (proj₁ (ψ (fn (suc n)) o r B (fn j) (tp s) β x))` | 折到低层的保持（`LF` 加 `keep`） |
| `selfKeep̂` | `∀ N o r B β {P₀} → M (suc N) (ψᴺ (suc N) P₀) (proj₁ β) → ∀ {a x} → M̂ᴺ (suc N) a x → M̂ᴺ (suc N) (ψᴺ (suc N) (P₀ ++ a)) (Self.F N o r B β x)` | 折到自身的保持 |
| `exitᴺ` | `∀ {s x} (m : M̂ᴺ 0 s x) → Ex m → (h : HC s) → Rt h ≼ readRW x` | 精简块的第 0 层出口 |
| `ω̂`、`ex-ω̂`、`exit-ω̂` | `M̂ᴺ 0 ωᵀ ωᶜ`；`Ex ω̂`；`(h : HC ωᵀ) → Rt h ≼ readRW ωᶜ` | 条件可满足的一例：用到极限规则，见证项错位 3 |
| `low0` | `(o : Ok (fn 2)) (r : Rb (fn 2)) (s : Tp 1 0) (B : Base (fn 2)) → OKB B → (β : Tr⁺ (fn 0)) → M⁰ (Ωᴺ 0) (proj₁ β) → ∀ {c} → Can c → M⁰ ωᵀ c → M̂ᴺ 0 (ψᴺ 0 (ψᴺ 2 (E.Ωt ωᵀ))) (proj₁ (ψ (fn 2) o r B (fn 0) (tp s) β (proj₁ (gˢ c))))` | 合成的推导以空前缀折到第 0 层 |
| `¬nf-wit` | `NF (ψᴺ 0 (ψᴺ 2 (Ωᴺ 3))) → ⊥` | ψ₀(ψ₂(Ω₃)) 不是标准形 |
| `¬ex-low0` | `∀ o r s B ok β hβ {c} (cc : Can c) (l : M⁰ ωᵀ c) → Ex (low0 o r s B ok β hβ cc l) → ⊥` | 出口条件在这个推导上不成立 |

**`YiMHFin`（F2 块，`gradedᴴ = record gradedᴬ { R = λ n → M̂ (M n) ; Rd = Rdᴰ }`）**

| 名字 | 陈述 | 白话 |
|---|---|---|
| `of̃` | `∀ {n s x} → M̃ n s x → M̂ (M n) s x` | 旧的封闭关系嵌入新的 |
| `limᴴ` | `Laws.Lim gradedᴴ domsᴬ` | 接口的极限律 |
| `leafᴴ` | `Laws.Leaf gradedᴴ domsᴬ` | 接口的 `Leaf` |
| `lowKeepᴴ` | `Laws.LowKeep gradedᴴ domsᴬ` | 接口的 `LowKeep` |
| `exitᴴ` | `ExSuff.Exit₀ gradedᴴ domsᴬ`，条件是 `Ex` | 接进带条件出口的充分性定理 |

#### 4. 与已有结果的关系

**新的**
- `M̂` 的定义与极限规则。
- 接口的 `Lim` 律在封闭关系上成立（`YiDCRel` 没有填这一条）。
- 出口的极限情形（`exit̂` 的 `hω` 一支）。
- 叶子谓词 `All` 与它对 `keep` 的两个方向。
- 精简块、兄弟孩子折叠上的封闭关系的律：`YiDC*` 只在 F2 块上做过。
- 边界 `¬ex-low0`。

**一步组合，不是新数学**
- `synˢ` 是 `ω̃ˢ` 加一步 `l̂`。
- `lowKeep̂`、`selfKeep̂` 是 `LF`、`Self.PF` 加 `keep`。
- `leaf̂`、`leafᴴ` 照 `leafᴰ`；出口的叶子情形照 `exitᴰ`。
- `¬nf-wit` 与 `YiDCExit.¬nf₂` 同一类。

没有重证已有引理。

#### 5. 第一个障碍

出口条件 `Ex` 在与 ψ₂(Ω_ω) 有关的推导上的可满足性，精确到引理是 `NF (ψᴺ 0 (t₀ ++ ψᴺ 2 (Ωᴺ (3+k))))`。
- `t₀ = []` 时为假（`¬nf-wit`，k = 0）。
- 缺的是下面两者之一，都没有做：
  - 非标准形见证项上 "项序推出值序" 的记号引理（V157 (ii)），用来替换 `exit̂` 叶子情形里的 `mono≤ⁿ`。
  - 一个前缀 t₀ 不低于 Ω_ω 且 `GB n B t₀` 成立的实例；这要 ℕ 极限层号上的关系族，`YiCLFam.M` 只有有限层号。
- 档：`¬ex-low0` 是编译定理；"缺的是这两者之一" 是判断。

#### 6. 偏离、事故、没有读的东西

**偏离**
- 多做了一个 F2 块上的文件 `YiMHFin`，因为精简块没有 `Graded` 实例，`Exit₀` 只能在那里接。
- 多交了 `synᵗ`、`selfKeep̂`、`weakᴺ`，各一行。
- 关系写成对任意基础关系的一般形式，两个块共用。

**事故**
- `YiMHRel` 第一次编译退出码 154：Agda 内部错误（`LeftInverse.hs:222`，`__IMPOSSIBLE__`），出在 `all-keep⁻`、`all-keep⁺`。把隐式参数 `{R′}`、`{P}` 显式写出并把 `λ k →` 改成参数后通过；没有换选项。
- 自己的两个文件有两次是用脚本改的，没有用编辑工具；没有动任何已有文件。

**没有读、只凭简报或台账引用的**
- `Reports-2026-11-12/YiRL.md`、`YiDC.md`：只读了台账 V156、V157、V161 的行。
- `YiAbsGSuff`、`EBOHandbook.md` 第 4 节。
- `YiRBSib` 折叠的定义本身、`YiASProofLow.LFᶠ`、`YiCFCofin.cofin`：只看了签名或文首。
