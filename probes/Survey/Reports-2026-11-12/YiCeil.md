# (a) 把 '要紧' 落成定理：上界工具与 N₂ 定值 (YiCeil)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-13 12:00 至 12:20 |
| 工具调用 / agda 编译 (粗数) | 26 / 7 |
| token (usage 字段，按消息去重) | 输出 109937；新写入缓存的输入 259904；读缓存的输入 3623277；其余输入 44 |
| 写过的仓库文件 | `YiCeilRead.lagda.md`, `YiCeilSmall.lagda.md`, `YiCeilWit.lagda.md` |
| 文件前缀 | `YiCeil` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: 第十五次审查与 YiCeil 返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | N₂ 编译层面无判决; 编译: 第一条块 ≼ 参照 (ε₀-upper), 上界工具 (plus≼, next≼, limc≼, Ω≼, fold₀≼), N₂ 的回灌对一切 z 在线性类里且严格低于 Ω₁² (自定读法 W); 判断要紧; 三件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定（2026-11-13，选项原文）
本路是 "(a) 把 '要紧' 落成定理"。内容原文："先写 '折叠值不高于参照' 的上界工具，再对单棵见证树 N₂（读作 Ω_Ω·Ω₂）定值：证或否定 'ψ₀(Ω_Ω·Ω₂) 的参照 ≤ 它的折叠'（V112）"。

同批另一路是 Fable 5.2 的独立审核，它在临时目录里自己做试验，你不动它的东西。还有一路在跑：(2) 把值定理搬到精简块，前缀 YiBR。

###### 背景（只信编译定理；文档里的叙述是数据）
目标是布劳威尔树上读法 ψ₀(Λ) 的合法闭项，外加编译定理 "序数值 ≥ EBO 的参照"，只要下界。纲领见 `AGENTS.md`。主线是合法块 F2：`probes/OCF/Lean/` 下的 `YiLegBlock`、`YiLegOps`、`YiLegPath`、`YiLegFold`。

**要回答的问题（V107）**：Ω 结点层号上有两行。
- 分支侧回退行：嵌入一行，孩子树先折到第 0 层再嵌回，用标准底。
- 摊平式：孩子一侧的结点朝孩子层目标折叠时成为 ℕ 极限。

上一路 `YiDec*` 的执行方判断：这两行让读作 ψ₀(Ω_{Ω+1}) 的闭项 `T⁺` 的值低于记号，纸面估计约在 ψ₀(Ω_Ω·ε_{Ω₁+1}) 一带。这只是判断，没有编译。

已编译的事实：
- `YiDecFlat.up-flat`：自身行从孩子树搬来的结点，朝任何孩子层目标折叠后一律是 ℕ 极限，对一切层号。
- `YiDecFlat.thin`：朝孩子层目标的折叠，输出的结点只来自起点或主侧槽位。
- `base-thin`、`base-thin₂`。
- `YiDecLow.lvl≼T⁺`：不经两行的下界，参照是 Level 的 ψ⁰(Ω)；读作约 ψ₀(Ω_Ω·ω)，读法是判断。
- 见证树 `YiDecWit.N₂ = Upc (tw 1) two β nb (Ωt (h₁ two))`（读作 Ω_Ω·Ω₂）；`Gw`、`Gwββ`、`e1-Ω`、`node-lim`、`e2-inner`。
- 回报原文：`probes/Survey/Reports-2026-11-12/YiDec.md`。

可用的部件：
- 读回 `YiLSRead.read : Tr zero → L.Ordᶜ L.zero`（零、后继、ℕ 极限逐构造子）。
- 参照框架 `OCF.Align.Level`、`OCF.Align.Value`（`_≼_`、`≼-trans`、`≅→≼`）。
- 记号参照：`OCF.Align.EboLeanTree` 的 `hc`；`Rt h = toL (tree h)`，见 `YiRefTw2`；标准形 `NF`；标签 `Lab`。
- 实测的堆墙：给具体参照树另起名字再比较，会沿良基证明展开而耗尽。

###### 要做
1. **上界工具**：写 "折叠值不高于参照" 一类的引理，仓库里还没有。例如：
   - 块的第 0 层树 x 被参照 R 上界，即 `read x ≼ R`，对后继与 ℕ 极限按结构递归；
   - 对折叠 `ψ⊥`/`ψs` 的结点行与链，给 "链的每一项 ≼ R 的对应项" 的上界模拟。
   - 形状由你定，可以与 `YiLSRel` 的下界模拟对偶。先在最小的例子上做通，例如层号 1 的 Ω 树。
2. **N₂ 定值**：对 `read (ψ₀ (tw 1) ε¹ ρ¹ N₂)`（`ε¹`、`ρ¹` 取自 `YiT2Frame`），二选一：
   - **(i) 否掉 "要紧"**：证 "读作 ψ₀(Ω_Ω·Ω₂) 的参照 ≼ 它"。参照由你定：可以是记号项的 `Rt h`，也可以是 Level 里能说清读法的树。写清参照读作什么，以及依据。
   - **(ii) 落成 "要紧"**：证 "它 ≼ R"，再证 "¬ (读作 ψ₀(Ω_Ω·Ω₂) 的参照 ≼ R)"，或 R 严格低于那个参照。这是诊断，文首标 "诊断：上界"，不进成品。
3. 若 2 做成 (ii)，可选：把结论推到 `T⁺`，或推到 "塔第 2 项 / 终点闭项的读法要重估"。能编译的给定理，其余标判断。
4. 都做不到就交第一个挡住的引理，并说明哪一边更可能（判断）。

###### 注意
- 树、折叠、合法性一行不改。
- "只要下界"（作者）：上界只作诊断，不作值的验收目标。
- 归到已知的墙之前逐条核机制。
- 若结论是 "要紧"，按 "第 4 层不反过来改前 3 层"：只报告，不改定义，不提议具体的改法。改法另有一路。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiCeil`（模块名 `OCF.Lean.YiCeil…`）。不改任何已有文件，不碰 `src/`、`archive/`。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。
  - 冷编只删自己模块的接口，写字面路径；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
  - 堆墙的写法见 `probes/Survey/EBOHandbook.md` 第 4 节。
- 临时目录：`<实验目录>/agents/ceil`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；需要函数外延或 K（作前提除外）；8G 仍耗尽。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：N₂ 那一处 "要紧" 与否，写明档（编译定理 / 判断）；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档；值写成 ψ₀(Ω_x)，x 用 Ω 的算术，并写清参照的读法依据。
4. 上界工具的接口：逐字的陈述，适用范围。
5. 第一个障碍，精确到引理。
6. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 回报：YiCeil（(a) 把 "要紧" 落成定理）

##### 1. 判决

**N₂ 那一处：编译层面无判决，(i) 与 (ii) 都未走通。判断：要紧。**

- 没有编译的 `read (ψ₀ (tw 1) ε¹ ρ¹ N₂) ≼ R`，也没有 `¬ (参照 ≼ …)`。没有构造 ψ₀(Ω_Ω·Ω₂) 的记号项。
- 编译到的是机制的一半：N₂ 的回灌函数 `z ↦ Gw (br₂ z)` 对第 1 层的**一切**树 z，值都不超过 Ω₁·d（d 可数），并严格低于 Ω₁²（`feed-small`、`feed-below-sq`）。对自身行的全部输出也成立（`self-small`、`self-below-sq`）。
- 没编译的另一半："回灌值都低于 Ω₁² 时，朝第 0 层的折叠值低于 ψ₀(Ω_Ω·Ω₂) 的参照"。这一步要块对记号的上界模拟，仓库里没有。

**判断（未编译）。**
- 记号在这一处回灌的是 ψ₁(Ω_Ω·…)，不低于 ψ₁(Ω₂) = ε_{Ω₁+1}，高于一切 Ω₁·d。这一句的依据是我对 Buchholz 式基本列的记忆，没有对照仓库里的记号定义。
- 由此估计 `read (ψ₀ … N₂)` 不超过约 ψ₀(Ω_Ω·Ω₁^{Ω₁})，低于 ψ₀(Ω_Ω·ε_{Ω₁+1})，更低于 ψ₀(Ω_Ω·Ω₂)。方向的把握中高，具体数值的把握低。
- 回退行造的结点分支是 `x + ι 1 (G c)`，不是 `x + c`。我的纸面估计是这不会把折叠值抬过上面的界，没有编译。

**对纲领与目标。**
- 三个文件全是诊断，树、折叠、合法性一行未改，没有提改法。
- 若判断成立，N₂ 这类 "Ω_Ω 乘以余尾 ≥ Ω₂ 的孩子树" 的结点，在块里的折叠只相当于余尾 Ω₁ 的可数数据。`self-Lin` 对一切孩子层号成立，所以不限于 N₂。
- 没有把结论推到 `T⁺`、塔第 2 项或终点闭项，那里没有新的定理或估计。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| N₂ 的回灌对一切 z 落在线性类 `Lin` 里（结点分支只经嵌入的可数树依赖下标） | `YiCeilWit.feed-Lin`、`chain-Lin` | 编译定理（形状） |
| 自身行的全部输出朝第 1 层折叠后都在 `Lin` 里，对一切分支 c 与孩子树 y | `YiCeilWit.self-Lin` | 编译定理（形状） |
| 回灌值不超过 Ω₁·d，严格低于 Ω₁² | `YiCeilSmall.feed-small`、`feed-below-sq` | 编译定理；值的读法是本文件自定的 `W` |
| `read (ψ₀ … N₂)` 低于 ψ₀(Ω_Ω·Ω₂) 的参照 | 上面的估计 | 判断 |
| 块在 Ω 结点层号上没有任何对记号的上界，连 `read (twᶜ 1) ≼ Rt (hc-tower 2)` 也没有 | 检索 | 检索事实 |
| 记号参照之间只有 `fs≼`、`tree-≼`，没有 "项的序推出 `Rt` 的 `≼`" | 检索 `EboLeanTree`、`EboLeanLab`、`YiMonoExit`、`YiRefTw2` | 检索事实 |

##### 2. 文件表

都在 `<仓库>/probes/OCF/Lean/`，文首各 3 行。删自己三个接口后冷编，每份日志只有自己模块的一行 `Checking`；禁用构造与本机路径检索为 0。

| 文件 | 总行 | 代码行 | 冷编退出码 | 内存（`+RTS -s` total in use） |
|---|---|---|---|---|
| `YiCeilRead.lagda.md` | 248 | 164 | 0 | 1119 MiB |
| `YiCeilWit.lagda.md` | 147 | 88 | 0 | 1519 MiB |
| `YiCeilSmall.lagda.md` | 253 | 185 | 0 | 1670 MiB |

冷编日志在 `<实验目录>/agents/ceil/`，文件名 `<模块>.cold.log`。

##### 3. 定理表

全部无前提。

| 名字 | 逐字的陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `ε₀-upper` | `read (ψ₀ (suc zero) tt tt (Ωt (suc zero))) ≼ L.ψ⁰ (L.Ω (L.suc L.zero))` | 层号 1 的 Ω 树的折叠不高于 Level 的 ψ⁰(Ω₁)，读作 ψ₀(Ω₁) = ε₀；仓库里第一条 "块 ≼ 参照" | `YiCeilRead` | 编译定理 |
| `chain≼` | `∀ n → read (F₁ n) ≼ e (suc (suc n))` | 上例链上的第 n 行不高于参照塔的第 n+2 项（`e 0 = 1`，`e (n+1) = ω^(e n)`） | `YiCeilRead` | 编译定理 |
| `feed-Lin` | `(z : Tr (suc zero)) → Lin (Gw (br₂ z))` | N₂ 的回灌对一切 z 在线性类里 | `YiCeilWit` | 编译定理（形状） |
| `chain-Lin` | `(n : ℕ) → Lin (e₂ (suc n))` | 链 `e₂` 从第 1 项起都在线性类里 | `YiCeilWit` | 编译定理（形状） |
| `self-Lin` | `(c : Tr zero) (y : Tr (h₁ c)) → Lin (Gw (Upc (tw 1) c β nb y))` | 自身行的任何输出朝第 1 层折叠后在线性类里 | `YiCeilWit` | 编译定理（形状） |
| `N₂-Lin` | `Lin (Gw N₂)` | 上一条在 N₂ 的实例 | `YiCeilWit` | 编译定理（形状） |
| `Gw-Src` | `{x : Tr (tw 1)} → Src x → Lin (Gw x)` | 输入类 `Src`（β、右加 β、ℕ 极限、孩子一侧槽位的结点）被送进 `Lin` | `YiCeilWit` | 编译定理（形状） |
| `Src-Up` | `(j : LF) (d : Dn (tw 1) j) → NS d → (b : Tr (tw 1)) (nb′ : tw 1 ⊢ zero ◃ b) → Src b → (y : Tr j) → Src (Up j d b nb′ y)` | 上折的像都在 `Src` 里（链不是 `stop`，底在 `Src` 里） | `YiCeilWit` | 编译定理（形状） |
| `lin-small` | `{x : Tr (suc zero)} → Lin x → Σ T₀ λ d → rd x ≤ʷ mulΩ d` | 线性类的树值不超过 Ω₁·d | `YiCeilSmall` | 编译定理 |
| `feed-small` | `(z : Tr (suc zero)) → Σ T₀ λ d → rd (Gw (br₂ z)) ≤ʷ mulΩ d` | 回灌值不超过 Ω₁·d，对一切 z | `YiCeilSmall` | 编译定理 |
| `chain-small` | `(n : ℕ) → Σ T₀ λ d → rd (e₂ (suc n)) ≤ʷ mulΩ d` | 链的每一项如此 | `YiCeilSmall` | 编译定理 |
| `not-sq` | `(d : T₀) → ¬ (sq ≤ʷ mulΩ d)` | Ω₁² 不低于等于任何 Ω₁·d | `YiCeilSmall` | 编译定理 |
| `feed-below-sq` | `(z : Tr (suc zero)) → ¬ (sq ≤ʷ rd (Gw (br₂ z)))` | 回灌值严格低于 Ω₁² | `YiCeilSmall` | 编译定理 |
| `self-below-sq` | `(c : Tr zero) (y : Tr (h₁ c)) → ¬ (sq ≤ʷ rd (Gw (Upc (tw 1) c β nb y)))` | 自身行的输出朝第 1 层折叠后严格低于 Ω₁² | `YiCeilSmall` | 编译定理 |

**参照的读法依据。**
- `ε₀-upper` 的参照是 `OCF.Align.Level` 的 ψ⁰(Ω₁)，读法沿用该框架。
- `W` 是本文件自定的类型：以 ℕ 与第 0 层的合法树为分支的布劳威尔树，值前序 `≤ʷ` 与 `OCF.Align.Value` 的 `≼` 同形。
- `rd : Tr (suc zero) → W` 逐构造子读回；`up x tt y` 读成 `rd x ⊞ emb y`，与块自己的 `↑ k (up x c y _) = ↑ k x ⊕ ↑ch k c y` 同一约定。
- `mulΩ d` 对 d 递归：零得零，后继右加 `Ω₁ʷ = wo emb`，极限逐项，读作 Ω₁·d。
- `sq = wo (λ c → mulΩ (read c))`，读作 Ω₁²。
- 这些读法没有接到记号或 Level 的第 1 层。

##### 4. 上界工具的接口（`YiCeilRead`）

参照一侧，只在第 0 层：`mul Y n` 读作 Y·n，`ωx Y = L.lim (mul Y)` 读作 Y·ω，`pw Y a` 读作 Y·ω^a。

```
plus≼    : (a b : Tr zero) {A B : T₀} → read a ≼ A → read b ≼ B → read (a + b) ≼ A L.+ B
next≼    : (b : Tr zero) (nz : zero ⊢ zero ◃ b) {Y : T₀} → read b ≼ Y → read (next b nz) ≼ ωx Y
cum≼     : (F : ℕ → Tr zero) (G : ℕ → T₀) → (∀ n → read (F n) ≼ G n) → (∀ n → G n ≼ G (suc n))
           → ∀ n → read (cum F n) ≼ mul (G n) (suc n)
limc≼    : (F : ℕ → Tr zero) (nz : (n : ℕ) → zero ⊢ zero ◃ F n) {Y : T₀}
           → (∀ n → read (F n) ≼ Y) → read (limc F nz) ≼ ωx Y
limc≼lim : (F : ℕ → Tr zero) (nz : (n : ℕ) → zero ⊢ zero ◃ F n) (G : ℕ → T₀)
           → (∀ n → read (F n) ≼ G n) → (∀ n → G n ≼ G (suc n)) → (∀ n → ωx (G n) ≼ G (suc n))
           → read (limc F nz) ≼ L.lim G
Ω≼       : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) (G : ℕ → T₀)
           → (∀ n → read (ψ⊥ ℓ ε ρ B (g (stp⊥ ℓ ε ρ B p g n))) ≼ G n)
           → (∀ n → G n ≼ G (suc n)) → (∀ n → ωx (G n) ≼ G (suc n))
           → read (ψ⊥ ℓ ε ρ B (Ω p g)) ≼ L.lim G
fold₀≼   : (B : Base zero) {Y : T₀} → read (b⊥ B) ≼ Y → (x : Tr zero) → read (ψ⊥ zero tt tt B x) ≼ pw Y (read x)
folds₀≼  : (B : Base zero) (β : Tr zero) (nβ : zero ⊢ zero ◃ β) {Y : T₀} → read β ≼ Y
           → (x : Tr zero) → read (ψs zero tt tt B zero self β nβ x) ≼ pw Y (read x)
pw-mono  : {Y Y′ a a′ : T₀} → Y ≼ Y′ → a ≼ a′ → pw Y a ≼ pw Y′ a′
pw≼ψ⁰    : (x : T₀) → pw 𝟏 x ≼ L.ψ⁰ x
```

适用范围：
- `Ω≼` 对一切层号、槽位、底成立，是结点行定义的展开加部分和的吸收。`stp⊥` 是折叠自己的链。
- 链点的上界（回灌 `ψs` 的值）与各行的上界由使用者提供，工具不给。
- `fold₀≼`、`folds₀≼` 只管层号零。
- 参照一侧只有第 0 层的 Y·ω^a 算术，没有高层参照，没有与 `Rt` 的连接。
- 逐项对上时要带严格的余量：`ε₀-upper` 里的不变量是 "链点加 2 不高于塔的下一项"（`inv`）。这种差一的账在一般层号上要系统化，本路没做。

##### 5. 第一个障碍

**没有尝试编译的引理，下面是我判断会挡住的第一条：**

`read (ψ⊥ (tw 1) ε¹ ρ¹ (B₀ (tw 1)) (Up (suc zero) d₂ β nb z)) ≼ R`，z 在 `Lin` 里，R 是某个读得出的参照。

挡住的两处：
1. **没有能叫出 ψ₀(Ω_Ω·α) 的参照，除了记号树 `Rt h`。** Level 的层号只有零、后继、ℕ 极限。z 取零时这条引理就是 `read (twᶜ 1) ≼ Rt (hc-tower 2)`，即塔第 1 项不高于 BTBO 的参照。它要对一切可数层号 c 给 `read (G c)` 的上界，是 `YiLSFold.lower` 的对偶，再过 `tw 1` 的结点行。
2. **记号一侧没有序到值的单调性。** `Rt` 之间只有 `fs≼`（基本列的项）与 `tree-≼`（同一个项）。上界模拟的每一步都要 "较小的项的树不高于较大的项的树"，现在只能对基本列的后代用。

哪一边更可能：(ii)，理由见第 1 节的判断。

##### 6. 偏离与事故

- 简报要 2 做成 (i) 或 (ii)，都没做成。交的是工具、最小例子，以及回灌一侧的编译定理。
- `W`、`rd`、`mulΩ`、`sq` 是我自定的值语义，不是仓库已有的参照框架。
- 没有做第 3 项（推到 `T⁺` 或塔第 2 项）。
- 一次编译失败（`ε₀-tower` 里一个下划线解不出），补显式参数后通过；无堆耗尽。
- 没有碰别的路的文件；`rm` 只删了自己三个模块的接口。
- 没有读、只凭名字或转述引用的：
  - `YiLSRel`、`YiLSFold` 的正文，只用了行数与 `lower` 的名字；
  - `YiDecLow`；
  - `EBOHandbook.md` 第 4 节；
  - `YiDec.md` 回报只读了前 150 行；
  - 记号的定义文件（`EboLeanDef` 等）没有打开。
