# (C) F2 前 3 层从头精简重写 (YiRW)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 10:51 至 11:25 |
| 工具调用 / agda 编译 (粗数) | 64 / 27 |
| token (usage 字段，按消息去重) | 输出 189003；新写入缓存的输入 419415；读缓存的输入 13295678；其余输入 116 |
| 写过的仓库文件 | `YiRWBlock.lagda.md`, `YiRWCheck.lagda.md`, `YiRWFold.lagda.md`, `YiRWKall.lagda.md`, `YiRWOps.lagda.md`, `YiRWPath.lagda.md`, `YiRWSame.lagda.md` |
| 文件前缀 | `YiRW` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: (C) F2 前 3 层从头精简重写返回并复核; 第二十一批全部返回 (主审)” 一节 |
| 主审复核后的一句结论 | 前 3 层切片 89 / 422 / 422 (原 114 / 862 / 862; 主审重算一致); 行律都成立; 判断与 F2 同构, 值定理不自动搬; 七件冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定（2026-11-13，选项原文）
本路是 "(C) F2 前 3 层从头精简重写"。内容原文："按 '每到一站做成就安排一次从头重写'：现 862 行，标杆 1513。重写后对象可能换，旧值定理不自动搬；与 (A) 同时做，(A) 的结果可能要再搬"。

关键动词是 **"从头精简重写"**：从空白页开始写，现有代码只作参考，不是拷贝后删减。

同批另三路，各自只新建文件，你不动它们的文件：
- (A) 冲塔第 2 项，前缀 YiT2；
- (B) 终点的 Into，前缀 YiEB；
- (D) YiLPIface 的配对否定，前缀 YiLN。

###### 背景
- **标杆**：记号侧 EBO 从头重写到 FGH 可算是 1513 行（切片口径）。
- **先例**：上一次从头重写，把乙线前三层从 297 / 1251 / 1373 压到 112 / 335 / 351，见 `probes/OCF/Lean/YiLean*` 与 `probes/LOG.md` 2026-11-11。
- **现主线 F2**（合法块），在 `probes/OCF/Lean/`：`YiLegBlock`、`YiLegOps`、`YiLegPath`、`YiLegFold`。
  - 切片行数：块 114，加折叠与闭项 862。合法性是类型，第 3 层不另加。
  - 层 2 的增量主要是：路线证据 `YiLegPath` 270 行（由 `YiLimCheck.no-req` 逼出），与折叠同时造推导的 `YiLegFold` 313 行。
- **F2 的设计要点**（重写后要保住的性质，写法自由）：
  - 树与第一位置序归纳-归纳：ℕ 极限带相邻步进，嵌入带孩子非零，每棵树都合法（纲领第 1 条 "按低层合法树分支"）。
  - 层号是树：零、后继、ℕ 极限、Ω 结点 `Ωₗ k h`（`h : Tr k → L`）。ℕ 极限层号带必带的相邻路径。
  - 折叠 `ψ⊥`（到第 0 层）与 `ψs`（到目标层，带底）。嵌入一致 J2 各条，其中分支侧那一行回退：`YiAbsFrame.branch→wdec` 证明它不能观察地保同支。
  - 自身行上折（`self-up`）；k 侧保留（`kall`）；单调与非零（`mono⊥`、`monos`、`nz⊥`、`nzs`）。
  - 闭项 `twᶜ n`、`EBOᶜ`，记号无关：`importclosure.py` 要 OK。
- 接口记录 `YiLPIface` 列出了 F2 满足的全部行律，可作重写的验收清单。

###### 要做
1. **从头写一个新块与折叠**，到合法闭项 `twᶜ n`、`EBOᶜ` 为止。
   - 可以重新设计；可以与 F2 同构，也可以不同。
   - 硬要求：
     - `--safe --without-K`；
     - 导入闭包干净，只导入标准库与你自己的 `YiRW*` 文件；
     - 塔各项与 Λ 的闭项合法（类型保证或定理）；
     - 必带路径在塔上可满足；
     - 嵌入一致的各行（分支侧回退那一行除外）、单调、非零成立。
2. **行数**：同一口径（定义级切片，从闭项出发）目标前 3 层 ≤ 550 行，硬上限 700 行。超了要说明多出来的是哪一块、为什么。
3. **便宜的编译判据**（证明不是空树）：
   - 塔第 1 项里 ω+1 那一层孩子的底是结点，对照 `YiLegCheck.bω-tw`，有限测试即可；
   - 必带路径在塔上的闭项，对照 `Rt-tw`。
4. **可选**（做得到就做）：若新块与 F2 同构，给出到 F2 的转换，证明折叠与转换交换。这样 `YiLSBtbo.btbo-tw1`（F2 塔第 1 项 ≥ BTBO）能搬过来。做不到就写明旧值定理不自动搬。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiRW`（模块名 `OCF.Lean.YiRW…`）。不改任何已有文件，不碰 `src/`、`archive/`。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。无关参数可以用。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G。
  - 冷编只删自己模块的接口，写字面路径；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
- 临时目录：`<实验目录>/agents/rw`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；6G 仍耗尽。
- **过程要求**（硬性）：
  - 读完参考文件后，下一次回复就写块的文件并编译；块的文件 15 分钟内首次编译。
  - 每写完一个文件就编译。
  - 每次回复都要有工具调用，不要在一次回复里只思考。
  - 设计边写边改。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；`importclosure.py OCF.Lean.<模块>` 全部 OK；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：对纲领与目标意味着什么；新块与 F2 的关系（同构 / 不同，哪里不同）。
2. 文件表：代码行、冷编退出码、内存、importclosure。
3. 行数：你按什么口径数的，前 3 层各多少；与 F2 的 114 / 862 对比，省在哪里。
4. 定理表：名字、逐字的陈述、一句白话、文件、档（编译定理 / 有限测试 / 判断）。
5. F2 的哪些行律在新块上成立、哪些没做；旧值定理能否搬。
6. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 回报: (C) F2 前 3 层从头精简重写 (前缀 YiRW)

##### 1. 判决

**结果**: 从空白页重写的新块与折叠全部编译通过。前 3 层切片行数是 **89 / 422 / 422**, F2 是 114 / 862 / 862, 目标 ≤ 550 达到, 硬上限 700 也没碰到。

**对纲领**
- 第 1 条: 新块仍是布劳威尔树的归纳-归纳块, 合法性就是类型。ℕ 极限带相邻步进, 嵌入带孩子非零; Ω 结点的分支和 Ω 形状层号的孩子下标只取低层合法树。
- 第 2 条: 全部 `--safe --without-K --lossy-unification`, 没有公设, 没有洞。
- 第 4 条: 产品文件 Block/Ops/Path/Fold 的导入闭包只有标准库和 YiRW*。`importclosure.py --only OCF.Lean.YiRW` 退出 0。
- 第 3 条 (判断): 没有新增任何比较或三歧。

**对目标 "树自足" (判断)**: 没有进展。这是同一对象的重写, 去掉的是写法上的脚手架: 按形状重复的子句, 单独的非零引理, 单独的到第 0 层的折叠, 两套证据谓词。来自记号的规则一条没去掉, 折叠各行的来源与 F2 相同, 翻译账不变。

**与 F2 的关系 (判断: 同构, 即同一数学对象; 没有编译过的转换)**
- 层号一一对应: `suc a` ↔ `nd sS (λ _ → a)`, `lim g` ↔ `nd sL g`, `Ωₗ k h` ↔ `nd (sΩ k) h`。槽位多一层 `⊥ ⊎`。
- 折叠各行逐行对应。有限测试 `YiRWSame` 支持这一判断: 在 6 条下标路径上, 新旧闭项记录相同。

与 F2 的写法差异:
1. **层号统一成 `nd s h`** (形状 s, 孩子 h)。孩子类型 `ChT (nd s h) c = Tr (h c)` 定义上成立, 所以 F2 的 `chL/chP/chBr/chFirst/↑ch/Upc*` 都不需要了。缺的荒谬子句由检查器自己补。
2. **第一分支直接是 `fromBr ℓ p zero`**: `sl` 同时给槽位所在层号和换型, 进 Sig 不出停机问题。F2 的 `br0`, `br0≡` 去掉了。
3. **路径合成一个类型**: `Pth : Bool → L → L → Set`, 4 个构造子。`true` 才有 `ink`, `≤ = Pth true`, `⊑ = Pth false`。F2 是两个类型, 前者 7 个构造子。
   - 后继形状多出一种路径 `inu`, 行为等同 `inc tt`; F2 的 suc 层没有这种路径。
4. **F2 的 `Ev` 与 `Rt` 合成一个谓词 `Ok`**: Ω 形状的下标层合法且 ≤ 每个孩子; ℕ 极限形状必带相邻路径。
5. **树与 "0 ◃ 树" 成对 (`Tr⁺`)**: 非零并进了值, F2 的 `nz⊥`, `nzs`, `Ωt-nz`, `Up-nz`, `emb-nz` 都去掉了。
6. **`ψ⊥` 并进 `ψ`**: 到第 0 层就是目标取 `zero`、路径取一致路径 `z≤`、底显式传入。`Base` 不再单带 `b⊥`。
   - 这一对应是判断; 支持它的编译定理是 `J2⊥`, `kp-z`, `node⊥`。
7. **保留判定 `kp` 返回 `Maybe (Σ q, Σ cv, cv (第一分支) ≡ 第一分支)`**, 不用 CPS, 所以 `kp-ind` 去掉了。
8. **`way` 改成平移递归** (约 10 行), 取代 `<ₙ/Cmp/cmp/rt`。m = n 时同样给 `bwd self` (`way-refl`)。

##### 2. 文件表

都在 `<仓库>/probes/OCF/Lean/`。冷编方式: 删掉自己的 7 个 `.agdai`, 按依赖序 6G 各编一次。

| 文件 | 性质 | agda 块非空行 (含导入) | 冷编退出码 | 最大驻留 / 时间 | importclosure |
|---|---|---|---|---|---|
| YiRWBlock | 成品候选 | 101 | 0 | 134 MB / 1.5 s | OK |
| YiRWOps | 成品候选 | 107 | 0 | 139 MB / 1.6 s | OK |
| YiRWPath | 成品候选 | 147 | 0 | 158 MB / 1.8 s | OK |
| YiRWFold | 成品候选 | 109 | 0 | 159 MB / 1.9 s | OK |
| YiRWCheck | 验收 | 140 | 0 | 267 MB / 2.4 s | OK |
| YiRWKall | 定理 | 54 | 0 | 161 MB / 1.8 s | OK |
| YiRWSame | 有限测试, 导入 F2 | 36 | 0 | 996 MB / 6.2 s | OK |

- 每个日志只有自己模块的一行 `Checking`。
- 7 个文件对禁用构造的检索为 0: postulate、TERMINATING、NO_POSITIVITY、trustMe、洞、irrelevant-projections、cubical、funext。也没有本机路径。
- YiRWSame 导入 `YiLegBlock`, `YiLegFold`: 闭包干净, 但不是只有 YiRW*。

##### 3. 行数

**口径**: 复用 `probes/Survey/scripts/locslice.py` 的块划分与闭包 (像 `lvtop/locslice_lvtop.py` 一样 exec 它), 计到达的定义块里 agda 非空非注释行, 标准库不计。
- 根: 层 1 `tw`, `Λ`; 层 2 加 `twᶜ`, `EBOᶜ`; 层 3 是合法性, 它就是类型, 不另加。
- 校准: 同一脚本跑 F2 得 114 / 862 / 862, 与 LOG 的主审数一致。
- 脚本在 `<实验目录>/agents/rw/slice_rw.py`。

| 层 | 新块 | F2 |
|---|---|---|
| 1 块 | 89 | 114 |
| 2 + 折叠与闭项 | 422 | 862 |
| 3 + 合法性 (类型) | 422 | 862 |

层 2 按文件对比 (新块对 F2):
- **Fold 99 对 313**: ψ⊥ 并入 ψ; nz 并入值; 不要 kp-ind; 一切孩子的路径那一行对所有形状只写一条子句; 孩子的底写成一行 lambda。
- **Path 135 对 270**: 两套证据合一; 两种路径合一; way 从约 45 行降到约 10 行; `psh` 一族每个 4 条子句 (F2 是 7 条)。
- **Ops 97 对 150**: 不再需要 `cumΩ`, Upc 四件, chP 三件, 非零引理。
- **Block 91 对 129**: 孩子类型一族各一条子句; 去掉 `br0/br0≡`; 荒谬子句由检查器补。

Check、Kall、Same 不计入三层。

##### 4. 定理表

**编译定理 (无前提)**

- `Ok-tw : (n : ℕ) → Ok (tw n)`; `Ok-Λ : Ok Λ`
  白话: 塔各项与 Λ 的层号证据, 含必带的相邻路径, 是闭项。文件 Path。
- `mono : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ ℓ o B j w β x) ◃ proj₁ (ψ ℓ o B j w β y)`
  白话: 折叠对第一位置序单调。文件 Fold。
- 非零: 是 `ψ : (ℓ : L) → Ok ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j` 的类型, `proj₂` 就是非零的证明。文件 Fold。
- 闭项: `twᶜ : ℕ → Tr zero`, `EBOᶜ : Tr zero`, 合法是类型。文件 Fold。

以下都在 Check, 除非另注:

- `J2-u : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (B : Base (nd s h)) (j : L) (ws : (c : Ch s) → j ≤ h c) (β : Tr⁺ j) (x : Tr (nd s h)) (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → ψ (nd s h) o B j (inu ws) β (up x c y e) ≡ ψ (h c) (proj₂ o c) (cb o B c x) j (ws c) (ψ (nd s h) o B j (inu ws) β x) y`
  白话: 一切孩子的路径进孩子 c, 底是 x 的折叠。对应 F2 的 J2-limu, J2-Ωu。refl。
- `J2⊥ : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (B : Base (nd s h)) (β : Tr⁺ zero) (x : Tr (nd s h)) (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → ψ (nd s h) o B zero (z≤ (nd s h)) β (up x c y e) ≡ ψ (h c) (proj₂ o c) (cb o B c x) zero (z≤ (h c)) (ψ (nd s h) o B zero (z≤ (nd s h)) β x) y`
  白话: 到第 0 层的三条, 合成一条。
- `J2-k : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (j : L) (v : j ≤ k) (β : Tr⁺ j) (x : Tr (nd (sΩ k) h)) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → ψ (nd (sΩ k) h) o B j (ink v) β (up x c y e) ≡ ψ (h c) (proj₂ o c) (cb o B c x) j (v ∙ proj₂ (proj₁ o) c) (ψ (nd (sΩ k) h) o B j (ink v) β x) y`
  白话: 下标层侧。
- `J2-s : (h : ⊤ → L) (o : Ok (nd sS h)) (B : Base (nd sS h)) (j : L) (v : j ≤ h tt) (β : Tr⁺ j) (x : Tr (nd sS h)) (y : Tr (h tt)) (e : h tt ⊢ zero ◃ y) → ψ (nd sS h) o B j (inc tt v) β (up x tt y e) ≡ ψ (h tt) (proj₂ o tt) (cb o B tt x) j v (ψ (nd sS h) o B j (inc tt v) β x) y`
  白话: 后继形状。
- `way-refl : (g : ℕ → L) (r : (n : ℕ) → g n ≤ g (suc n)) (n : ℕ) → way g r n n ≡ inj₂ self`
- `J2-lim : (g : ℕ → L) (o : Ok (nd sL g)) (B : Base (nd sL g)) (n : ℕ) (j : L) (v : j ≤ g n) (β : Tr⁺ j) (x : Tr (nd sL g)) (y : Tr (g n)) (e : g n ⊢ zero ◃ y) → ψ (nd sL g) o B j (inc n v) β (up x n y e) ≡ ψ (g n) (proj₂ o n) (cb o B n x) j v (ψ (nd sL g) o B j (inc n v) β x) y`
  白话: 同号孩子。
- `J2-lim-fwd`: 多一个前提 `(u : g m ≤ g n) → way g (proj₁ o) m n ≡ inj₁ u`, 结论 `ψ (nd sL g) o B j (inc n v) β (up x m y e) ≡ ψ (g n) (proj₂ o n) (cb o B n x) j v (ψ (nd sL g) o B j (inc n v) β x) (proj₁ (emb (g n) (proj₂ o n) u (y , e)))`。
- `J2-lim-bwd`: 多一个前提 `(u : g n ≤ g m) → way g (proj₁ o) m n ≡ inj₂ u`, 结论 `… ≡ ψ (g m) (proj₂ o m) (cb o B m x) j (v ∙ u) (ψ (nd sL g) o B j (inc n v) β x) y`。
- `J2-b : … → ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e) ≡ ψ (nd (sΩ k) h) o B j (inc c′ v) β x ⊞ ψ₀ (h c) (proj₂ o c) y`
  白话: 分支侧回退那一行, 只陈述它的形状。
- `self-up : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (B : Base (nd s h)) (β : Tr⁺ (nd s h)) (x : Tr (nd s h)) (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → ψ (nd s h) o B (nd s h) self β (up x c y e) ≡ Up (h c) (down stop c) (ψ (nd s h) o B (nd s h) self β x) y`
  白话: 自身行是上折。
- `node : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → ψ ℓ o B j w β (Ω p g) ≡ node⁺ (kp ℓ o p w) (λ z → ψ ℓ o B j w β (g z)) (step ℓ o B p g)`
  白话: 结点行。
- `kp-z : (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) (w : zero ≤ ℓ) → kp ℓ o p w ≡ nothing`
  白话: 到第 0 层, 经任何路径, 结点都不保留。
- `node⊥ : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (w : zero ≤ ℓ) (β : Tr⁺ zero) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → ψ ℓ o B zero w β (Ω p g) ≡ limc⁺ (λ n → ψ ℓ o B zero w β (g (iter (step ℓ o B p g) (fromBr ℓ p zero) n)))`
- `kp-fwd : (g : ℕ → L) (o : Ok (nd sL g)) (m n : ℕ) (t : Pos⁼ (g m)) {j : L} (v : j ≤ g n) (u : g m ≤ g n) → way g (proj₁ o) m n ≡ inj₁ u → kp (nd sL g) o (inj₂ (m , t)) (inc n v) ≡ mapK (pshBr u t) (pshFirst u t) (kp⁼ (g n) (proj₂ o n) (psh u t) v)`
- `kp-bwd : … (u : g n ≤ g m) → way g (proj₁ o) m n ≡ inj₂ u → kp (nd sL g) o (inj₂ (m , t)) (inc n v) ≡ kp⁼ (g m) (proj₂ o m) t (v ∙ u)`
- `kstep : (a : L) (oa : Ok a) (B : Base (Nx a)) (β : Tr⁺ a) (x : Tr (Nx a)) (p : Pos a) (g : Br a p → Tr a) (e : a ⊢ zero ◃ Ω p g) → ψ (Nx a) (Ok-Nx a oa) B a (ink self) β (up x zero (Ω p g) e) ≡ Ω⁺ p (λ z → ψ a (proj₂ (Ok-Nx a oa) zero) (cb (Ok-Nx a oa) B zero x) a self (ψ (Nx a) (Ok-Nx a oa) B a (ink self) β x) (g z))`
  另有 `tw-Nx : (n : ℕ) → tw (suc n) ≡ Nx (tw n)`。
- `kall : (a : L) (oa : Ok a) (B : Base (Nx a)) (β : Tr⁺ a) (x : Tr (Nx a)) (c : Tr a) {t : Pos (a ⊕ ↑ a c)} (G : Br (a ⊕ ↑ a c) t → Tr (a ⊕ ↑ a c)) (e : a ⊕ ↑ a c ⊢ zero ◃ Ω t G) (i : InB a (↑ a c) t) (p : Pos a) → prE i (OkO↑ a a oa self c) ≡ inj₂ p → Kept p (proj₁ (ψ (Nx a) (Ok-Nx a oa) B a (ink self) β (up x c (Ω t G) e)))`
  白话: k 侧对一切孩子保留。文件 Kall。`kall-tw` 是塔各项的实例。
- `no-bad : ∀ {ℓ} {x : Tr ℓ} → ℓ ⊢ suc x ◃ zero → ⊥`
- `req-child : (n : ℕ) (c : Tr (tw n)) → Ok (tw n ⊕ ↑ (tw n) c)`
- `adj-Λ : proj₁ Ok-Λ ≡ (λ n → ink self)`

**有限测试** (Check; 最后一项在 Same)

- `tw1-adj : proj₁ oω ≡ (λ n → inc tt self)`: 塔第 1 项给 ω+1 那一层的相邻路径。对照 F2 的 `ins self`, 即任务里说的 `Rt-tw`。
- `tw1-way : way gω (proj₁ oω) 1 2 ≡ inj₁ (inc tt self)`
- `bω-tw : isΩ (proj₁ (cb oω (B₀ _) 2 preω one (inc tt self)))`: ω+1 那一层孩子 2 的底是结点。对照 `YiLegCheck.bω-tw`。
- `cω-A`, `cω-B`: 结点经孩子 1 与孩子 2 两条路径都保留。
- `EBOᶜ-lim : isLim EBOᶜ`; `tw1ᶜ-lim : isLim (twᶜ 1)`
- `same1a … same1d`, `same2a`, `sameΛa`, 例如 `same1a : trN (NF.twᶜ 1) qa ≡ trO (OF.twᶜ 1) qa`: 沿 6 条下标路径, 新旧 `twᶜ 1`、`twᶜ 2`、`EBOᶜ` 的轨迹相同。

##### 5. 对照 YiLPIface 的行律, 旧值定理能否搬

**新块上成立 (编译定理, 都是新块自己的陈述)**
- J2-suc / lim / limu / Ωk / Ωu: 对应 J2-s, J2-lim, J2-u, J2-k。
- J2⊥ 三条: 合成一条 J2⊥。
- self-up, node, node⊥ (由 kp-z 推出), mono⊥/monos (合成 mono), nz⊥/nzs (是类型)。
- kp-fwd, kp-bwd, J2-lim-fwd, J2-lim-bwd, kstep, kall (含 kall-tw)。

**没做**
- 没有把 `YiLPIface.Iface` 记录实填出来: 字段的类型引用 F2 的 L 与 Tr, 新块的类型不同。
- 分支侧回退那一行按要求不处理, 只用 J2-b 陈述它的形状。

**旧值定理不能自动搬**, 包括 `YiLSBtbo.btbo-tw1`。理由是判断: 层号与树互为归纳-递归, Ω 形状的孩子函数 `h : Tr k → L` 是逆变的。转换必须两个方向同时造, 还要证往返恒等, 并沿它运输; 没有函数外延, 往返恒等只在命题上成立, 定义上不成立。所以只交了有限测试 YiRWSame, 没有转换。

##### 6. 偏离、事故、没读的东西

**事故**
- `/usr/bin/time -l` 被沙盒拦下 (sysctl), 所以内存一律用 `+RTS -s` 取最大驻留。
- 临时目录里的两次试验:
  - 慢增长观测 `G (twᶜ 1) 2` 跑过 120 秒, 转入后台后用 TaskStop 停掉。
  - 用 `--interaction` 规范化 `twᶜ 2` 的长路径时 6G 堆耗尽 (251)。
  - 仓库里的 YiRWSame 只留了能编译的测试 (约 1 GB)。

**结构上的说明**
- YiRWKall 从验收文件 YiRWCheck 导入 `Nx`, `Ok-Nx`。
- YiRWSame 导入 F2, 只用于测试。
- 新块在后继层号上多一种路径 `inu`。

**读过的**
- 全文: `YiLegBlock`, `YiLegOps`, `YiLegPath`, `YiLegFold`, `YiLPIface`, `YiLPKall`。
- 部分: `YiLegCheck` (20–69 行, 200–257 行), LOG 的 9070–9095 行, `locslice.py`/`importclosure.py`/`lvtop` 切片脚本的开头。

**没读, 只凭转述或 F2 注释引用**: `YiLSBtbo` (btbo-tw1), `YiLimCheck.no-req`, `YiAbsFrame.branch→wdec`, `YiLPInst`, 主审的 `slice_roots.py` (仓库里没有, 改用上面校准过的脚本)。
