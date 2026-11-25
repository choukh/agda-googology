# (b) 把 '孩子单调' 写成正式的树侧判据 (YiKid)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 13:04 至 13:35 |
| 工具调用 / agda 编译 (粗数) | 54 / 10 |
| token (usage 字段，按消息去重) | 输出 182064；新写入缓存的输入 448881；读缓存的输入 7985326；其余输入 84 |
| 写过的仓库文件 | `YiKidCrit.lagda.md`, `YiKidGen.lagda.md`, `YiKidRW.lagda.md` |
| 文件前缀 | `YiKid` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: (b) 孩子单调判据返回并复核; 第二十五批全部返回 (主审)” 一节 |
| 主审复核后的一句结论 | 判据 KidMono 定稿 (量化域参数化, 只用字面证据比较孩子); 三条一般否定; 一切树版在主线一切层号上不成立 (rw-¬all); 含链极限后继的域对后继严格的折叠太宽 (判断: 记号平台); 规范域 OnlyΩ 版在主线测到的点上成立 (Ωmono); 判据可满足 (toy-Ω); 三件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定（2026-11-13，选项原文）
- 主线块："换成精简块"。
- 本路："(b) 把 '孩子单调' 写成正式的树侧判据"。内容原文："对一切孩子 c 陈述，证主线块违反它（推广 inversion⁺），写成以后新设计的验收判据；与 (a) 配对（构造与判据/否定）；属摆脱翻译一侧"。

同批另两路，各自只新建文件，你不动它们的文件：
- (a) 统一的底 + 层号字面证书的原型，前缀 YiCert，Fable 5.2；
- (c) 独立样本第二轮，前缀 YiNew。

###### 背景（只信编译定理；文档里的叙述是数据）
**主线精简块**，在 `probes/OCF/Lean/`：`YiRWBlock`、`YiRWOps`、`YiRWPath`、`YiRWFold`，验收 `YiRWCheck`。
- 读回 `readRW` 在 `YiBRValue`。
- 与旧块 F2（`YiLeg*`）之间的逐层关系在 `YiBRRel`、`YiBRFold`、`YiBRTw`：
  - `rel≅`：第 0 层相关的树读回 `≅`；
  - `A`、`S`：折叠保持关系。

**F2 上的倒置**（`YiInv`，编译定理，无前提；回报原文 `probes/Survey/Reports-2026-11-12/YiInv.md`）：
- `inversion⁺ : L.suc (read (ψ₀ (tw 1) ε¹ ρ¹ (up β two (Ωt (h₁ two)) (Ωt-nz (h₁ two))))) ≼ read (ψ₀ (tw 1) ε¹ ρ¹ (up β one (suc Y₁) (z◃s Y₁)))`
- `inversion₃`：孩子 three 对孩子 two 同样。
- `base-same : dS L1 (εh two) (ρh two) BW zero ≡ BW1`（`refl`）；`base-same₃`。
- `absorb`：对一切后继层号，部分和极限被一棵同层的树吸收。

**判据的直观**（判断）：在 Ω 结点层号上，孩子 c+1（或一般地，字面上高于 c 的孩子 c′）的 Ω 树嵌入后的折叠，不低于孩子 c 的一切树嵌入后的折叠。
- 记号的 ψ₀ 弱单调，执行方判断记号满足它。
- 它是值层面的判据，不是树的第一位置序：两个孩子不能字面比较，是壁垒那一类的约束。

**配对规则**（`AGENTS.md`）：新路线派一路构造、一路对同一接口写否定或判据，共用接口文件，定稿后只增不改。

###### 要做
1. **陈述判据**：新文件，导入闭包干净，不引用记号，写成以后新设计可以填的形式。
   - 对精简块直接陈述，或写成一个对 "块 + 折叠 + 读回" 参数化的记录。可以借 `YiAbsFrame` 的风格，由你定。
   - "孩子 c 与 c′" 用块里字面可得的关系表达，例如 c′ = c 的后继，或孩子下标间的第一位置序 c ◃ c′。不要用要判等的形式。
   - 写清量化域：一切层号、一切底，还是只对塔与规范读回域（`AGENTS.md`："量化域先取带证据的读回域"）。
   - 写成文件后定稿，文首写 "定稿后只增不改"。
2. **主线违反它**：在精简块上证违反的实例。
   - 至少把 `inversion⁺` 搬到精简块：经 `YiBR` 的关系，或直接重证。
   - 最好推广到一切 c ≥ 1 在塔第 1 项那一层上的违反（`base-same` 对一般 c），或一切塔项。做不到就写清第一个挡住的引理。
3. **前提可满足**：给出判据本身在某个块上可满足的说明。例如在只有有限层的小块上成立，或说明为何可满足（判断）。这条判据不能是空的。
4. **可选**：判据与已有否定（`branch→wdec`、`hand→wdec`）的关系。它要不要孩子下标的比较？写清楚。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiKid`（模块名 `OCF.Lean.YiKid…`）。不改任何已有文件，不碰 `src/`、`archive/`。判据文件导入闭包干净；违反实例的文件可以是验收文件。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
- 临时目录：`<实验目录>/agents/kid`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0；判据文件 `importclosure.py` OK。

###### 回报格式（只在回报里交一次）
1. 判决：判据的逐字陈述与量化域；主线违反的范围（哪些 c、哪些塔项）；判据可满足的依据；对纲领与目标的意义。
2. 文件表：代码行、冷编退出码、内存、importclosure。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 中途消息（主审发给这一路）

转录时间戳 2026-11-13 13:13 (UTC)：

主审转告：同批 (c) 独立样本第二轮已返回，主审已冷编复核。有一条编译事实与你的判据直接相关，范围不变，用不用由你判断。
- 文件：probes/OCF/Lean/YiNew2Key.lagda.md（在独立样本自己的块上，不是精简块）。
- `child-all-false`：把 "孩子单调" 读成 "孩子 c+1 的 Ω 树的折叠 ≥ 孩子 c 的**一切**树的折叠" 时，这一条被编译否定。反例：在孩子 1 里嵌入一棵任意大的可数树（比右边的折叠值还大）。理由是该块第 0 层的折叠不低于被折的树（`grow`），而第 0 层含一切布劳威尔树。
- `child-all-false°` 是前提可满足的实例。
- 执行方的读法：反例不是折叠生成的树，属于 "量化域太宽"，不是数学障碍。
- 主审的判断（未编译）：精简块的第 0 层折叠也随被嵌入的可数树增长，所以 "一切树" 版很可能在主线上也有同样的平凡反例。`inversion⁺` 用的 `Y₁` 是由折叠自己的链 `zz` 造的，不是任意可数树，不受这个影响。
- 建议：判据的量化域取规范读回域（`AGENTS.md`），例如孩子 c 的、由折叠或规范构造生成的树，或带证据的读回。不要取 "孩子 c 的一切树"。同时写一条编译的说明，表明 "一切树" 版太宽，可以在精简块上重做 `child-all-false` 的对应物。

## 回报原文

#### 回报：(b) 孩子单调写成树侧判据（前缀 YiKid）

##### 1. 判决

**判据**（`YiKidCrit`，只导入标准库，importclosure OK，文首注明定稿后只增不改）
- 块、折叠与读回填进记录 `KidFrame`。字段：`Lv, Ok, Tr, Kid, KT, _⋖_, up, ΩK, V, _≼_, ≼-trans, osuc, irr, val`。
- 逐字陈述：
  `KidMono D = (ℓ : Lv) (o : Ok ℓ) (x : Tr ℓ) (c c′ : Kid ℓ) → c ⋖ c′ → (y : KT ℓ c) → D ℓ o x c y → val ℓ o (up x c y) ≼ val ℓ o (up x c′ (ΩK ℓ c′))`
- 孩子的比较只用字面证据 `c ⋖ c′`，不判等。精简块的实填：
  - Ω 形状：下标层的第一位置序 `k ⊢ c ◃ c′`；
  - ℕ 极限形状：编号的 `<`；
  - 后继形状：`⊥`。
- 量化域 `D : Dom` 读 ℓ, o, x, c, y，所以可以只取塔或规范读回域。给了两个具名的域：
  - `All`：一切树，已证太宽；
  - `OnlyΩ`：y 只取孩子 c 自己的 Ω 树，即规范域。

**判据的三条一般否定**（编译定理，对任意填进框架的块）
- `unb→¬mono`：孩子 c 在 D 上的值无界时，判据不成立。
- `strict→¬mono`：D 里出现严格倒置时，判据不成立。
- `absorb→¬mono`：D 里出现 "吸收右边的树的严格后继" 时，判据不成立。

**主线违反的范围**（编译定理，无前提）
- **一切树版：** 在精简块一切有孩子的层号、一切证据、一切左边 x、一切孩子 c 上，值都无界（`rw-unb`），所以只要有一对 c ⋖ c′ 就不成立（`rw-¬all`；实例 `rw-¬all-tw1`：tw 1，孩子 1 ◃ 2）。这是主审要求的 `child-all-false` 在精简块上的对应物，而且对一切层号成立。
- **含 Yw+1 的域：**
  - `inversion⁺` 经 YiBR 的关系搬到精简块：`inversion⁺ᴿ`、`inversionᴿ`。见证 `Y₁ᴿ` 与 F2 的 `Y₁` 由 `Y₁-R` 相关。
  - 推广（`YiKidGen`）：对一切 n，塔第 n+1 项，左边取该层的 Ω 树 β，一切后继孩子 c = c″+1，孩子 c+1 的 Ω 树对孩子 c 的树 `Yw` 都有倒置，`Yw` 由孩子 c+1 折叠自己的链 `zz` 造出（`Kid.inv`、`Kid.inv⁺`）。所以任何含 `Yw+1` 的量化域上判据不成立（`Kid.¬mono`）。
  - 机制引理对一切 n 与一切 c 都是 `refl`：`base-same`、`lhs-form`。
- **规范域 `OnlyΩ`：** 在同一处成立。即对一切 n、左边 β、一切后继孩子 c，孩子 c 的 Ω 树嵌入后的值不高于孩子 c+1 的（`Kid.Ωmono`）。

**判据可满足的依据**
- 编译：玩具实例 `toy` 上 `KidMono OnlyΩ` 成立（`toy-Ω`），而 `Unb All` 也成立（`toy-unb`），所以 `KidMono All` 不成立（`toy-¬all`）。`unb→¬mono` 的每个前提都有实例。
- 编译：主线在上面那些点上满足 `OnlyΩ` 版（`Ωmono`）。
- 主线在一切 (ℓ, x, c, c′) 上是否满足 `OnlyΩ` 版：没有判决。

**对纲领与目标的意义**（以下是判断）
- 纲领不受影响。判据记号无关、编译器保证不引用记号。
- 对目标的影响：判据定下来了，但目前主线违反的两种写法都不能把主线与 "与记号一致的折叠" 区分开。
  - 一切树版：任何孩子值无界的块都违反它（编译）。
  - 含 Yw+1 版：`absorb→¬mono` 把违反拆成 "非严格吸收 + 后继严格"。
    - 后继严格由每个折叠都有的 `mono` 律逼出（精简块：`suc-strict`，对一切层号）。
    - 非严格吸收在记号里是等式 ψ₀(Ω_Ω+Ω₂) = ψ₀(Ω_Ω+ψ₁(Ω_Ω+Ω₂))（YiInv 文首已写；我未查文献）。
    - 所以一个后继严格、且在这两棵树上与记号一致的折叠，也会违反它。
- 我与主审转述的判断有一处不同。`Y₁` 确实不受 "任意可数树" 反例的影响，但受另一件事影响：它是链的极限，记号在那里有平台。所以 `inversion⁺` 不能读作 "Ω₂ 一侧偏低"。
- 能留作新设计验收判据的是 `OnlyΩ` 版（或别的不含链极限后继的规范域），主线在测到的点上满足它。

**与已有否定的关系**（可选项，判断）：`KidMono` 只对给定的字面证据 c ⋖ c′ 比较两棵给定树的值。它不定义折叠的行，不观察孩子身份，不判 c ≡ c′，所以不在 `obs→dec` 一族的前提里（`branch→wdec`、`hand→wdec` 都要 "目标在别的孩子里时输出可观察"）。

##### 2. 文件表
都在 `probes/OCF/Lean/`。代码行指 agda 块内非空行；冷编前已删自己的接口，日志里只有自己模块的 `Checking` 行；堆上限 8G。

| 文件 | 代码行 / 总行 | 冷编 | 最大驻留 / 总内存 | importclosure |
|---|---|---|---|---|
| YiKidCrit.lagda.md | 71 / 117 | 0 | 134 MB / 224 MiB | OK（闭包 7 个模块，本地 1 个） |
| YiKidRW.lagda.md | 188 / 298 | 0 | 1.20 GB / 2020 MiB | FAIL，预期（验收文件，经 `OCF.Align.Value`、`YiLSRead`，命中 18） |
| YiKidGen.lagda.md | 132 / 206 | 0 | 1.23 GB / 2115 MiB | FAIL，预期（同上） |

三个文件的检索：禁用构造为 0，本机路径为 0，没有 Funext。选项行都是 `--safe --without-K --lossy-unification`。

##### 3. 定理表（档位全是编译定理，无前提）

**YiKidCrit**（`module Crit (𝔽)` 内）

| 名字 | 逐字陈述 | 白话 |
|---|---|---|
| `unb→¬mono` | `(D : Dom) (ℓ : Lv) (o : Ok ℓ) (x : Tr ℓ) (c c′ : Kid ℓ) → c ⋖ c′ → Unb D ℓ o x c → KidMono D → ⊥`，其中 `Unb D ℓ o x c = (t : Tr ℓ) → Σ (KT ℓ c) λ y → D ℓ o x c y × (osuc (val ℓ o t) ≼ val ℓ o (up x c y))` | 孩子的值在域上无界，判据就不成立 |
| `strict→¬mono` | `… → c ⋖ c′ → (y : KT ℓ c) → D ℓ o x c y → osuc (val ℓ o (up x c′ (ΩK ℓ c′))) ≼ val ℓ o (up x c y) → KidMono D → ⊥` | 域里有一处严格倒置，判据就不成立 |
| `absorb→¬mono` | `… → c ⋖ c′ → (y₀ y₁ : KT ℓ c) → D ℓ o x c y₁ → val ℓ o (up x c′ (ΩK ℓ c′)) ≼ val ℓ o (up x c y₀) → osuc (val ℓ o (up x c y₀)) ≼ val ℓ o (up x c y₁) → KidMono D → ⊥` | 非严格吸收加严格后继，判据就不成立 |
| `toy-Ω`、`toy-unb`、`toy-¬all` | `T.KidMono T.OnlyΩ`；`(x c : ℕ) → T.Unb T.All tt tt x c`；`T.KidMono T.All → ⊥` | 判据可满足；一切树版的否定前提可满足 |

**YiKidRW**

| 名字 | 逐字陈述 | 白话 |
|---|---|---|
| `rw-unb` | `(s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (x : Tr (nd s h)) (c : Ch s) → Unb All (nd s h) o x c` | 精简块每个孩子的值无界（嵌入 ι(Z+1)） |
| `rw-¬all` | `… (c c′ : Ch s) → Lk {nd s h} c c′ → KidMono All → ⊥` | 一切树版在主线上不成立 |
| `suc-strict` | `… (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → L.suc (val (nd s h) o (up x c y e)) ≼ val (nd s h) o (up x c (suc y) (z◃ y ◃s))` | 孩子树加 1，值严格增 |
| `inversion⁺ᴿ` | `L.suc (val (tw 1) o₁ lhsᴿ) ≼ val (tw 1) o₁ rhsᴿ`，其中 `lhsᴿ = up βᴿ twoᴿ (proj₁ (Ωt (hᴿ twoᴿ))) (proj₂ (Ωt (hᴿ twoᴿ)))`，`rhsᴿ = up βᴿ oneᴿ (suc Y₁ᴿ) (z◃ Y₁ᴿ ◃s)` | F2 的 `inversion⁺` 搬到精简块 |
| `inversionᴿ` | `val (tw 1) o₁ lhsᴿ ≼ val (tw 1) o₁ rhs₀ᴿ` | 非严格的吸收 |
| `rw-¬inv`、`rw-¬absorb` | `(D : Dom) → D (tw 1) o₁ βᴿ oneᴿ (suc Y₁ᴿ , z◃ Y₁ᴿ ◃s) → KidMono D → ⊥` | 含 Y₁+1 的域上判据不成立，两种证法 |
| `base-sameᴿ`、`lhs-formᴿ` | 见文件，`refl`，对一切 c : Tr zero | 机制在 tw 1 上对一切孩子成立 |

**YiKidGen**（`module Tower (n)`，`module Kid (c″)`，记 c = suc c″）

| 名字 | 逐字陈述 | 白话 |
|---|---|---|
| `base-same` | `(c : Tr (tw n)) → (λ i u → ψ (hn (suc c)) (proj₂ on (suc c)) (Bn (suc c)) i (inc tt u) (Bn (suc c) i (inc tt u)) zero) ≡ Bn c`（`refl`） | 孩子 c+1 进 tt 后的底与孩子 c 的底逐字相同，对一切塔项 |
| `lhs-form` | `(c : Tr (tw n)) → ψ₀ (tw (suc n)) on (lhs c) ≡ limc⁺ (λ k → row c (iter (chain c) zero k))`（`refl`） | Ω 树的折叠是孩子 c 一列树的部分和极限 |
| `Absorb.absorb` | `readRW (proj₁ (limc⁺ R)) ≼ readRW (proj₁ (Fd Yw))`，前提 `dom : ∀ n c → a ⊢ zero ◃ c → readRW (proj₁ (R n)) ≼ readRW (proj₁ (Fd (Sf n c)))`；对一切后继形状层号、证据、底 | YiInv 的 `absorb` 移植到精简块 |
| `Kid.inv` / `Kid.inv⁺` | `val (tw (suc n)) on (lhs c) ≼ val (tw (suc n)) on (up βn c Yw Yw-nz)` / `L.suc (val (tw (suc n)) on (lhs c)) ≼ val (tw (suc n)) on (up βn c (suc Yw) (z◃ Yw ◃s))` | 倒置推广到一切塔项与一切后继孩子 |
| `Kid.¬mono` | `(D : Dom) → D (tw (suc n)) on βn c (suc Yw , z◃ Yw ◃s) → KidMono D → ⊥` | 含 Yw+1 的域上判据不成立 |
| `Kid.Ωmono` | `val (tw (suc n)) on (up βn c (proj₁ (Ωt (hn c))) (proj₂ (Ωt (hn c)))) ≼ val (tw (suc n)) on (lhs c)` | 规范域版在同一处成立 |

##### 4. 第一个障碍
没有遇到过不去的检查器错误。以下情形未覆盖，属于没有尝试，不是被挡住：
- **孩子 c 是零或极限：** `Absorb` 只对后继形状的层号写了。极限孩子的层号是 `nd sL _`，要先有 ℕ 极限形状上的 `Tw`/`Yw` 构造（槽位取哪个是第一个要定的）。
- **左边 x 不是 β：** `base-same` 靠 x 是闭项才是 `refl`。一般的 x 要先证一条引理：ψ 对逐点相等的底给出相同的值。
- **c′ 不是 c+1：** 要先证 `Ωmono` 或倒置沿多步串联的引理。

##### 5. 偏离与事故；没读、只凭转述引用的东西
- **偏离：**
  - 多建了一个文件 `YiKidGen`（同前缀）。
  - 定稿前把 `Unb` 的量化从 "一切值 u" 改为 "同层的一切树 t"，因为 `readRW` 不满射到 `Ordᶜ`。
  - 采纳了主审转来的建议：量化域参数化，在精简块上重做 `child-all-false`。
- **事故：**
  - `/usr/bin/time` 在沙箱里不可用（退出 1），内存改用 `+RTS -s` 读取。
  - 其余失败只是作用域与 pun 的小错，一次修好。
- **没读 / 只凭转述：**
  - YiInv 的回报原文 `probes/Survey/Reports-2026-11-12/YiInv.md` 没读。
  - `YiNew2Key` 只读了文首并检索了 `child-all-false`、`grow`，没有自己编译。
  - "记号在 Y* 处有平台、ψ₀(Ω_Ω+Ω₂) = ψ₀(Ω_Ω+Y*)" 是我的判断，依据 YiInv 文首的说法与通常的 Buchholz 型闭包，没有查 `OrdinalNotationsGuide.md`。
  - YiBR 的 `S`、`cΩ`、`ψ₀-R`、`rel≅` 与 F2 的 `inversion`、`inversion⁺` 经现有接口引用，我没有冷编它们。

**建议记进 IdeaLedger：**
- 判据 `KidMono` 与它的三条一般否定。
- "一切树版太宽" 与 "含链极限后继的域对后继严格的折叠太宽"，第二条依据记号平台，是判断。
- `OnlyΩ` 版作为候选验收判据。
