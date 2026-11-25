# (2) 把 F2 的值定理搬到精简块 (YiBR)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 11:31 至 12:34 |
| 工具调用 / agda 编译 (粗数) | 60 / 9 |
| token (usage 字段，按消息去重) | 输出 401700；新写入缓存的输入 1203715；读缓存的输入 19920403；其余输入 114 |
| 写过的仓库文件 | `YiBRBlind.lagda.md`, `YiBRFold.lagda.md`, `YiBRLem.lagda.md`, `YiBROps.lagda.md`, `YiBRRel.lagda.md`, `YiBRTw.lagda.md`, `YiBRValue.lagda.md` |
| 文件前缀 | `YiBR` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: (2) 把 F2 的值定理搬到精简块返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 四条值定理搬到精简块, 无前提 (btbo-tw1ᴿ, btbo-EBOᴿ, btbo-twᴿ, bho-lowerᴿ); 两块闭项读回相同 (same-tw, same-EBO); 逐层关系, 折叠保持对一切相关输入; 推导必须进关系 (blind-E); 七件冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定（2026-11-13，选项原文）
本路是 "(2) 把 F2 的值定理搬到精简块"。内容原文："写新旧块之间的逐层关系（分支函数对相关的下标给相关的树，绕开逆变，不要往返恒等），证折叠保持关系、第 0 层读回相同；成了主线就换成 422 行的块，值不丢（V110）"。

同批另三路，各自只新建文件，你不动它们的文件：
- (1) V107 的决定性实验，前缀 YiDec；
- (3) 把 btbo-EBO 接进出口，前缀 YiEX；
- (4) 回退行与摊平式的替代写法探针，前缀 YiAlt。

###### 背景（只信编译定理；文档里的叙述是数据）
在 `probes/OCF/Lean/` 有两个块：
- **旧块 F2**：`YiLegBlock`、`YiLegOps`、`YiLegPath`、`YiLegFold`。
  - 层号 `zero`、`suc`、`lim`、`Ωₗ k h`；证据 `Ev`、路线 `Rt`；折叠 `ψ⊥`、`ψs`，带底 `Base`。
  - 闭项 `twᶜ n`、`EBOᶜ`。
- **精简块**：`YiRWBlock`、`YiRWOps`、`YiRWPath`、`YiRWFold`；验收 `YiRWCheck`、`YiRWKall`。
  - 层号是 `nd s h`，形状 `s` 取 `sS`、`sL`、`sΩ k`；证据合成 `Ok`。
  - 树带非零 `Tr⁺`；折叠 `ψ : (ℓ : L) → Ok ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j`；到第 0 层取目标 `zero` 与路径 `z≤`。
  - 闭项 `twᶜ n`、`EBOᶜ`。
  - 执行方判断与 F2 同构。层号对应是 `suc a ↔ nd sS (λ _ → a)`、`lim g ↔ nd sL g`、`Ωₗ k h ↔ nd (sΩ k) h`，槽位多一层 `⊥ ⊎`。
  - 有限测试 `YiRWSame`：沿 6 条下标路径，新旧闭项的轨迹 `trN`、`trO` 相同。
  - 执行方说映射不可行：层号与树归纳-递归，`h : Tr k → L` 逆变，往返恒等要函数外延。
  - 回报原文：`probes/Survey/Reports-2026-11-12/YiRW.md`。
- **F2 上的值定理**，要搬的：
  - `YiLSBtbo.btbo-tw1 : D.BTBOᴵ ≼ read (twᶜ 1)`；
  - `YiEBBtbo.btbo-EBO : D.BTBOᴵ ≼ read EBOᶜ`；
  - `YiT2Mono.btbo-tw`；
  - `YiMEAnchor.bho-lowerᴹ`。
  - 读回 `YiLSRead.read : Tr zero → L.Ordᶜ L.zero`，逐构造子：零、后继、ℕ 极限。

###### 要做
1. **逐层关系**，用关系不用映射：
   - 层号的关系 `Rℓ : L_RW → L_F2 → Set`；
   - 各层树的关系 `Rt : Tr_RW ℓ → Tr_F2 ℓ′ → Set`，参数是相关的层号；
   - Ω 结点处：对相关的分支下标给相关的树；ℕ 极限的步进推导不进关系；
   - 证据、路线、底、路径也给关系。
   - 不要往返恒等，不要函数外延。
2. **闭项相关**：塔各项、Λ 的层号相关；`twᶜ n`、`EBOᶜ` 两边相关。
3. **折叠保持关系**：两边的折叠，在相关的输入上给相关的输出。逐行对应，可以借助 `YiRWCheck` 与 `YiLegCheck`/`YiLPIface` 的行律。
4. **第 0 层读回相同**：给精简块写一个读回 `readRW`，证相关的第 0 层树读回 `≅`。
5. **搬值**：得到精简块上的
   - `D.BTBOᴵ ≼ readRW (twᶜ 1)`；
   - `D.BTBOᴵ ≼ readRW EBOᶜ`；
   - 塔各项 ≥ BTBO；
   - 若容易，ψ₀(Ω₂) 锚点也搬。
   - 若 3 只能对规范输入（塔、Λ 的读回域）证，就只对规范输入证，写清量化域（`AGENTS.md`："量化域先取带证据的读回域"）。
6. 证到第一个挡住的引理也算交付。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiBR`（模块名 `OCF.Lean.YiBR…`）。不改任何已有文件，不碰 `src/`、`archive/`。值的文件是验收文件，文首标 "验收文件"。
- 两个块都一行不改。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"（本路的要求是不用）。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G；若导入 `YiLSBtbo` 一类（依赖 `YiLSRel`，冷编约 6.9G），用 8G。
  - 冷编只删自己模块的接口，写字面路径；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
- 临时目录：`<实验目录>/agents/br`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；需要函数外延或 K；堆仍耗尽。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：搬成了哪些值定理，主线能否换成精简块；列关键路径上暴露的问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 关系的逐字定义；量化域。
5. 第一个障碍，精确到引理。
6. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 1. 判决

**结论：要搬的四条值定理都已搬到精简块，都是无前提的编译定理。** 精简块的闭项与 F2 的同名闭项读回 `≅`（`same-tw : ∀ n`，`same-EBO`）。所以就这四条以及凡是经 `YiLSRead.read` 读 `twᶜ n`、`EBOᶜ` 的 F2 值定理而言，主线换成精简块，值不丢：每条一行 `up≼` 就能搬过来（V110 在这个范围内成立）。

**偏离简报一处：ℕ 极限的步进推导进了关系（`RelD`）。** 这一处有编译过的否定作依据（`YiBRBlind.blind-E`）。理由：证据里 ℕ 极限层号的相邻路径由树的推导经 `◃→⊑` 读出；两边的折叠沿这些路径比较孩子（`way`、`psh`、`emb`）。推导不进关系时，塔第 1 项在一对"只差推导"的孩子处，证据关系不成立。

**关系是关系，不是映射。** 层号 `RelL`、树 `RelT`、推导 `RelD`、槽位 `RelP`、分支 `RelB`、路径 `RelW`/`RelV`、证据 `RelE`、底 `RelBase`。Ω 结点处对相关的分支给相关的树。不用往返恒等，不用函数外延，不用 K。

**量化域：** 折叠保持（`A`、`Am`、`S`、`Sm`）对一切相关的证据、底、路径、底树与树成立，不限于塔与 Λ。

关键路径上暴露的问题：

| 问题 | 位置 | 档 |
|---|---|---|
| 推导不进关系时，塔的证据关系在孩子 c₁~c₂ 处不成立；推导必须进关系 | `YiBRBlind.blind-W`、`blind-E`、`b0`、`sep` | 编译定理（否定） |
| 精简块的 sS 形状有两种路径（`inc tt v`、`inu vs`），F2 只有 `ins`；两者都对 `ins`，各折叠对两者处理相同 | `RelW` 的 `wincS`/`winuS` | 编译定理（`kp-R`、`S` 过检查） |
| 两块接 ℕ 极限层号的比较路径方式不同（`from0` 对 `rt`），项不同但相关 | `YiBRLem.way-R`、`rt-s`、`idl-R` | 编译定理 |
| 递归调用放在 `with` 里时，停机检查器看不到证据关系保持不变 | `YiBRFold` 的 sL 各行 | 实测，已绕开：先在 `with` 外算好，再抽象进去 |
| `YiMEBase` 另有一个同文不同名的 `read`，要另写一条 `rel≅ᴹ`；别的模块若也自带读回，同样各要几行 | `YiBRValue.rel≅ᴹ` | 实测 |
| F2 上对一切底或一切输入量化的引理（如 `YiLSFold.lower`），不能由本关系直接得出精简块上的同类 ∀ 陈述：关系只对已有的 F2 相关输入给结论，没有从精简块到 F2 的映射 | — | 判断 |

#### 2. 文件表

- 全部在 `<仓库>/probes/OCF/Lean/`。
- 冷编方式：删自己的 `.agdai` 后按依赖顺序逐个编译，日志里只有本模块的 `Checking` 行。
- 代码行数只算 agda 块内的非空行。

| 文件 | 代码行 | 冷编退出码 | 最大驻留（堆上限） |
|---|---|---|---|
| `YiBRRel.lagda.md`（定义） | 149 | 0 | 0.20 GB（6G） |
| `YiBRLem.lagda.md` | 174 | 0 | 0.48 GB（6G） |
| `YiBROps.lagda.md` | 196 | 0 | 0.92 GB（6G） |
| `YiBRFold.lagda.md` | 424 | 0 | 1.99 GB（8G） |
| `YiBRTw.lagda.md` | 151 | 0 | 0.56 GB（8G） |
| `YiBRValue.lagda.md`（验收文件） | 49 | 0 | 1.12 GB（8G） |
| `YiBRBlind.lagda.md` | 55 | 0 | 0.16 GB（6G） |

- 合计 1198 行代码。
- 禁用构造检索为 0：postulate、洞、TERMINATING、NO_POSITIVITY、trustMe、cubical、irrelevant-projections、funext、本机路径。
- 选项行都是 `--safe --without-K --lossy-unification`。

#### 3. 定理表（全部是编译定理）

**搬值（`YiBRValue`，验收文件）**

- `btbo-tw1ᴿ : D.BTBOᴵ ≼ readRW (twᶜ 1)`：精简块塔第 1 项不低于 BTBO。
- `btbo-EBOᴿ : D.BTBOᴵ ≼ readRW EBOᶜ`：精简块终点不低于 BTBO。
- `btbo-twᴿ : (n : ℕ) → D.BTBOᴵ ≼ readRW (twᶜ (suc n))`：塔各项不低于 BTBO。
- `bho-lowerᴿ : (h : E.HC t₂) → Rt h ≼ readRW (proj₁ (ψ₀ two Ok-two (proj₁ (Ωt two))))`：ψ₀(Ω₂) 锚点搬到精简块。`two = nd sS (λ _ → nd sS (λ _ → zero))` 在 `YiBRTw` 里定义。
- `same-tw : (n : ℕ) → readRW (twᶜ n) L.≅ read (F.twᶜ n)`、`same-EBO : readRW EBOᶜ L.≅ read F.EBOᶜ`：两块闭项读回结构相等。
- `rel≅ : {x : Tr zero} {x′ : F.Tr F.zero} → RelT zero F.zero x x′ → readRW x L.≅ read x′`：第 0 层相关的树读回相同（`rel≅ᴹ` 是对 `YiMEBase.read` 的同文版本）。

**闭项（`YiBRTw`）**

- `twᶜ-R : (n : ℕ) → RelT zero F.zero (twᶜ n) (F.twᶜ n)`。
- `EBOᶜ-R : RelT zero F.zero EBOᶜ F.EBOᶜ`。
- `two-R`：层号 2 的 Ω 树的折叠相关。
- `tw-L : (n : ℕ) → RelL (tw n) (F.tw n)`、`Λ-L : RelL Λ F.Λ`：层号相关。
- `tw-E : (n : ℕ) → RelE (tw n) (F.tw n) (Ok-tw n) (F.Ev-tw n) (F.Rt-tw n)`、`Λ-E : RelE Λ F.Λ Ok-Λ F.Ev-Λ F.Rt-Λ`：证据相关。
- `↑-L`、`◃→⊑-V`、`⊕-E`、`↑-EO`：读出的层号、路径、偏移证据相关。

**折叠保持（`YiBRFold`）**

```
A : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
  → (β : Tr⁺ zero) → RelT zero F.zero (proj₁ β) (F.b⊥ B′) → RelD zero F.zero (proj₂ β) (F.n⊥ B′)
  → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′
  → RelT zero F.zero (proj₁ (ψ ℓ o B zero (z≤ ℓ) β x)) (F.ψ⊥ ℓ′ ε ρ B′ x′)
  × RelD zero F.zero (proj₂ (ψ ℓ o B zero (z≤ ℓ) β x)) (F.nz⊥ ℓ′ ε ρ B′ x′)
S : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → (B : Base ℓ) (B′ : F.Base ℓ′) → RelBase ℓ ℓ′ B B′
  → ∀ {j j′} {w : j ≤ ℓ} {w′ : F._≤_ j′ ℓ′} → RelW w w′
  → (β : Tr⁺ j) {β′ : F.Tr j′} {nβ : F._⊢_◃_ j′ F.zero β′} → RelT j j′ (proj₁ β) β′ → RelD j j′ (proj₂ β) nβ
  → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′
  → RelT j j′ (proj₁ (ψ ℓ o B j w β x)) (F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ x′)
  × RelD j j′ (proj₂ (ψ ℓ o B j w β x)) (F.nzs ℓ′ ε ρ B′ j′ w′ β′ nβ x′)
```

- `A`：目标第 0 层、路径 `z≤` 的折叠对 F2 的 `ψ⊥`，值与非零都相关。
- `S`：一般目标、相关路径的折叠对 `ψs`，值与非零都相关。
- `Am`、`Sm`：同样的前提，加 `RelD ℓ ℓ′ d d′`，得 `RelD zero F.zero (mono ℓ o B zero (z≤ ℓ) β d) (F.mono⊥ ℓ′ ε ρ B′ d′)` 与 `RelD j j′ (mono ℓ o B j w β d) (F.monos ℓ′ ε ρ B′ j′ w′ β′ nβ d′)`，即单调推导相关。
- `kp-R`：保留判定相关。对任意谓词 Φ，若保留时两边的槽位与换型相关则 Φ 成立、不保留时 Φ 对默认值成立，则 Φ 对 `(kp ℓ o p w)`、`(F.kp ℓ′ ε ρ p′ w′ K d)`、`(F.kp-ind ℓ′ ε ρ p′ w′ Q {K} {d} hk hd)` 成立。精简块的 `Maybe` 由此对上 F2 的续延 `kp` 与它的归纳原理 `kp-ind`，一条引理同时供值、非零、单调三处用。逐字陈述在文件里。

**运算与基础（`YiBROps`、`YiBRLem`）**

- `+-R`、`+m-R`、`next-R`、`limc-R`：加法、`next`、部分和极限保持关系（值与推导）。
- `zl-R`、`zs-R`：零的比较与"非零"推导相关。
- `Ωt-R`、`Ωn-R`：各层的 Ω 树及其非零推导相关。
- `ι-R`、`ιm-R`：第 0 层的嵌入相关。
- `emb-R`、`emb-mono-R`：孩子树沿路径搬进高层相关。
- `Up-R`、`Upm-R`：上折相关。
- `at-L`、`E-at`、`fromBr-R`、`br0-R`、`posW-R`、`psh-R`、`pshBr-R`、`∙-R`、`way-R`、`mv-R`、`mvBr-R`：槽位、路径、比较、下行链的搬运相关。
- 白话：两块对应的运算在相关输入上给相关输出。

**否定（`YiBRBlind`）**

- `b0 : B0 c₁ c₂`：不看推导时这一对相关。B0 是只比 zero/suc/lim、不看推导的关系；c₁ 是精简块的树，c₂ 是 F2 的树，同为列 0, ω+1, ω+2, …，第 0 步的推导不同。
- `blind-W : ¬ RelW (proj₁ (proj₂ (Ok-tw 1) c₁) 0) (proj₂ (proj₂ (F.Rt-tw 1) c₂) 0)`：两边第 0 条相邻路径一边读成 `inc tt (inc 0 self)`，一边读成 `ins (inl 1 (ins self))`，不相关。
- `blind-E : ¬ RelE (tw 0 ⊕ ↑ (tw 0) c₁) (F.tw 0 F.⊕ F.↑ (F.tw 0) c₂) (proj₂ (Ok-tw 1) c₁) (proj₂ (proj₂ (F.Ev-tw 1) c₂)) (proj₂ (F.Rt-tw 1) c₂)`：所以塔第 1 项在这一对孩子处的证据关系不成立。
- `sep : ¬ RelT zero F.zero c₁ c₂`：本路的 `RelT` 把这一对分开。

#### 4. 关系的逐字定义（`YiBRRel`）与量化域

```
RelT ℓ ℓ′ zero         x′ = IsZ x′
RelT ℓ ℓ′ (suc x)      x′ = IsS (RelT ℓ ℓ′ x) x′
RelT ℓ ℓ′ (lim f a)    x′ = IsL (λ f′ a′ → ((n : ℕ) → RelT ℓ ℓ′ (f n) (f′ n)) × ((n : ℕ) → RelD ℓ ℓ′ (a n) (a′ n))) x′
RelT ℓ ℓ′ (Ω p g)      x′ = IsΩ (λ p′ g′ → RelP ℓ ℓ′ p p′
    × ((z : Br ℓ p) (z′ : F.Br ℓ′ p′) → RelB ℓ ℓ′ p p′ z z′ → RelT ℓ ℓ′ (g z) (g′ z′))) x′
RelT ℓ ℓ′ (up x c y e) x′ = IsU (λ x₀ c′ y′ e′ → RelT ℓ ℓ′ x x₀ × RelU ℓ ℓ′ c y e c′ y′ e′) x′
RelU (nd sS h)     (F.suc a)    c y e c′ y′ e′ = RelT (h c) a y y′ × RelD (h c) a e e′
RelU (nd sL g)     (F.lim g′)   n y e n′ y′ e′ = (n ≡ n′) × RelT (g n) (g′ n′) y y′ × RelD (g n) (g′ n′) e e′
RelU (nd (sΩ k) h) (F.Ωₗ k′ h′) c y e c′ y′ e′ = RelT k k′ c c′ × RelT (h c) (h′ c′) y y′ × RelD (h c) (h′ c′) e e′
RelD ℓ ℓ′ ◃s d′ = DS d′ ;  RelD ℓ ℓ′ (◃l n) d′ = DL n d′
RelD ℓ ℓ′ (◃w {p = p} {g = g}) d′ = DW (λ p′ g′ → RelP ℓ ℓ′ p p′ × ((z : Br ℓ p) (z′ : F.Br ℓ′ p′) → RelB ℓ ℓ′ p p′ z z′ → RelT ℓ ℓ′ (g z) (g′ z′))) d′
RelD ℓ ℓ′ (◃u x c y e) d′ = DU (λ x′ c′ y′ e′ → RelT ℓ ℓ′ x x′ × RelU ℓ ℓ′ c y e c′ y′ e′) d′
RelD ℓ ℓ′ (◃c x c r)   d′ = DC (λ x′ c′ r′ → RelT ℓ ℓ′ x x′ × RelDc ℓ ℓ′ c r c′ r′) d′
RelD ℓ ℓ′ (◃t d e)     d′ = DT (λ d₁ e₁ → RelD ℓ ℓ′ d d₁ × RelD ℓ ℓ′ e e₁) d′
RelP (nd sS h) (F.suc a) (inj₂ (c , t)) t′ = RelP⁼ (h c) a t t′
RelP (nd sL g) (F.lim g′) (inj₂ (n , t)) p′ = IΣₙ n (RelP⁼ (g n) (g′ n) t) p′
RelP (nd (sΩ k) h) (F.Ωₗ k′ h′) (inj₁ t) p′ = I₁ (RelP⁼ k k′ t) p′
RelP (nd (sΩ k) h) (F.Ωₗ k′ h′) (inj₂ (c , t)) p′ = I₂ (IΣ (λ c′ t′ → RelT k k′ c c′ × RelP⁼ (h c) (h′ c′) t t′)) p′
RelB⁼ a a′ (inj₁ _) (inj₁ _) z z′ = RelT a a′ z z′   （RelB 沿槽位下降到这里；不相配的情形是 ⊥）
data RelL : lz ; lS : RelL (h tt) a → RelL (nd sS h) (F.suc a) ; lL : (∀ n → RelL (g n) (g′ n)) → …
  lΩ : RelL k k′ → ((c : Tr k) (c′ : F.Tr k′) → RelT k k′ c c′ → RelL (h c) (h′ c′)) → RelL (nd (sΩ k) h) (F.Ωₗ k′ h′)
data RelW : wself ; wincS/winuS (对 F.ins) ; wincL n / winuL (对 F.inl n / F.inlu) ;
  wincΩ : RelT k k′ c c′ → RelW v v′ → RelW (inc c v) (F.inb c′ v′) ;
  winuΩ : ((c c′) → RelT k k′ c c′ → RelW (vs c) (vs′ c′)) → RelW (inu vs) (F.inu vs′) ; wink
data RelE : ez ; eS : RelE (h tt) a (proj₂ o tt) ε ρ → … ;
  eL : ((n) → RelW (proj₁ o n) (proj₂ ρ n)) → ((n) → RelE (g n) (g′ n) (proj₂ o n) (ε n) (proj₁ ρ n)) → … ;
  eΩ : RelE k k′ (proj₁ (proj₁ o)) (proj₁ ε) (proj₁ ρ)
     → ((c c′) → RelT k k′ c c′ → RelW (proj₂ (proj₁ o) c) (proj₁ (proj₂ ε c′)))
     → ((c c′) → RelT k k′ c c′ → RelE (h c) (h′ c′) (proj₂ o c) (proj₂ (proj₂ ε c′)) (proj₂ ρ c′)) → …
RelBase ℓ ℓ′ B B′ = (j j′ w w′) → RelW w w′ → RelT j j′ (proj₁ (B j w)) (F.bs B′ j′ w′) × RelD j j′ (proj₂ (B j w)) (F.ns B′ j′ w′)
```

- `RelV` 与 `RelW` 同形，用于 ⊑ 路径，没有 `ink`。
- `RelC` 与 `RelDn` 在 `YiBRRel`、`YiBRLem` 里，用于孩子编号与下行链。
- F2 一侧的构造子由"形状见证"数据（`IsS`、`DL`、`I₂`、`IΣₙ` 等）读出。

**量化域：**

- `A`、`S`、`Am`、`Sm`、`kp-R` 对一切相关输入成立。
- 闭项的关系只对塔各项、Λ、层号 2。
- 值定理只对闭项。

#### 5. 第一个障碍

没有未解决的障碍，要做的 1 到 5 都已编译通过。过程中挡过两处，都已解决：

- **(a) 证据里的相邻路径来自推导。** `RelE (tw (suc n))` 对相关孩子 c, c′ 要求相邻路径相关；推导不进关系时这一条不成立（`blind-E`）。所以推导进了关系。
- **(b) 停机检查。** 递归调用写在 `with` 生成的辅助函数里时，证据关系参数看起来不是"不变"，size-change 判不出下降。解法是把 `S re₀ … rx` 和 `cL re₀ …` 写成 `with` 的被抽象项（as-pattern 绑定的 `re₀`），辅助函数里只剩对孩子证据 `re n` 的调用。

#### 6. 偏离与事故，没读、只凭转述引用的东西

**偏离：**
- 推导进了关系，与简报原文"ℕ 极限的步进推导不进关系"相反；依据是编译定理 `YiBRBlind.blind-E`。
- 层号、证据、路径的关系写成数据（`RelL`、`RelE`、`RelW`、`RelV`），为的是免去不相配情形的穷举，不影响内容。

**事故：**
- 第一次编译用了 `/usr/bin/time -l`，被沙箱拦下（sysctl），返回 1；之后改用 `+RTS -s` 记内存。
- 编译命令包在临时目录的 `ck.sh` 里：与简报的命令相同，只多 `-s`，退出码不经管道。
- 一次性试验在临时目录 `<实验目录>/agents/br/`：`t/WithT.agda`（`with` 能看穿定义）、`t/TermT.agda`（函数变量的应用可作递归参数）、`t2/OCF/Lean/YiBRFoldT.lagda.md`（停机诊断用的副本）。
- 没有改动任何已有文件。

**只凭陈述引用、没有复核证明的：**
- F2 的值定理 `YiLSBtbo.btbo-tw1`、`YiEBBtbo.btbo-EBO`、`YiT2Mono.btbo-tw`、`YiMEAnchor.bho-lowerᴹ`（及 `t₂`、`YiMEBase.Rt`、`E.HC`）：只经检索读了陈述。`YiBRValue` 用的是它们现有的 `.agdai`，我没有重编它们，也没有删它们的接口。
- 简报指的回报 `probes/Survey/Reports-2026-11-12/YiRW.md`：没有读。
- `YiRWCheck`、`YiLegCheck`、`YiLPIface`：没有用到，没有读。
- 两个块的 Block、Ops、Path、Fold 共 8 个文件：通读过。

**判断（非定理）：** 我推测，若不把推导放进关系，`YiRWSame` 的有限测试之所以没有出现分歧，是因为两块用对应的代码生成推导。这一点没有证明。
