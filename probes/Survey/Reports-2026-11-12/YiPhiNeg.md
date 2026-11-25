# F1 的配对否定 (YiPhiNeg)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 06:51 至 07:20 |
| 工具调用 / agda 编译 (粗数) | 46 / 8 |
| token (usage 字段，按消息去重) | 输出 183494；新写入缓存的输入 366655；读缓存的输入 6034044；其余输入 70 |
| 写过的仓库文件 | `YiPhiNegB.lagda.md`, `YiPhiNegDom.lagda.md`, `YiPhiNegK.lagda.md`, `YiPhiNegKSem.lagda.md` |
| 文件前缀 | `YiPhiNeg` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: F4, F3 → F2, F1 的配对否定返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | kall-phi (k 侧对一切孩子保留, 加强可满足); fullSem→lpo (按层号字面相等判能保留推出 LPO, 探针不在规范域); wdec, wdecα (分支侧同支交接加异支回退弱判定字面相等, 规范域内), wlpo (加 Funext 得 WLPO), viaE→dec; 证据量化过宽 (谓词太宽); 四件冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方：对一份已定稿的接口写**配对否定**。全程用中文写文件与回报。主审会从头冷编译复核你交的每个文件，只认编译过的定理。

作者 2026-11-13 的选择（选项工具）原文："F1 把 φ 并进空白页的折叠"。说明里写："接口定稿后按规则配一路否定。" 模型：作者定 "F1 用 Fable 5.2，其余 Opus 5.5"，你是 Opus 5.5。AGENTS.md 的规则："新路线派一路构造、一路对同一接口写否定，共用接口文件（定稿后只增不改）"。构造那一路（YiPhi，Fable 5.2）已发 "接口定稿"，现在在做自查与行数，可能还会动它的实现文件，但不会改接口。

###### 接口与实例（只信编译定理）
- **接口** `probes/OCF/Lean/YiPhiIface.lagda.md` 的记录 `Iface`，字段：
  - 两个折叠 `ψ⊥`、`ψs`；
  - 嵌入一致 `J2-suc`、`J2-lim`、`J2-limu`、`J2-Ωk`、`J2-Ωu`、`J2⊥-suc`、`J2⊥-lim`、`J2⊥-Ω`；
  - 单调 `mono⊥`、`monos`；保持合法 `pres⊥`、`press`；
  - 闭项合法 `tw-leg`、`EBO-leg`；
  - k 侧链步 `kstep`：塔第 n+1 项，目标是下标层 tw n，嵌入在第一个孩子 c = 0 里的 Ω 结点原样保留。

  路径 `_≤_`（含 `inlu`、`inu`）、层号证据 `Ev`（`Ωₗ k h` 的证据给每个孩子一条 k ≤ h c 的路径）、`∙`、`Base` 在 `YiPhiBlock`；序与合法性取自 `YiFreshLegal`。
- **实例** `YiPhiCheck.phi`，实现在 `YiPhiFold`、`YiPhiLegal`。
- **背景**：
  - 空白页的块：`YiFreshBlock`、`YiFreshFold`、`YiFreshLegal`、`YiFreshCheck`。
  - 第十三次审查 `probes/Survey/RR13-CommonWall.md`，以及附件 `probes/Survey/Reports-2026-11-12/attachments/Review13-*.agda.txt`，尤其 `R13Base`、`R13Diag`、`R13Top`。
  - 已知的编译否定：`probes/OCF/Lean/YiUniNegStep.lagda.md` 的 `step-full→lpo`（链第一步折到下标层的派发若 "能保留处都保留" 就推出 LPO）；`YiUniNegCmp.cmp-full→lpo`；`YiCtxNeg.diag1→dec`；壁垒 `probes/OCF/Barrier.lagda.md`。

###### 要做（每条写成编译定理，或写明 "未走通"）
接口已有实例，所以 "接口不可满足" 不成立。你的任务是划出它**不保证什么**、**加强到哪里就不可能**：

1. **k 侧对一切孩子**：`kstep` 只说 c = 0。
   - 写出 c ≠ 0 时的加强：孩子层 tw n ⊕ ↑c 里、槽位其实在基底 tw n 里的结点，在折到 tw n 时保留。
   - (a) 在实例 `phi` 上编一个有限测试，看它保留还是折掉。
   - (b) 试证：这一加强对一切 c 与一切这样的结点，连同接口的律，推出 LPO（或 WLPO、⊥）。仿 `step-full→lpo` 的探针办法。
   - 也可能证出反面：给出满足加强的折叠。无论哪一边，如实写。
2. **分支侧**：接口里没有 "目标在分支 c′、嵌入在分支 c" 的律。
   - 写出这样一条律 `J2-Ωb` 的陈述。
   - 证明：任何满足它（加上必要的接口字段）的折叠都要判定 c ≡ c′，仿 `R13Diag.diag→dec` 与 `YiCtxNeg.diag1→dec`，接到这份接口的类型上。
   - 结论陈述精确：是 "判定字面相等"，还是更强的不可能性。
3. **量化域与证据**：`Ev` 是层号上的 "基底加偏移" 证据。
   - 检查律里的量化：对一切树、对一切 `Ev`、对一切 `Base`、对一切偏移 β。是否有律对退化输入（常值极限、不合法的树、不合法的底）说得过宽，而实例只是碰巧满足？
   - 按 AGENTS，"反例对象不在读回域内的否定，读作 '谓词太宽'"。写出的每条否定都要说它的对象在不在规范域内。规范域可以用 `R13Top` 的 `Top` 判断。
4. **每条否定定理与条件定理的每个前提**，给一个实例或说明为何可满足（AGENTS："前提要可满足"）。

###### 先读什么
- `AGENTS.md` 全篇。
- `YiPhiIface` 全读；`YiPhiBlock` 全读；`YiPhiCheck` 的 `phi` 与有限测试（检索）；`YiPhiFold` 全读。
- `YiUniNegStep`（`step-full→lpo`、`Full`、探针）与 `YiCtxNeg`（`diag1→dec`）的陈述与证明。
- 附件 `Review13-R13Diag.agda.txt`、`Review13-R13Base.agda.txt`。
- `probes/Survey/EBOHandbook.md` §4.1 到 §4.5。

查签名用检索，不整篇读大文件。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiPhiNeg`（模块名 `OCF.Lean.YiPhiNeg…`），文首标 "验收文件（否定）"。不改任何已有文件，包括 YiPhi 的文件。不碰 `src/`、`archive/`。
- 中文 literate Agda（`.lagda.md`）。每个模块文首不超过 5 行：判决与档位，否定的确切是什么，不否定什么。代码之间的文字只写范围与不显然的定义理由。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的结论标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G（另有三路在编译）。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。日志落文件，只看首个错误附近。
  - 不用 `--ignore-interfaces`。要冷编译只删你自己模块的接口（`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`），写字面的精确路径，不用通配，不用变量拼路径。**不要删 YiPhi 或别人模块的 `.agdai`。**
- 临时目录：`<实验目录>/agents/phineg`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不写 `/tmp` 的别处，不装包，不提交，不推送。
- **停下的条件**：同一处两次重新设计仍过不了检查器；需要函数外延或 K（作前提除外）；6G 仍耗尽。没有编译的否定时只写 "未走通"。归到已知的墙之前，逐条核机制：有没有折叠，有没有值，失败的是哪个字段。
- **过程要求**：读完上面的文件后尽快动手，第一个文件在 30 分钟内写出并编译；每次回复都要有工具调用，不要在一次回复里只思考。
- **结束前自查**：每个文件删自己的接口后冷编译，退出码 0，日志里只有你自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：1 到 3 各得到什么（编译否定、有限测试、未走通）；一段话说这份接口的边界在哪里。
2. 文件表：文件、代码行数、冷编译退出码、常驻内存峰值。
3. 定理表：名字、逐字的陈述、一句白话、文件、档（编译定理 / 条件定理 / 有限测试 / 判断），对象在不在规范域。
4. 每条否定的前提的可满足实例。
5. 与已知否定的关系（逐条核机制）。
6. 偏离与事故。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 1. 判决

1. **k 侧对一切孩子 (任务 1)。结果是反面：加强可以满足，不推出 LPO。**
   - 加强写成 `KAll`：塔第 n+1 项折到 tw n，孩子 c 任意，孩子层 tw n ⊕ ↑c 里的结点槽位带见证 `InB`，且严格在基底里，结论是输出以同一个基底槽位为根 (保留)。
   - (a) 有限测试：4 个样本保留，其中 2 个核对了交出的槽位；2 个槽位层号等于目标层的样本折叠。
   - (b) 编译定理 `kall-phi : KAll phi`，以及 `kall-sat : Σ Iface KAll`。所以 KAll 连同接口推不出 LPO，也推不出 ⊥。
   - 按 `step-full→lpo` 的探针办法，另写了一个加强 `FullSem`：按层号字面相等判 "能保留"。编译定理 `fullSem→lpo : FullSem I → LPO`，且 `phi-not-fullSem`。探针不在规范域。
2. **分支侧 (任务 2)。编译否定。**
   - 律是 `J2-Ωb` (同一分支变量 c 上交给孩子) 加 `Ωb-off` (分支不同时按 phi 的回退)，再加接口自己的字段 `J2-limu`、`kstep`、`pres⊥`。
   - 结论：对塔 tw 2 的一个合法规范下标 c₀ 与一切 c′，弱判定 c₀ ≡ c′，即 ¬ 或 ¬¬ (`wdec`)。
   - 因而对一切 α：α 处处为假，或 c₀ 与 cα α 字面不等 (`wdecα`)。
   - 加 Funext 作前提得 WLPO (`wlpo`，条件定理)。
   - 若派发经由两个下标算出的同支证据 E (`ViaE`)，结论是字面相等可判定 (`viaE→dec`，与 `R13Diag.diag→dec` 同)。
   - 精确陈述：一般折叠只得到 "弱判定字面相等"，不是 LPO 或 ⊥。
3. **量化域 (任务 3)。有限测试与编译定理。**
   - `Ev` 量化过宽：同一层号、同一棵树、同一目标，证据路径取 `inu` 时 phi 保留，取 `inb zero` 时折叠 (`ev-kept`, `ev-folds`)。两份证据下接口的律都成立，律不区分证据。对象不在规范域，读作 "谓词太宽"。
   - 规范域内 KAll 只涉及 c = 0 与下标层侧的槽位 (`top-inB`)。
   - 逐条读律 (判断)：J2 各律、单调、`kstep` 对一切 ε, B, β 成立，都是定义式或结构归纳，没有找到 "实例只是碰巧满足" 的律。过宽的方向是反的：律不度量保留。
   - 未做：phi 是否保持 `Top`。

**接口的边界。**
- 接口里讲保留的律只有 `kstep` (塔、规范证据、c = 0)。phi 实际对一切 c 都保留在基底里的结点 (`kall-phi`)，这一条可以作为只增的字段加进接口 (判断，由作者或主审定)。
- 不能加强的方向有两个：
  - 按层号相等判保留 (`FullSem` → LPO，只在规范域外被否定)；
  - 分支侧同支交接并在异支回退 (`J2-Ωb` + `Ωb-off` → 规范域内合法下标的弱判定；加 Funext 得 WLPO)。
- 律对一切 `Ev` 量化，非规范证据下的丢失不违反任何律。

#### 2. 文件表

| 文件 | 总行 / 代码非空行 | 冷编译退出码 | GHC 最大驻留 / 总内存 |
|---|---|---|---|
| probes/OCF/Lean/YiPhiNegKSem.lagda.md | 156 / 95 | 0 | 163 MB / 279 MiB |
| probes/OCF/Lean/YiPhiNegK.lagda.md | 185 / 116 | 0 | 183 MB / 334 MiB |
| probes/OCF/Lean/YiPhiNegB.lagda.md | 281 / 182 | 0 | 181 MB / 303 MiB |
| probes/OCF/Lean/YiPhiNegDom.lagda.md | 178 / 113 | 0 | 160 MB / 305 MiB |

- 冷编译方法：删自己的 4 个 `.agdai` 后依次编译，每份日志只有自己模块的 `Checking` 一行。
- 禁用构造检索为 0，本机路径为 0。
- 内存是 RTS `-s` 的数字，不是常驻内存峰值 (见第 6 节)。

#### 3. 定理表

档位记号：编=编译定理，条=条件定理，测=有限测试，判=判断。

**YiPhiNegK**

- `kall-phi : KAll phi`，编。phi 对一切孩子保留基底里的结点。对象：既有规范的 (ibK, ib0)，也有非规范的 (ibS/ibL/ibW)。
  `KAll` 逐字如下：
  ```
  KAll I = (n : ℕ) (B : Base (tw (suc n))) (β : Tr (tw n)) (x : Tr (tw (suc n))) (c : Tr (tw n))
    {t : Pos (tw n ⊕ ↑ (tw n) c)} (G : Br (tw n ⊕ ↑ (tw n) c) t → Tr (tw n ⊕ ↑ (tw n) c))
    (i : InB (tw n) (↑ (tw n) c) t) (p : Pos (tw n)) → prE i (evc n c) ≡ inj₂ p
    → Kept p (Iface.ψs I (tw (suc n)) (Ev-tw (suc n)) B (tw n) (ink self) β (up x c (Ω t G)))
  ```
  其中 `Kept p o = Σ G′, o ≡ Ω p G′`。
- `kall-sat : Σ Iface KAll`，编。加强有实例。
- `lemA`, `lemB`, `child-kept`，编，引理。保留判定沿 `lift` 路径下行到基底。
- 有限测试 `t-top`, `t-top-slot`, `t-inner`, `t-lim`, `t-deep`, `t-deep-slot`, `t-eq-suc`, `t-eq-inner`，测 (`refl`/`tt`)。
  - 例：`t-top : isΩ (out 1 cΩ (inj₁ (inj₁ tt)))`，属规范域。
  - 例：`t-deep-slot : slot (out 2 (Ω pc (λ _ → zero)) (inj₁ (inj₁ tt))) (inj₁ (inj₁ tt)) ≡ pc`。
  - `t-eq-*` 的结点层号等于目标层，结果是折叠。
- `t-top-thm`, `t-lim-thm`，编。测试样本落在 `kall-phi` 的范围内。

**YiPhiNegKSem**

- `fullSem→lpo : (I : Iface) → FullSem I → LPO`，编。按层号相等的 "能保留处都保留" 推出 LPO。对象：规范域外 (孩子层不合法，结点不在顶槽位)。
  `FullSem` 逐字如下：
  ```
  FullSem I = (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (β : Tr k)
    (x : Tr (Ωₗ k h)) (c : Tr k) (t : Pos (h c)) (G : Br (h c) t → Tr (h c))
    → Σ (Pos k) (λ q → at k q ≡ at (h c) t)
    → Σ (Pos k) λ q → Σ (Br k q → Tr k) λ G′ →
        (Iface.ψs I (Ωₗ k h) ε B k (ink self) β (up x c (Ω t G)) ≡ Ω q G′) × (at k q ≡ at (h c) t)
  ```
- `phi-not-fullSem : FullSem phi → ⊥`，编。依据是 `phi-folds : obs (λ _ → true) (Oα phi (λ _ → true)) ≡ false`。

**YiPhiNegB**

`J2-Ωb` 与 `Ωb-off` 逐字如下：
```
J2-Ωb I = … (j : L) (c : Tr k) (w : j ≤ h c) (β : Tr j) (x : Tr (Ωₗ k h)) (y : Tr (h c))
  → ψs (Ωₗ k h) ε B j (inb c w) β (up x c y)
  ≡ ψs (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) j w (ψs (Ωₗ k h) ε B j (inb c w) β x) y
Ωb-off I = … (c c′ : Tr k) (w : j ≤ h c′) … (y : Tr (h c)) → (c ≡ c′ → ⊥)
  → ψs (Ωₗ k h) ε B j (inb c′ w) β (up x c y)
  ≡ ψs (Ωₗ k h) ε B j (inb c′ w) β x + ι j (ψ⊥ (h c) (proj₂ (proj₂ ε c)) (B₀ (h c)) y)
```

- `wdec : (I : Iface) → J2-Ωb I → Ωb-off I → (c′ : Tr (tw 2)) → WDec (c₀ ≡ c′)`，编。其中 `WDec A = (A → ⊥) ⊎ ((A → ⊥) → ⊥)`。规范域内。
- `wdecᵂ`，编。同一结论，第三个前提弱化为 "异支时探针输出不是结点头"。
- `wdecα : … → ∀ α → (∀ n → α n ≡ false) ⊎ (c₀ ≡ cα α → ⊥)`，编。规范域内。
- `wlpo : Funext → (I : Iface) → J2-Ωb I → Ωb-off I → WLPO`，条 (Funext)。
- `viaE→dec : (I : Iface) → J2-Ωb I → ViaE I → (c′ : Tr (tw 2)) → Dec′ (c₀ ≡ c′)`，编。派发经同支证据时，字面相等可判定。
- `off-phi : Ωb-off phi`，`viaE-phi : ViaE phi`，`j2b-const`，编。都是前提的实例。

**YiPhiNegDom**

- `top-inB : ∀ {a b t} (i : InB a b t) → IsTop (a ⊕ b) t → IsK0 i`，编。顶槽位的见证只能是 c = 0 或下标层侧。
- `ev-kept : isΩ (outE ε₁)` 与 `ev-folds : isLim (outE ε₂)`，测。对象在规范域外：有 `nodeE-not-top`；层号不是塔；ε₂ 不是规范证据。
- 探针位置的核对，编：`b-c₀-top`, `b-cα-top`, `b-y₀-top`, `b-c₀-leg`, `b-cα-leg` (NegB 里另有 `legy₀`)，`ksem-not-top`, `ksem-illegal`。
- `Top` 逐字重写了 `R13Top` 在块上的部分。

#### 4. 前提的可满足实例

- `fullSem→lpo`：I 取 `phi`。`FullSem` 是被否定的加强，`phi` 不满足它 (编译)；经典逻辑下可满足 (判)。
- `wdec`、`wdecα`、`wlpo`：
  - I 取 `phi`；`Ωb-off` 取 `off-phi`。
  - `J2-Ωb` 的式子由常值折叠满足 (`j2b-const`)，但它不是接口实例。接口内没有给出实例；判断是一个经典地判定 c ≡ c′ 的折叠同时满足接口、`J2-Ωb`、`Ωb-off`，所以前提不矛盾。这一点未编译。
  - Funext 在 `--without-K` 下不可证，与理论相容；结论标 "条件"。
- `viaE→dec`：`ViaE` 取 `viaE-phi`，`J2-Ωb` 同上。
- `kall-phi`：定理自带的前提 `prE … ≡ inj₂ p` 由 `refl` 实现 (`t-top-thm`, `t-lim-thm`)。

#### 5. 与已知否定的关系 (逐条核机制)

- **`fullSem→lpo` 与 `YiUniNegStep.step-full→lpo`。**
  - 失败的字段相同：都是 "能保留处都保留"，且能否保留是层号上的存在命题；目标层是由 α 定的 ℕ 极限层。
  - 不同处：旧的对象是派发族 `Ext` (keep/fold)，新的是 `Iface.ψs` 的输出树，按头构造子与槽位层号观察。新块要证据 `Ev`，探针把 Kα α 放在孩子层的第 0 项来提供。本块的 `Pos (lim g)` 含 g n 自身，所以探针层号用 2 而不用 1。两边都不涉及值。
- **`viaE→dec` 与 `R13Diag.diag→dec`、`YiCtxNeg.diag1→dec`。**
  - 同一机制。E c₀ c₀ 必须是 just，由 `J2-Ωb` + `J2-limu` + `kstep` + `pres⊥` 逼出。
  - `wdec` 不用证据函数，所以结论较弱 (¬ ⊎ ¬¬)。
  - R13Diag 的 c₀ 是常值极限 (不合法)；这里的 c₀、cα 合法且在规范域内。
- **不是** `cmp-full→lpo` (这里没有层号比较)，**不是** 壁垒 (没有 `Ordᴰ` 初始段，没有三歧)。
- **`kall-phi` 与 RR13 §4 主审意见。** 那条意见说 φ 在 b ≠ 0 时一律折叠、只在 c = 0 保留，说的是 `R13Base` 的 φ。并进折叠后的 `phi` 对一切 c 都保留 (编译)。

#### 6. 偏离与事故

- **内存口径。** `/usr/bin/time -l` 被沙盒拦下 (sysctl)，第一次编译 KSem 的退出码 1 来自 time，agda 本身跑完了。此后每次都在 `+RTS -M6G` 之外加了 `-s<文件>`，表中是 GHC 的最大驻留与总内存，不是常驻内存峰值。
- **附件内容的重写。** `R13Top` 的 `Top` 与 `R13Diag` 的 `diag→dec` 是附件，不能导入，所以在我的文件里逐字重写了。
- **对 YiPhi 版本的依赖。** 结果针对编译时的 YiPhi 文件 (sha256 前 12 位)：Iface ae534ac4ef1e，Block baee14a21312，Fold 0708fac440d5，Legal 766ef8b8c4f1，Check 4ae4ccbabcf6。YiPhi 若改实现，需重编。
- **规则遵守。** 没有改已有文件，没有删别人的 `.agdai`，没有在临时目录外写文件。日志在 `<实验目录>/agents/phineg/`。
