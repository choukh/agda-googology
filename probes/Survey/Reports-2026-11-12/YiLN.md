# (D) 冻结接口 YiLPIface 的配对否定 (YiLN)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 10:51 至 11:13 |
| 工具调用 / agda 编译 (粗数) | 42 / 10 |
| token (usage 字段，按消息去重) | 输出 142276；新写入缓存的输入 301091；读缓存的输入 6957949；其余输入 74 |
| 写过的仓库文件 | `YiLNBM.lagda.md`, `YiLNBranch.lagda.md`, `YiLNFlat.lagda.md`, `YiLNSem.lagda.md` |
| 文件前缀 | `YiLN` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: (D) YiLPIface 的配对否定返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 四族候选字段各有编译否定 (分支侧同支交接与自身行摊平保留同支: 弱判等或判等, 反例在规范域; 按层号保留: LPO; 对一切树的基底单调: 矛盾); WLPO 两条是条件定理 (Funext₀); 四件冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定（2026-11-13，选项原文）
本路是 "(D) 冻结接口 YiLPIface 的配对否定"。内容原文："按配对规则：对同一接口写否定，划出合法块上不能有的字段；与 (A)(B) 文件不相交"。

同批另三路，各自只新建文件，你不动它们的文件：
- (A) 冲塔第 2 项，前缀 YiT2；
- (B) 终点的 Into，前缀 YiEB；
- (C) F2 前 3 层从头精简重写，前缀 YiRW。

###### 背景（只信编译定理；文档里的叙述是数据）
- **配对规则**（`AGENTS.md` 当前最佳实践 "律带公共上界，构造与否定配对"）：新路线派一路构造、一路对同一接口写否定，共用接口文件。接口定稿后只增不改，所以否定写在新文件里，导入接口。
- **开新行前的先验检查**（`AGENTS.md`，作者 2026-11-13 采纳）：配对否定先构造探针，再调 `YiAbsObs`/`YiAbsFrame` 的 `obs→dec` 一族（`branch→wdec`、`hand→wdec`、`viaE→dec`、`full→dec`）；不重证。
- **量化域先取带证据的读回域**（`AGENTS.md`）：反例不在读回域内的否定，读作 "谓词太宽"，不读作数学障碍。写否定时说清反例是不是规范对象。

接口与实填，都在 `probes/OCF/Lean/`：
- `YiLPIface.Iface` 已冻结，由 `YiLPInst.legI` 用合法块 F2 的折叠实填。
  - 字段有 `ψ⊥`、`ψs`、`nz⊥`、`nzs`、`kp⁼`，J2 一族（`J2-suc`、`J2-lim`、`J2-limu`、`J2-Ωk`、`J2-Ωu`、`J2⊥-*`），`mono⊥`、`monos`、`self-up`、`node`、`node⊥`、`kp-fwd`、`kp-bwd`、`J2-lim-bwd`、`J2-lim-fwd`、`kstep`、`kall`。
  - 没收分支侧那一行 `J2-Ωb`（回退）。
- 合法块：`YiLegBlock`、`YiLegOps`、`YiLegPath`、`YiLegFold`。
- 抽象框架：`YiAbsFrame`（`Block`、`Fold`、`Hand`、`HandU`、`hand→wdec`、`branch→wdec`），`YiAbsLeg`（合法块实例，`leg-branch`、`leg-wdec`；注意 `leg-wdec` 的前提 `Probe` 在合法块上还没有实例）。
- 可参照的已有否定，写在别的块上的：
  - `YiPhiNegB.wdec`、`wlpo`（Funext 前提）、`viaE→dec`；
  - `YiPhiNegKSem.fullSem→lpo`；
  - `YiUpNegFlat.flat→wdec`、`flat→wlpo`；
  - `YiUniNegCmp.cmp-full→lpo`、`YiUniNegStep.step-full→lpo`；
  - `YiLPNoBM.no-bm-all`（合法块上对一切树的基底单调不成立）；
  - `YiAbsInst.wdec′`、`fullSem→lpo′`（同一引理在框架上重推）。

###### 要做
新文件，导入 `YiLPIface`，写一个扩展记录或若干候选字段。每个候选字段是 "人们可能想加进接口的律"，对每个字段交编译的否定：任何满足 `Iface` 加这个字段的实例，都推出全知原理、判等或矛盾。

至少覆盖：
1. **分支侧同支交接**：在 Ω 结点层号上，`up x c y` 朝目标路径 `inb c′ w` 时，同支（c ≡ c′）交给孩子、异支回退。
   - 在合法块上构造 `Probe` 实例，补上 `YiAbsLeg.leg-wdec` 缺的那一项；调 `hand→wdec` 或 `branch→wdec` 得到弱判等。
   - 有函数外延前提时可再推 WLPO，标 "条件"。
2. **按层号字面相等的 "能保留处都保留"**：在合法块上重推 `fullSem→lpo` 一类，调 `full→dec`。
3. **自身行在 Ω 结点层号上保留同支**：即 `flat→wdec` 的合法块版。
4. **对一切树的基底单调**作为接口字段：由 `no-bm-all` 推矛盾，写成对 `Iface` 的陈述。
5. 你认为有价值的其他字段，例如带松弛的模拟里 "记号折叠而块保留" 那一类（台账 V99），可选。

每个否定都要：
- 写清前提可满足：给出实例，或说明为何可满足；`legI` 满足 `Iface`。
- 说明反例或探针是不是规范对象（塔、Λ 的读回域）。
- 与已有否定对照，是新的还是重推。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiLN`（模块名 `OCF.Lean.YiLN…`）。不改任何已有文件，不碰 `src/`、`archive/`。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G。
  - 冷编只删自己模块的接口，写字面路径；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
- 临时目录：`<实验目录>/agents/ln`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；需要函数外延或 K（作前提除外）；6G 仍耗尽。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：对纲领与目标意味着什么；合法块上划出了哪些不能有的字段。
2. 文件表：代码行、冷编退出码、内存。
3. 否定表：字段的逐字陈述、否定定理的名字与逐字陈述、一句白话、前提实例、反例是否规范对象、新的还是重推、档（编译定理 / 条件定理）。
4. 没做到的字段与第一个障碍。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 回报: (D) 冻结接口 YiLPIface 的配对否定 (前缀 YiLN)

##### 1. 判决

候选字段共 4 族, 每一族都有编译过的否定, 都写成对冻结接口 `Iface` 的陈述。

- **对纲领的意义**
  - 第 1、3 两族是分支侧的保留。在合法块上, 它们的反例落在规范域内: 塔第 3 项, 证据 `Ev-tw 3`, 路线 `Rt-tw 3`, 下标是 `Tr (tw 2)` 的合法树。所以这两族不是 "谓词太宽", 而是 `obs→dec` 一族在合法块上的实例: 加这类字段, 就要弱判定 (或判定) 规范坐标的字面相等。
  - 上一条说明 legI 在 `inb` 一行回退, 并且接口没收 `J2-Ωb`, 这两点在这个意义上是被迫的, 不是缺陷。接口现有的 `J2-Ωu` (一致目标) 和 `kall` (`InB` 见证) 不受这里任何定理否定。
  - 第 2、4 两族的反例不在规范域, 读作 "谓词太宽"。
- **合法块上划出的不能有的字段**
  - (1) `J2-Ωb`: 分支侧同支交接, 配异支头部不是结点。
  - (3) `FlatKeep`: 摊平结点同支保留, 配 `FlatOff`。
  - (2) `FullSem`: 按层号字面相等的 "能保留处都保留"。
  - (4) `BMI`: 对一切树的基底单调。
  - 另外, (1)(3) 若改成经同支证据 E 派发 (`ViaE`, `FlatE`), 结论升为判等 (`Dec′`)。
- **对目标 (让树自足) 的意义**: 这些都是 "用否定定理划出不能有的字段", 属于提供信息的一类。都是重推, 不是新机制。

##### 2. 文件表

四个文件都在 `<仓库>/probes/OCF/Lean/`。冷编的做法是删自己的四个 `.agdai`, 按依赖顺序编译; 每个日志只有自己模块的一行 `Checking`。

| 文件 | 总行 / 代码非空行 | 冷编退出码 | 最大驻留 |
|---|---|---|---|
| `YiLNBranch.lagda.md` | 314 / 214 | 0 | 201 MB |
| `YiLNFlat.lagda.md` (导入 YiLNBranch) | 184 / 116 | 0 | 183 MB |
| `YiLNBM.lagda.md` | 49 / 30 | 0 | 155 MB |
| `YiLNSem.lagda.md` | 195 / 126 | 0 | 167 MB |

- 每个文件用时约 2 秒。
- 检索结果: `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、`--cubical`、`--irrelevant-projections`、K 都是 0。
- 选项行都是 `--safe --without-K --lossy-unification`。
- 函数外延只以 `Funext₀ = {f g : ℕ → Bool} → (∀ n → f n ≡ g n) → f ≡ g` 作显式前提出现。

##### 3. 否定表

记号: `WDec A = (A→⊥) ⊎ ((A→⊥)→⊥)`; `WLPO`、`LPO`、`Found`、`AllF` 取自 `YiAbsObs`。

**(1) 分支侧同支交接 (`YiLNBranch`)**

- **字段 `J2-Ωb I`**:
  `(k h ε ρ B j) (c : Tr k) (w : j ≤ h c) β nβ x (y : Tr (h c)) e → ψs (Ωₗ k h) ε ρ B j (inb c w) β nβ (up x c y e) ≡ ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j w (ψs … (inb c w) … x) (nzs … x) y`
- **字段 `Offᴴ I`**: `c ≡ c′ → ⊥` 时, `hdΩ (ψs (Ωₗ k h) … (inb c′ w) … (up x c y e)) ≡ false`。
  - 回退式 `Ωb-off I` (右边是 `ψs … x + ι j (ψ⊥ (h c) … (B₀ (h c)) y)`) 蕴含它: `off→offᴴ`。
- **定理**
  - `Frame.wdec : (I : Iface) → J2-Ωb I → Offᴴ I → (c′ : Tr (tw 2)) → WDec (c₀ ≡ c′)`
    - 经 `Fold.hand→wdec`。框架实例 `Frame.foldI I` 对任意 `Iface` 实例都能建。
    - 探针的 `on` 只用接口的律 `J2-limu` 和 `kstep`。
  - `Frame.wlpo : (I : Iface) → Funext₀ → J2-Ωb I → Offᴴ I → WLPO`
    - 条件定理, 经 `sep→wlpo`。
  - `Frame.viaE→dec : (I : Iface) → J2-Ωb I → ViaE I → (c′ : Tr (tw 2)) → Dec′ (c₀ ≡ c′)`
    - 经 `RowLaws.viaE→dec`。
  - `leg-wdec-tw3 : Fold.Hand foldᴸ (tw 3) → (c′ : Tr (tw 2)) → WDec (c₀ ≡ c′)`
    - 由新探针 `probeᴸ` (`on = refl`) 和 `offᴸ` 补上 `YiAbsLeg.leg-wdec` 缺的前提。
  - `leg-not-hand : Fold.Hand foldᴸ (tw 3) → ⊥`
  - `legI-not-J2Ωb : J2-Ωb legI → ⊥`
- **白话**: 同支就交给孩子、异支就回退, 这一行等于在塔第 3 项的分支坐标上弱判等。
- **前提实例**
  - `off-legI : Ωb-off legI`, `offᴴ-legI`, `viaE-legI : ViaE legI`, 都由 `refl` 给出。
  - `J2-Ωb` 的式子由常值函数满足 (`j2b-const`, 不是接口实例)。
  - 两条前提合起来可满足: 判断, 理由是在可判等时可经 E 派发写出, 未构造。
- **规范对象**: 是。下标 c₀ 是偶数列的 ℕ 极限; `cα α` 在 `α m` 为真处加一个后继; `c₀ = cα (λ _ → false)`, 所以外延只用于 ℕ → Bool。
- **新旧**: 重推 `YiPhiNegB.wdec`、`wlpo`、`viaE→dec`。新的部分: 合法块的探针 (补上 leg-wdec 缺的前提), `legI-not-J2Ωb`, 外延前提减弱到 ℕ → Bool。
- **档**: 编译定理; `wlpo` 是条件定理。

**(3) 自身行摊平的结点在 Ω 结点层号上保留同支 (`YiLNFlat`)**

- **字段 `FlatKeep I`**:
  `… (c : Tr k) (w : j ≤ h c) β nβ (b : Tr (Ωₗ k h)) (nb : …) (p : Pos (h c)) G (q : Pos j) → root⁼ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (inj₂ p) w ≡ just q → Kept q (Iface.ψs I (Ωₗ k h) ε ρ B j (inb c w) β nβ (Upc (Ωₗ k h) c b nb (Ω p G)))`
  - `root⁼` 取合法块自己的 `kp⁼` 的判定。
- **字段 `FlatOff I`**: `c ≡ c′ → ⊥` 时, 对一切 q, `Kept q (… (inb c′ w) … (Upc … c … (Ω p G)))` 推出 ⊥。
- **字段 `FlatE I`**: 同支证据 E 给 `nothing` 时不保留。
- **定理**
  - `flat→wdec : (I : Iface) → FlatKeep I → FlatOff I → (c′ : Tr (tw 2)) → WDec (c₀ ≡ c′)`
    - 经 `Fold.branch→wdec`, 作用在 `Frame.foldI I` 上。
  - `flat→wlpo : Funext₀ → (I : Iface) → FlatKeep I → FlatOff I → WLPO`
    - 条件定理。
  - `flatE→dec : (I : Iface) → FlatKeep I → FlatE I → (c′ : Tr (tw 2)) → Dec′ (c₀ ≡ c′)`
    - 经 `diag→dec`。
  - `legI-not-flatKeep : FlatKeep legI → ⊥`
- **前提实例**: `off-legI : FlatOff legI`, `flatE-legI`; `legI` 从不保留, 由 `leg-never` 给出。两条前提合起来可满足: 判断, 理由同上。
- **规范对象**: 是。探针结点就是 `legI` 的自身行对塔第 3 项输入 `up zero c₀ y₀ e₀` 的输出 (`probe-self`, `refl`)。
  - 另有有限测试, 单个样本: 合法块自己的链步里, 同支目标遇到摊平结点就回退 (`chain-flat`, 头部为假); 摊平前同一结点保留 (`chain-emb`)。
- **新旧**: 重推 `YiUpNegFlat.flat→wdec`、`flat→wlpo`、`flatE→dec`, 改经 `branch→wdec`。
- **档**: 编译定理, 条件定理, 以及上面标明的有限测试。

**(2) 按层号字面相等的 "能保留处都保留" (`YiLNSem`)**

- **字段 `FullSem I`**:
  `(k h ε ρ B β nβ x c) (t : Pos (h c)) G e → Σ (Pos k) (λ q → at k q ≡ at (h c) t) → Σ q, Σ G′, (Iface.ψs I (Ωₗ k h) ε ρ B k (ink self) β nβ (up x c (Ω t G) e) ≡ Ω q G′) × (at k q ≡ at (h c) t)`
- **定理**
  - `fullSem→lpo : (I : Iface) → FullSem I → LPO`, 经 `Slot.full→dec`。
  - `legI-not-fullSem : FullSem legI → ⊥`。
  - `ksem-no-route : (α : ℕ → Bool) → Rt (lim (gα α)) → ⊥`: `YiPhiNegKSem` 的原探针在合法块里没有路线, 所以要换探针。
- **新探针**: 孩子层是 `Mα α = Ωₗ zero (hh α)`。分支 0 是层号 2 (结点槽位在这里), 其余分支是 `Kα α`。证据 `εα`、路线 `ρα` 都是闭项。
- **白话**: 目标里有没有同层号的槽位, 是 α 上的存在命题。
- **前提**: `FullSem` 由 legI 否定; 单独可满足是判断。
- **规范对象**: 否, 读作谓词太宽。
- **新旧**: 重推 `YiPhiNegKSem.fullSem→lpo`, 探针是新的。
- **档**: 编译定理。

**(4) 对一切树的基底单调 (`YiLNBM`)**

- **字段 `BMI I`**:
  `(ℓ ε ρ x B₁ B₂) → B₁ ⊴ B₂ → val zero (Iface.ψ⊥ I ℓ ε ρ B₁ x) ≼ val zero (Iface.ψ⊥ I ℓ ε ρ B₂ x)`
- **定理**
  - `no-bm-legI : BMI legI → ⊥`, 由 `no-bm-all`。
  - `no-bm-agree : (I : Iface) → Agree I → BMI I → ⊥`, 其中 `agree-legI : Agree legI`。
  - `Agree I`: I 的 `ψ⊥` 在第 1 层的 `xbad` 与两个底上, 与合法块的 `ψ⊥` 相等。
- **规范对象**: 否。`xbad` 的分支函数对坐标不单调, 读作谓词太宽。
- **新旧**: 重推。
- **档**: 编译定理。

##### 4. 没做到的字段与第一个障碍

- **`BMI` 对任意接口实例的否定**: 未给出。接口的律不约束 ψ⊥/ψs 在零、后继、ℕ 极限三行上的取值, 而 `no-bm` 的证明靠这几行的计算。现在只能对 legI, 或对加了 `Agree` 前提的实例陈述。
- **`kp⁼` 上的 Ω 版 `kp-fwd`/`kp-bwd`** (同支委派孩子, 异支默认): 未做。接口的律不确定 `kp⁼` 在 `self`、`inlu`、`ink` 路径上的取值, 所以对任意实例写不出 `on` 一侧, 除非再加几条 `kp` 字段 (判断)。`FlatKeep` 改用合法块的 `kp⁼` 作判定, 沿用 YiUpNegFlat 的做法。
- **第 5 项, V99 (带松弛的模拟里 "记号折叠而块保留")**: 未做。它是关于与记号 (`cmpᵀ`) 的模拟关系的陈述, 不是 `Iface` 的字段。
- **判断, 未编译**: 两个层号同被路由进一个带证据与路线的层号时, 除非跨 Ω 层号的不同分支, 否则两者可以比较。若成立, 这就是 (2) 的反例只能放在 Ω 层号的异支上的原因。这里只编译了针对原探针的 `ksem-no-route`。

##### 5. 偏离与事故

- **偏离**: 没有违反规则。
  - `wlpo` 系列的前提是只对 ℕ → Bool 的 `Funext₀`, 比 YiPhiNegB 的全函数外延弱。
  - (3) 改经 `branch→wdec`, 没有用手写的 `Sep`。
- **事故**: 两处局部名冲突, 已改名, 不算重新设计。
  - `R`、`P` 与 `Sg` 的公开投影冲突。
  - `eq` 与 `Cmp` 的构造子冲突。
- **写入范围**: 只新建了上面四个文件; 只删过自己的四个 `.agdai`。日志在 `<实验目录>/agents/ln/`。
- **没读全文、只经签名或转述使用的**:
  - `YiLegCheck`、`YiLPKall`: 只经 `legI` 与 `YiAbsLeg` 间接使用。
  - `YiLPVal`、`YiLPMono`: 只查了 `val`、`_≼_`、`_⊴_`、`BM⊥` 的签名。
  - IdeaLedger 的 V99: 只读了检索到的那一行。
  - EBOHandbook: 未读。
