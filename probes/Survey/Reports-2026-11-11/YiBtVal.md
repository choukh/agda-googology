# 把值做到与 BTBO 持平 (YiBtVal)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-11 06:43 至 07:40 |
| 工具调用 / agda 编译 (粗数) | 85 / 24 |
| token (usage 字段，按消息去重) | 输出 347321；新写入缓存的输入 1097181；读缓存的输入 24228472；其余输入 142 |
| 写过的仓库文件 | `YiBtValAdd.lagda.md`, `YiBtValAdm.lagda.md`, `YiBtValBT.lagda.md`, `YiBtValFin.lagda.md`, `YiBtValFold.lagda.md`, `YiBtValRel.lagda.md`, `YiBtValTw3.lagda.md` |
| 文件前缀 | `YiBtVal` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 值到 BTBO 的一路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 新折叠的值下界到一切有限 n、ω、ω+n；塔的第 3 项的闭项不低于参照的 ψ₀(Ω_ω)；与 BTBO 持平归约到一条未证的单调性；七件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库> = <仓库>) 的一路执行方, 任务是 "把乙线的值下界做到与 BTBO 持平": 目标是塔的第 3 项的闭项 `T₃ᵐ` 不低于 BTBO 的参照 (读法 ψ₀(Ω_Ω)). 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

### 0 先读什么

1. `AGENTS.md` 全篇. 特别是: "用记号验收强度" 与 "中间站给界, 终点对 EBO 验收" (序数值验收; 中间站给下界即可); Agda 一节 (选项, 文字预算, 退出码, 堆; Funext 只准作前提); "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 (编译与内存, 堆墙的对策) 与 §5.4.
3. **两份回报原文, 全读**: `probes/Survey/Reports-2026-11-11/YiLvAll.md` (旧折叠上对层号一致的值证明是怎么做成的) 与 `YiRawVal.md` (新折叠上 n ≤ 3 与 `T₃ᵐ` 的下界, §5 列了往上缺什么). 同目录 `README.md` 的 §2.
4. 代码 (都在 `probes/OCF/Align/`, 模块名 `OCF.Align.<名>`; 都已定稿, 可以导入, 不许编辑):
   - **范例一 (对层号一致, 旧折叠)**: `YiLvAllRel` (`Rel : (M : ℕ) → ∀ {k} → L.Ordᶜ k → Raw (fin M) → Set`, `START`, `TRC-all`, `below-nat`, `nat-inj`), `YiLvAllTree` (`TREE-KEEP`, `TREE-FOLD`), `YiLvAllAdd` (`ADDg`, `SUCC`, `ABSORB`), `YiLvAllFold` (`FOLD`), `YiLvAll` (`interfaceᴬ`, `lower-all`, `lower-Ωω`).
   - **范例二 (新折叠, 逐层)**: `YiRawValBase` (`Interface`, `FromInterface.theorem`, `theoremᵐ`, `one≼`, `lower₁ᵐ`), `YiRawVal2`, `YiRawVal3Base`, `YiRawVal3` (`lower₃ᵐ`), `YiRawValTw3` (`T₃ᵐ-Ω₁`, `T₃ᵐ-Ω₂`, `T₃ᵐ-Ω₃`).
   - **被验收的对象**: 写在 `Raw K` 上的新折叠. `YiRawFoldBase` (`Ext`, `psum`, `CohP`), `YiRawFold` (`Ψ`, `Φᵐ`, `Φ`, `own`, `ownT`, 各行), `YiRawFoldInst` (`closed`, `closedᵐ`, `closedᵐ-legal`), `YiRawFoldUp` (`Φᵐ-lim-row`: 极限层号上 `closedᵐ` 是各支的部分和), `YiRawFoldTw3` (`T₃ᵐ`, `T₃ᵐ-term`, `T₃ᵐ-feedback`).
   - 参照一侧: `OCF.Align.Level` (`Ordᶜ`, `ψ`, `ψ⁰`, `Ω`, `natᴵ`, `ωᴵ`, 层号类型 `Ordᴵ` 与它的极限), `OCF.Align.Value` (`≼`); `src/OCF/BTBO.lagda.md` 第 1040 到 1108 行 (`ordᴰ`, `ψⁿ`, `BTBO` 的定义; 它在 `OCF.BTBO` 模块里, 用自己的族). 仓库里与 BTBO 的参照有关的已有验收: 用检索找 `BTBO` 在 `probes/OCF/Align/` 里的出现 (例如 `Level` 族上 ψ⁰ (Ω ℓ) 对一般 ℓ 的定义, 以及上一条主线里 "BTBO 的参照树" 的写法), 先弄清参照取哪一个再动手, 并在回报里写明.
   - 值的序与部分和: `YiPsumVal` (`lim≼psumᵖ`: 部分和不降值; `absorb-suc`).
   查签名用检索, 大文件不要整篇读.

### 1 这一步是什么, 为什么要做

乙线塔的第 3 项的闭项 `T₃ᵐ` 合法, 折叠问到的派发处处完全, 读法是 ψ₀(Ω_Ω) (与已封存的 BTBO 持平). 但值定理只到: `T₃ᵐ` 不低于参照的 ψ₀(Ω₃). 闭项合法不携带强度信息, 所以读法要靠值定理落实. 本任务把下界往上推, 最终目标是 "BTBO 的参照 ≼ 读回的 `T₃ᵐ`". 做成就是乙线第一个与 BTBO 持平的值定理. 只要下界, 不要上界, 不要同值.

### 2 目标, 分步; 每步先交再往下

1. **新折叠上对层号一致的版本.** 把 `YiLvAll*` 的办法搬到新折叠: `∀ M → YiRawValBase.Interface M`, 从而对一切 n, 参照的 ψ₀(Ω_n) ≼ 读回的 `closedᵐ (fin n)` (与 `closed (fin n)`). `YiRawVal` 的回报 §5 指出新派发是对位置的规范比较, 变量层号上要另写化简引理. 这一步有两个范例可照, 最便宜, 先做.
2. **`T₃ᵐ` 到 ψ₀(Ω_ω).** 由第 1 步加上 "`T₃ᵐ` 的第 1 项的第 0 支的第 n 支是 `closedᵐ (fin (n+2))`" (命题等式, 对变量 n 要处理层号; `YiRawValTw3` 对 n = 0, 1 是定义性的) 得: 参照的 ψ₀(Ω_ω) ≼ 读回的 `T₃ᵐ`. 极限层号处经过部分和一行; 部分和不降值 (`lim≼psumᵖ` 一类) 可用.
3. **含极限的层号.** `closedᵐ K` 对含 ℕ 极限的 `Plain` 层号 K 的下界: 先 K = ω+1 (读法 ψ₀(Ω_{ω+1})), 再一般的合法 `Plain` K. 这里参照一侧的层号不再是 `natᴵ`; 被验收一侧的派发是规范比较 `ccompare`, 极限层号上 `top` 取部分和. 关系族要从 "按 ℕ 的层" 推广到 "按 `Plain` 层号的位置". 这是本任务的主体, 没有范例.
4. **根上的链.** `T₃ᵐ` 是 `lim (λ n → closedᵐ (read0 ηₙ))`, 链点 `ηₙ₊₁ = ηₙ + closedᵐ (read0 ηₙ)`. BTBO 的参照是 `lim ψⁿ`, `ψⁿ⁺¹ = ψ₀ (Ω (ordᴰ ψⁿ))` (或 `Level` 族上的对应物). 证参照的第 n 项 ≼ 读回的 `T₃ᵐ` 的某一项, 对 n 归纳: 归纳步要第 3 步的下界, 并且要它对层号单调 (参照一侧层号小的, 被验收一侧层号是它的读回或更大的). 参照一侧 `ordᴰ` 用了累加; 两边层号的对应关系怎么陈述, 是这一步要先想清楚的, 写进回报.

部分进展也算: 做到第 2 步 (ψ₀(Ω_ω)) 已经超过现有的 ψ₀(Ω₃); 做到第 3 步的 ω+1 是第一次越过 ω.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要 Funext 或 K 才能证 (可交显式前提的条件定理, 另给不带它的最强结果); 堆到 6G 仍耗尽 (先按手册 §4.2 的对策; 文件拆小). 约化: 把缺的引理写成带确切类型的模块参数, 其余条件地证出来并编译; 说明前提在已有的实例上是定理.

不要为了让值定理好证而改折叠: 被验收的对象就是 `YiRawFoldInst.closedᵐ` (与 `closed`) 和 `YiRawFoldTw3.T₃ᵐ`. 发现它的值低于读法 (例如部分和或某一步其实掉值), 那是重要结果: 写成编译过的定理交回, 不要自己修.

### 3 规则

- **只新建文件**, 前缀 `YiBtVal`, 放 `probes/OCF/Align/`, 中文 literate Agda (`.lagda.md`). 都是验收文件, 文首标 "验收文件"; 允许导入带记号闭包的 `Value` 与旧验收文件. 不改任何已有文件 (含 README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 同时在跑的另几路用前缀 `YiGenFold`, `YiGenNeg`, 不要动它们的文件, 也不要依赖它们.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. Funext 只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算** (AGENTS Agda 一节): 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda`.
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Align/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/btval`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步, 一段话说对纲领与目标意味着什么 (`T₃ᵐ` 的下界到了哪里; 哪些读法变成了定理, 哪些仍是读法).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型.
4. 办法: 参照取的是哪一个 (写明模块与定义); 关系族怎么推广的; 哪些引理从范例原样导入, 哪些是新的; 哪些定理经过部分和一行.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
强度写 ψ₀(Ω_x), 标明是定理还是读法; 下界不写成同值; 不用 "只差", "自然" 一类形容.

## 回报原文

### YiBtVal 一路回报 (把乙线的值下界往 BTBO 推)

#### 1 判决

第 1、2、3 步做完了。第 4 步归约到一条带确切类型的单调性引理 `MonoT`，交了条件定理，`MonoT` 本身没有证。

**变成定理的读法 (都只是下界，不是同值)：**
- **一切有限 n**：`closedᵐ (fin n)` 与 `closed (fin n)` 不低于 ψ₀(Ω_n)。同时交了 `∀ M → YiRawValBase.Interface M`。
- **一切 Plain 且 Legal 的层号 K**：`closedᵐ K` 与 `closed K` 不低于 ψ₀(Ω_κ)，只要参照层号 κ 与 K 结构对应 (`Corr κ K`)，并且满足 `Zs κ`。
  - κ 可以取 `toIL K`，它由 Legal 里的步进造出来。
  - 实例：ψ₀(Ω_ω)；ψ₀(Ω_{ω+n})，其中 ω+1 是第一次越过 ω；`YiRawFoldInst` 的具名闭项 `Ωω+1`, `Ωω+2`。
- **`T₃ᵐ`**：
  - 不低于 ψ₀(Ω_ω)。这是定理，比原来的 ψ₀(Ω₃) 高。
  - `T₃ᵐ` 的第 n 项不低于 ψ₀(Ω_{κₙ})，κₙ 是第 n 个链点读成层号后的参照层号。这一条无前提。

**仍是读法：**
- `T₃ᵐ` 的 ψ₀(Ω_Ω)，也就是与 BTBO 持平。现在只有条件定理："若 `MonoT`，则 Level 族的 BTBO 参照 ≼ 读回的 `T₃ᵐ`"。
- 上界、同值、FGH。

**其他：**
- 没有发现掉值。没有改折叠或任何已有文件。没有用 Funext 或 K。
- 翻译账：关系族 `RelF` 是验收工具，按参照一侧 `<ᴵ-dec` 的派发组织，这一点受记号启发；它不进成品。

#### 2 文件表

都在 `probes/OCF/Align/`，都是验收文件。只删自己模块的 `.agdai`，按依赖序冷编译。每份日志只有本模块一行 `Checking`，堆上限 6G。

| 文件 | 代码行 / 总行 | 退出码 | 常驻峰值，用时 |
|---|---|---|---|
| `YiBtValRel.lagda.md` | 255 / 316 | 0 | 1.23G，8s |
| `YiBtValAdd.lagda.md` | 243 / 288 | 0 | 1.56G，9s |
| `YiBtValFold.lagda.md` | 270 / 319 | 0 | 1.35G，8s |
| `YiBtValAdm.lagda.md` | 144 / 205 | 0 | 1.33G，7s |
| `YiBtValFin.lagda.md` | 135 / 197 | 0 | 1.34G，7s |
| `YiBtValTw3.lagda.md` | 46 / 72 | 0 | 1.30G，7s |
| `YiBtValBT.lagda.md` | 111 / 158 | 0 | 1.34G，7s |

- 检索 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`--irrelevant-projections`、`--cubical`、本机路径：0 处。
- Funext 只在 Fin 文首 "没有 Funext" 一句里出现。
- 选项行全是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。

#### 3 定理表

`⟨ n ⟩ = L.natᴵ n`。`ωp 0 = L.ωᴵ`，`ωp (suc n) = L.suc (ωp n)`。

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `interfaceᴮ` | `∀ M → Interface M` (即 `YiRawValBase.Interface`) | 上一轮条件定理的前提对一切 M 成立 | Fin | 编译定理 |
| `lower-allᵐ` / `lower-all` | `∀ n → L.ψ⁰ (L.Ω ⟨ n ⟩) ≼ read (closedᵐ (fin n) (fin-plain n) (fin-legal n))`；`closed` 版同 | 一切有限 n，不低于 ψ₀(Ω_n) | Fin | 编译定理 |
| `lower-any` / `lower-anyᶜ` | `∀ K (pl : Plain K) (Lg : Legal K) {κ} → Corr κ K → Zs κ → L.ψ⁰ (L.Ω κ) ≼ read (closedᵐ K pl Lg)`；`closed` 版同 | 一切合法层号，不低于 ψ₀(Ω_κ) | Fin | 编译定理，两个前提见下 |
| `lower-toIL` | `∀ K (pl : Plain K) (Lg : Legal K) → Zs (toIL K pl Lg) → L.ψ⁰ (L.Ω (toIL K pl Lg)) ≼ read (closedᵐ K pl Lg)` | 同上，κ 取 `toIL` | Fin | 编译定理 |
| `lower-finᵐ` | `∀ n (pl : Plain (fin n)) (Lg : Legal (fin n)) → L.ψ⁰ (L.Ω ⟨ n ⟩) ≼ read (closedᵐ (fin n) pl Lg)` | 有限层号，Plain/Legal 任意 | Fin | 编译定理 |
| `lower-ωᵐ` / `lower-ω` | `L.ψ⁰ (L.Ω L.ωᴵ) ≼ read (closedᵐ ω ω-plain ω-legal)`；`closed` 版同 | 不低于 ψ₀(Ω_ω) | Fin | 编译定理 |
| `lower-ω+ᵐ` / `lower-ω+` | `∀ n → L.ψ⁰ (L.Ω (ωp n)) ≼ read (closedᵐ (ω+ n) (ω+-plain n) (ω+-legal n))`；`closed` 版同 | 不低于 ψ₀(Ω_{ω+n}) | Fin | 编译定理 |
| `Ωω+1-lower` / `Ωω+2-lower` | `L.ψ⁰ (L.Ω (L.suc L.ωᴵ)) ≼ read Ωω+1`；`L.ψ⁰ (L.Ω (L.suc (L.suc L.ωᴵ))) ≼ read Ωω+2` | 具名闭项的下界 | Fin | 编译定理 |
| `T₃ᵐ-at` | `∀ m → L.ψ⁰ (L.Ω ⟨ suc (suc m) ⟩) ≼ read T₃ᵐ` | 第 1 项第 0 支的第 m 支 | Tw3 | 编译定理 |
| `T₃ᵐ-Ωω` | `L.ψ⁰ (L.Ω L.ωᴵ) ≼ read T₃ᵐ` | `T₃ᵐ` 不低于 ψ₀(Ω_ω) | Tw3 | 编译定理 |
| `H-fin` | `∀ m → read0 (one +ʳ copies B.zero one m) ≡ fin (suc (suc m))` | 那一支的层号命题相等于 fin (m+2) | Tw3 | 编译定理 |
| `T₃ᵐ-own` | `∀ n → L.ψ⁰ (L.Ω (κ n)) ≼ read T₃ᵐ`，`κ n = toIL (read0 (coordᵐ (pointsᵐ n))) …` | 每一项不低于它自己层号上的 ψ₀(Ω_·) | BT | 编译定理 |
| `FromMono.btbo` | `D.BTBOᴵ ≼ read T₃ᵐ`；模块参数 `mono : MonoT` | 若 `MonoT`，则与 BTBO 持平 (下界) | BT | 条件定理 |
| `mono-⊑` | `∀ x h a l → L.toLevel x h L.⊑ᴵ toIL (read0 a) (rplain a) (read0-legal a l) → ZsL (read0 a) → L.ψ⁰ (L.Ω (L.toLevel x h)) ≼ read (foldᵐ₃ a l)` | 层号结构可比时，`MonoT` 的结论成立 | BT | 编译定理 |
| `mono₀` | `L.ψ⁰ (L.Ω (L.toLevel (D.γ 0) (D.cert 0))) ≼ read (obsᵐ (pointsᵐ 0))` | `MonoT` 在第 0 步的实例 | BT | 编译定理 |
| `FOLD` (模块 `FoldA`，参数 `AdmI`) | `∀ K → Adm K → (pl : Plain K) (Lg : Legal K) → ∀ m → Adm m → (x : Ext m K) → N.Complete x → ∀ {j} {y : L.Ordᶜ j} {η} → RelF K y η → ∀ {i ℓ} → Corr i m → (p : i <ᴵ ℓ) (σ : L.Simᴵ j ℓ) → .(l : Lgl K η) .(nb : Nested K η) → RelF m (L.ψ p σ y) (N.Ψ m K pl Lg x η l nb)` | 新折叠在一切输入层、目标层上保持关系 | Fold | 编译定理 (`AdmI` 由 `CPClass` 实例化) |
| `CPClass.admI` | `AdmI` | 层号类 = 一个合法层号的字面子项 | Adm | 编译构造 |
| `chainCP`, `strict`, `noSelf` | `∀ K → Plain K → Legal K → ∀ {x y} → CP x K → CP y K → (x ≡ y) ⊎ (CP⁺ x y ⊎ CP⁺ y x)`；`CP⁺ x y → Corr a x → Corr b y → a ≅ᴵ b → ⊥`；`SubP a b → a ≅ᴵ b → ⊥` | 合法层号的子项两两可比；真子项不与自身结构对应 | Adm | 编译定理 |
| `START`, `POS`, `posCorr`, `TRC-all`, `ABSORB`, `ADDg`, `SUCC`, `PSUM` | 例如 `START : ∀ m {i} → Corr i m → RelF m (L.Ω i) (cO m)` | 一般层号上的起点、位置、搬运、加法、部分和引理 | Rel / Add | 编译定理 |

**条件定理的前提，逐字：**

```
MonoT = ∀ (x : L.Ordᶜ L.zero) (h : L.HS x) (a : R) (l : Lgl B.zero a) → x ≼ read a →
  L.ψ⁰ (L.Ω (L.toLevel x h)) ≼ read (foldᵐ₃ a l)
```

**前提的可满足性：**
- `MonoT` 在第 0 步是定理 (`mono₀`)；在层号结构可比时也是定理 (`mono-⊑`)。一般情形未证，见 §5。
- `lower-any` 的两个前提：`Corr` 由 `natC`、`ωC`、`toIL-c` 给出；`Zs` 由 `ZsN`、`ZsW`、`inv` (T₃ᵐ 的一切链点) 给出。
- `Zs` 在退化层号上不成立，例如 `suc (lim (λ _ → zero))`。

#### 4 办法

##### 参照取哪一个

- **第 1–3 步**：参照是 `OCF.Align.Level` 的 `L.ψ⁰ (L.Ω κ)`。κ 取 `natᴵ n`、`ωᴵ`、`ωp n`，一般情形取 `toIL K`。
- **第 4 步**：参照是 Level 族上无累加的对应物，即 `OCF.Align.Diagonal` 的模块 `Diagonal`，参数取 `OCF.Align.Uniform.Uniform`：
  - `D.γ 0 = Ω zero = 1`，`D.γ (n+1) = ψ⁰ (Ω (toLevel (D.γ n) (D.cert n)))`，`D.BTBOᴵ = lim (D.γ ∘ suc)`。
  - 两个模块的已编译接口原样加载，没有重编。
  - 没有直接用 src 的 `BTBO`。它在别的族里，层号用 `ordᴰ`/`cumsum`，且 Ω₀ = ω。Diagonal §3 的估计是两条对角线的值交错、标签同为 ψ₀(Ω_Ω)；这是估计，不是定理。

##### 关系族怎么推广

`RelF K` 对 `K : LF` 递归 (`YiBtValRel`)：
- 第 0 层是原样导入的 `R0`。
- 后继层用模块 `LvS`，它就是 `YiLvAllRel.Lv`，只把 `fin N` 换成 `k`。
- 极限层用新模块 `LvL`。它多两条构造子：`emrˡ`，对 `em n a`；`tlrˡ n`，表示 `top` 来自第 n 支的 `top`。两种层都多了 `up (self n)` 的情况。

参照层号不取函数值，只要求结构对应：`data Corr`，与 `≅ᴵ` 相容。结点的起点对一切对应的层号陈述：`∀ {j′} → Corr j′ (lev K s) → SL s (Ω j′) c`。

变量层号上的派发靠下面几点解决：
- 主引理以外部派发的**完全性** (`YiRawFold.Complete`) 为前提。
- 对位置的走法 (`NODEW`, `FIRSTN`) 与对槽位的走法 (`ndAt`, `bAt`) 都对 (层号, 位置) 递归。
- 到根位置时，派发结果 `keep s refl` 直接把层号统一成 `lev m s`。这里不需要 `wayOf` 化简，也不需要 J 或 UIP。

两侧派发的一致需要三条：
1. 参照说 "在下"：由 `adm-sep` 推出树一侧的位置；`adm-sep` 来自 `chainCP` 加 `strict`。
2. 参照说 "在上" 或 "相同"：由 `POS` 加 `clash₁`/`clash₂` 排除树一侧的保留。
3. 折叠：两条链同步 (`Chainᴿ`)。

##### 中途的一次重写

起初 `toI (lim f) = ωᴵ`，只覆盖 fin 与 ω+n；后来改为 `Corr` 加 `CPClass`。最终文件里没有那个写法。

##### 原样导入与新写的

**原样导入：**
- `YiLvAllRel` 的 `R0`、`r0`、`un0`、`TRC`、`Back`、`TR0`。
- `YiLvValBase` 的 `plus≽`、`read-copies`、`suc-lower`、`⟨_⟩`。
- `YiLvAll` 的 `z<M`。
- `YiRawValBase` 的 `Interface`、`FromInterface`。
- `YiRawFold` 的 `complete-*`、`own`、`ownT`、`ndL`、`ndT`。
- `RR4MonoFragment.≼-+ˡ`，`YiIrrFoldValue.read-add`。
- `Level` 的 `Ψ⁰-mono`、`ψ⁰≅ψ`、`clash₁`/`clash₂`。

**新写的：**
- `RelF`、`RelL`、`Corr`。
- TRC 的极限层版本。
- 极限层上的 `EMSHIFT`、`ADDg`、`ABSORB`、`cumρ`、`PSUM`。
- 新折叠上的 `FIRSTn/N`、`NODEn/W`、`KEEPc`、`FOLDc`、`OMEGA`、`FOLD0`、`FOLD`。
- `START`、`POS`、`posCorr`。
- 层号类 (`chainCP`、`strict`、`noSelf`、`toIL`)。
- `Run` (一般层号的 `FromInterface`)。
- `H-fin`；`T₃ᵐ` 链点的 `inv`。

##### 经过部分和一行的定理

部分和一行指极限层号上 `top` 在 `mix` 之下取部分和，即 `Φᵐ-lim-row`；在 FOLD 里是 `tlrˡ` 的 `mix` 子句。

- **经过它的：**
  - `lower-any` 与 `lower-toIL`：层号含极限时，在顶层与链内都经过。
  - `lower-ωᵐ`：只在顶层。
  - `lower-ω+ᵐ` 与 `lower-ω+` (n ≥ 1)：在链内，因为 `ownT` 是 `mix`。
  - `T₃ᵐ-at`、`T₃ᵐ-Ωω`：两次 `psum≽`。
  - `T₃ᵐ-own`、`FromMono.btbo`。
- **不经过它的**：一切有限层号的定理，以及 `closed ω` 的顶层。
- **另一处累加**：加法在 `x + top` 极限层号处的 `cum`，在 `EMSHIFT`、`ADDg`、`ABSORB` 的极限子句里用到。

#### 5 第一个障碍

障碍在第 4 步的 `MonoT`。没有检查器报错，缺的就是这条引理本身，类型见 §3。

**现成工具只到结构可比。** 现成的单调性只有 `Ψ⁰-mono : a ⊑ᴵ b → ψ⁰ (Ω a) ⊑ ψ⁰ (Ω b)`，它要求参照层号 `toLevel (D.γ n)` 与树一侧层号 κₙ 之间有结构上的 `⊑ᴵ`。
- n = 0 时成立 (`mono₀`)。
- n ≥ 1 时我判断它不成立 (判断，未编译)。理由：树的链是累加的，ηₙ₊₁ = ηₙ + 闭项，前面还加了 1；`successor y = lim (y, y+y, …)` 的基本列与参照的 `lim (0, A, A+A, …)` 错位。所以树的层号里出现 `lim (natᴵ (k+2))`，而参照一侧是 `ωᴵ`。两者值相同，但对这样的一对 `⊑ᴵ` 不能经 `suc` 保持 (与 `Value.⊑-not-suc` 是同一现象)。
- 结果：结构的路线在第 1 步之后断开。

**值层面的单调性未知。** 改用值的 ≼ 时，链的归纳本身是现成的 (`FromMono.chain`)，缺的正是 "ψ⁰∘Ω 对层号的值单调"。
- 已知的相关否定：`RR4MonoFragment.mono-fragment-not-cong` 说明 ψ⁰ 对一般的第 1 层树不是值单调的。
- 但 `MonoT` 只涉及层号的 Ω (规范树)。它成立与否没有定理，也没有反例。

**同一个障碍挡住 `T₃ᵐ` 从 ψ₀(Ω_ω) 再往上：** `T₃ᵐ-own` 的层号 κ₁ 里有 `suc ω″`，ω″ 是错位的 ω；要从它得到 ψ₀(Ω_{ω+1}) 也需要同类的值单调性。

**关系族本身的界限：** ndr、ntr 要求参照结点层号与树结点层号结构对应。若把它放宽到 "值不高于"，两侧派发会不一致 (参照折叠而树保留)，需要新的 "链进结点" 构造子；这是判断，未试。

#### 6 偏离与事故

- 中途重写了 Rel、Fold、Adm 三个文件 (§4)。最终交的是重写后的版本，每个都冷编译过。
- 编译中途的错误都是自己的，每处改一次就过了：
  - telescope 的语法：`∀` 后混写带类型和不带类型的绑定。
  - `levC` 对记录模式的停机，拆成 `levF`/`levW` 解决。
  - `out-at` 的隐式参数 x 推断成 `up zero …`，标上类型解决。
  - 没有导出的 `coordᵐ`，改为 `open Ptᵐ`。
- 没有写临时 `.agda` 探针。只删过自己 7 个模块的 `.agdai`，写的是字面路径。
- 没改任何已有文件，没碰 `src/`、`archive/`，不依赖 `YiGenFold`、`YiGenNeg`，没有提交。
- 加载了 `Diagonal`、`Uniform`、`RR4MonoFragment` 的已有接口，没有重编它们。
- 编译日志在 `<实验目录>/agents/btval/cold-*.log`。
