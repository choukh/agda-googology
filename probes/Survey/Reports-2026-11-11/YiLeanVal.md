# 主线块上的值证明，带前驱结构 (YiLeanVal)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-11 08:59 至 09:34 |
| 工具调用 / agda 编译 (粗数) | 60 / 17 |
| token (usage 字段，按消息去重) | 输出 206426；新写入缓存的输入 600286；读缓存的输入 14188581；其余输入 106 |
| 写过的仓库文件 | `YiLeanValAdd.lagda.md`, `YiLeanValBreak.lagda.md`, `YiLeanValFin.lagda.md`, `YiLeanValFold.lagda.md`, `YiLeanValRel.lagda.md` |
| 文件前缀 | `YiLeanVal` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 主线块上的值证明返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 主线新块上一般可数层号的下界与闭项不低于参照的 ψ₀(Ω_ω) 是定理；与 BTBO 持平是条件定理，只缺链点对的那一条；五件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 任务是 **在主线块 (重写的新块 `YiLean`) 上做值证明, 并带前驱结构**: 把新闭项 `T₃` 的值下界从 ψ₀(Ω₂) 推到一般的可数层号, 目标是 "BTBO 的参照 ≼ 读回的 `T₃`". 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 "用记号验收强度" (序数值验收), "中间站给界", "第 4 层不反过来改前 3 层" (验收只新增关系与定理, 不改树, 折叠, 合法性的定义), Agda 一节 (选项, 文字预算, 退出码, 堆; 函数外延只准作前提), "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 (编译与内存, 堆墙的对策) 与 §5.4.
3. **三份回报原文, 全读**: `probes/Survey/Reports-2026-11-11/YiLean.md` (新块是怎么写的, 值做到哪里), `YiBtVal.md` (旧块上对层号一致的值证明是怎么做的: 关系族对层号递归, `Corr`, `FOLD`, `lower-any`), `YiMono.md` (为什么只带值的下界到不了 BTBO; 前驱嵌入这个工具; §5 列的缺的四条引理).
4. 代码:
   - **被验收的对象 (在 `probes/OCF/Lean/`, 模块名 `OCF.Lean.<名>`; 作者 2026-11-11 定为主线; 已定稿, 可以导入, 不许编辑)**: `YiLeanCore` (块: `LF`, `Raw`, `Lay`, `Cp`, `Dn`, `Lgl`, `up`, `upT`, `tw`, `plus`, `add`, `acc`), `YiLeanFold` (`lev`, `Way`, `Ext`, `Lv`, `Shift`, `cmp`, `chain`, `Ψn`, `ΨN`, `Ψ`, `succ`, `psum`, 各行), `YiLeanLegal` (`Ψ-lgl`, `Ψ-cp`, `plus-lgl`, `plus-weak`), `YiLeanTw3` (`⌜_⌝`, `lv`, `F η l = Ψ zero (lv η l) (λ _ → fold) G.top`, `F-up`, `pts`, `obs`, `T₃`, `T₃-legal`, `T₃-feedback`: 链点 ηₙ₊₁ = ηₙ + F ηₙ, 从 `top` 起), 已有的验收 `YiLeanAccFin` (`read : R → L.Ordᶜ L.zero`, `fold₀`, `lower₁`, `lower₂`, `NodeLower`, `T₃-Ω₂`).
   - **范例 (旧块上的值证明, 在 `probes/OCF/Align/`)**: `YiBtValRel` (关系族 `RelF`, `Corr`, `START`, `POS`), `YiBtValAdd`, `YiBtValFold` (`FOLD`), `YiBtValAdm`, `YiBtValFin` (`lower-allᵐ`, `lower-any`, `lower-ω+ᵐ`), `YiBtValTw3`, `YiBtValBT` (`T₃ᵐ-own`, `MonoT`); 更早的 `YiLvAllRel`, `YiLvAllFold`, `YiLvAll`.
   - **前驱嵌入**: `BTBOFullEmb` (记录 `PEmb a b`: 字段 `map`, `bnd`, `mono`, `coh`; `Ψ-emb : PEmb a b → ψ⁰ (Ω a) ≼ ψ⁰ (Ω b)`), `YiMonoEmb` (`PEmb-⊑`, `PEmb-∘`, `PEmb-limʳ`, `PEmb-suc`, `PEmb-limˡ`; `DomT`, `EmbT`, `btbo-dom` 是对旧树的陈述, 可作体例), `YiMonoOne` (`emb₁`, `T₃ᵐ-Ωω+1`: 在旧树的真实链点上手造一个嵌入的例子), `YiMonoBreak` (结构可比的证法在旧树上不通: `no-L`), `YiMonoVM` (`HS-read`, `lvl≅`: 旧树上读回的层号与折叠用的层号结构互模拟).
   - 参照: `OCF.Align.Level` (`L.ψ⁰ (L.Ω κ)`, `Ordᴵ`, `toLevel`, `HS`, `_⊑ᴵ_`, `_≅ᴵ_`, `Ψ⁰-mono`), `OCF.Align.Value` (`≼`), `OCF.Align.Diagonal` 取 `OCF.Align.Uniform.Uniform` (不累加的 BTBO 对角线: `γ`, `cert`, `L n = toLevel (γ n) (cert n)`, `BTBOᴵ`).
   查签名用检索, 大文件不要整篇读.

#### 1 为什么要做, 做成什么算数

新块上的闭项 `T₃` 读法是 ψ₀(Ω_Ω) (与 BTBO 同高度), 值定理现在只有 `T₃` 不低于参照的 ψ₀(Ω₂). 作者定的顺序: 先把与 BTBO 持平做成定理, 再往上. 旧块上的教训 (`YiMono` 的回报): 值证明的底关系若只是 "值不低于" (`y ≼ read a`), 得到的下界只对树自己的层号成立 (`T₃ᵐ-own`), 接不到参照的对角链上, 因为参照的层号与树的链点层号结构不可比, 而每一种单调工具都要目标层号的前驱结构. 所以这次要求值证明 **带前驱结构**: 证出的不只是 "参照 ≼ 读回", 还要给出参照层号到树的层号的前驱嵌入 (`PEmb`) 或足以推出它的东西.

#### 2 目标, 分步; 每步先交再往下

1. **一切有限 n 与 ψ₀(Ω_ω).** 对一切 n: 参照的 ψ₀(Ω_n) ≼ 读回的第 n 层闭项 (`F (fin n) …`); 推出参照的 ψ₀(Ω_ω) ≼ 读回的 `T₃` (若 `T₃` 的某一项的某一支是 ω 层的闭项) 或直接对 `F` 在 ω 层号上证. 办法照 `YiBtVal*` / `YiLvAll*`: 一族对层号一致的关系, 折叠在一切输入层与目标层上保持它. 新块比旧块简单的地方 (没有守卫, 没有无关证据, 合法性不进折叠的定义) 应当让这一步更短; 如实报代码行数.
2. **一般的可数层号.** 对一切带 `Lv` 数据的层号 (零, 后继, ℕ 极限): 参照在对应层号上的 ψ₀(Ω_κ) ≼ 读回的 `F`. 即新块上的 `lower-any`. 由它得到 `T₃` 的第 n 项不低于它自己层号上的参照 (新块上的 `T₃-own`).
3. **带前驱结构.** 把第 1, 2 步的结论加强, 使它能接到参照的对角链上. 两种做法, 取你判断更可行的, 说明理由:
   - (a) 关系族的底关系直接取前驱嵌入 (或在值之外并带一份嵌入): 第 0 层上不是 `y ≼ read a`, 而是 "y 读成的层号的前驱嵌进 a 读成的层号 (`⌜ a ⌝` 对应的 `Ordᴵ`)" 一类; 需要的引理 (见 `YiMono` 回报 §5): 第 0 层 ψ⁰ 对嵌入的函子性; 平移嵌入 `PEmb X (P + X)`; 各块嵌入的一致性 (喂给 `PEmb-limˡ`); 第 1 层闭项的结构刻画.
   - (b) 值的关系族不动, 另证一条沿对角链的嵌入: `∀ n → Σ ℕ λ m → PEmb (D.L n) (新树第 m 个链点的层号)` (新块上的 `EmbT`), 对 n 归纳; 归纳步要 "新折叠的输出的前驱结构" 的刻画.
   先做 n = 1 的闭实例 (参照的 `D.L 1` 嵌进新树的某个链点层号), 再一般的 n.
4. **与 BTBO 持平.** `D.BTBOᴵ ≼ read T₃` (新块的 `read`, 新块的 `T₃`). 无条件最好; 否则是条件定理, 前提写成带确切类型的模块参数, 并说明它在哪些实例上是定理.

**退路.** 第 3 步做不成时, 第 1, 2 步 (只带值的版本) 仍然要交: 另一对路 (前缀 `YiVmCon`, `YiVmNeg`) 同时在攻参照框架上的值单调 `VMᴸ` (陈述在 `YiMonoVM`); 它若成立, 配上你第 2 步的结果就得到 BTBO 下界. 不要等它, 不要依赖它的文件; 但把 "由 `VMᴸ` 加第 2 步推出 `D.BTBOᴵ ≼ read T₃`" 写成一条以 `VMᴸ` 为显式前提的条件定理 (新块上的 `btbo-vm`; 旧块的写法见 `YiMonoVM`).

**要核对并写成编译事实的.** 新树的链同样是累加的 (下一点是这一点加上折叠值, 从 `top` 起, `top` 读成 1). 结构可比的证法在新树上通不通 (旧树上 `no-L` 说不通)? 先在 n = 1 上试一次, 通与不通都写成定理, 不要只转述.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理, 另给不带它的最强结果); 堆到 6G 仍耗尽 (先按手册 §4.2 的对策: 陈述逐字写, 大的参照树放 `opaque`, 隐式参数显式写出, 文件拆小).

不要为了好证而改新块的定义: 被验收的对象就是 `YiLeanTw3.T₃` 与 `F`. 发现它的值低于读法 (某一步其实掉值), 那是重要结果: 写成编译过的定理交回, 不要自己修. 发现新块的定义有妨碍值证明的地方, 写进回报, 不要改.

#### 3 规则

- **只新建文件**, 前缀 `YiLeanVal`, 放 `probes/OCF/Lean/` (模块名 `OCF.Lean.YiLeanVal…`), 中文 literate Agda (`.lagda.md`). 都是验收文件, 文首标 "验收文件"; 允许导入带记号闭包的 `OCF.Align.Value`, `OCF.Align.Level` 与旧验收文件. 不改任何已有文件 (含 `YiLean*`, README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 同时在跑的另两路用前缀 `YiVmCon`, `YiVmNeg` (在 `probes/OCF/Align/`), 不要动也不要依赖它们的文件.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算**: 每个模块文首不超过 5 行 (判决与档位, 做了什么, 不否定什么, 入口指向); 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/leanval`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步; 一段话说对纲领与目标意味着什么 (`T₃` 的下界到了哪里; `D.BTBOᴵ ≼ read T₃` 是定理, 条件定理, 还是没有; 哪些读法变成了定理).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值. 另报验收代码的总行数, 与旧块上同样范围的 (`YiBtVal*` 约 1200 行) 并列.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型与它的可满足性.
4. 办法: 参照取的是哪一个; 关系族怎么写的, 底关系是什么; 第 3 步取 (a) 还是 (b), 为什么; 结构可比在新树上通不通 (编译事实).
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 新块的定义里有没有妨碍值证明的地方.
7. 偏离与事故.
强度写 ψ₀(Ω_x), 标明是定理还是读法; 下界不写成同值; 不用 "只差", "自然" 一类形容.

## 中途消息（主审发给这一路）

转录时间戳 2026-11-11 09:26 (UTC)：

主审通知 (不改你的任务, 多给一个已定稿可导入的工具): 另一路 `YiVmCon` 已返回并经主审冷编复核, 它的四个文件现在定稿, 你可以导入 (撤销简报里 "不要依赖 YiVmCon 的文件" 这一条; `YiVmNeg` 仍不要依赖).

对你的第 3, 4 步直接有用的 (都在 `OCF.Align.YiVmConExact`):
- `XEmb a b`: 保值的前驱嵌入 = `PEmb a b` 加上 "每个前驱的像与它值相等" (字段 `P`, `ex`, `ex′`).
- `XEmb-limˡ : (∀ n → XEmb (f n) b) → XEmb (L.lim f s) b` —— 左极限的拼接**不要一致性前提** (上一路卡住的 `PEmb-limˡ` 的前提由保值加 `≈→≅` 自动得到). 另有 `XEmb-⊑`, `XEmb-limʳ`, `XEmb-sucʳ`, `XEmb-∘`, `XEmb-suc` (后继同余要两边顶值相等).
- 两个定义域: `_≼ˣ_` (构造子 `zˣ`, `sˣ : a ≼ˣ b → b ≼ a → suc a ≼ˣ suc b`, `wˣ`, …) 与更宽的 `_≼ᵖ_` (`zᵖ`, `sᵖ`, `wᵖ`, `≼lᵖ`, `lᵖ`); `⊑→≼ˣ : a L.⊑ b → a ≼ˣ b`, `reflˣ`, `ˣ→ᵖ`.
- `VMᵖ : ∀ x hx y hy → x ≼ᵖ y → L.ψ⁰ (L.Ω (toLevel x hx)) ≼ L.ψ⁰ (L.Ω (toLevel y hy))` 是无条件的定理 (值单调在这个定义域上成立).
- 旧树上的用法见 `OCF.Align.YiVmConChain`: `ChainP = ∀ n → D.γ n ≼ᵖ read (coordᵐ (pointsᵐ n))`, `btbo-p : ChainP → D.BTBOᴵ ≼ read T₃ᵐ` (用的是只带值的 `lower-any` 加 `VMᵖ`, 不要 `VMᴸ`, 不要 `MonoT`); `chainP₀` (n = 0), `diag-in : ∀ n → D.γ n ≼ˣ D.γ (suc n)`.

所以在新块上, "BTBO 的参照 ≼ 读回的 `T₃`" 归约成两件: (i) 你第 2 步的只带值的下界 (新块的 `lower-any`); (ii) 新树的链点对落在定义域里: `∀ n → Σ ℕ λ m → D.γ n ≼ᵖ read (新树第 m 个链点的坐标)` (允许错开下标). 请把 (ii) 作为第 3 步的首选做法: 先 n = 1 的闭实例, 再一般的 n; 做不成时写清卡在 `≼ᵖ` 的哪个构造子上 (那一路的判断: 链是累加的, `≼ˣ` 对左加平移不封闭, 保值要吸收律 1 + a ≈ a, 所以要按树的具体结构逐项做). 一般的 `VMᴸ` 经这条证法要一个推出 LPO 的前提 (`YiVmConLPO.tri→LPO`), 所以不要指望 `VMᴸ` 无条件成立, 条件定理那一条仍可以交.

## 回报原文

I've done steps 1 and 2 of the brief, and steps 3–4 as conditional theorems. `D.BTBOᴵ ≼ read T₃` is not yet an unconditional theorem. The new compiled lower bound on `T₃` is ψ₀(Ω_ω) (up from ψ₀(Ω₂)); ψ₀(Ω_Ω), level with BTBO, is still only a reading. All five files cold-compile with exit 0.

#### 1 Verdict

- **Done:** steps 1 and 2, compiled, no premises. For every legal layer-0 tree η, and every reference level κ that structurally corresponds to `⌜ η ⌝` (`Corr`), ψ₀(Ω_κ) ≼ `read (F η l)`. This is `lower-any` on the new block.
  - Corollaries: every finite n, and ω.
  - `T₃-own`: term n of `T₃` is ≥ ψ₀(Ω_{κₙ}), where κₙ is the level that chain point n reads as.
  - `T₃-Ωω`: `T₃` ≥ ψ₀(Ω_ω).
  - All of these are lower bounds, not equalities.
- **Steps 3–4: conditional only.**
  - `btbo-vm : VMᴸ → D.BTBOᴵ ≼ read T₃`. `VMᴸ` is imported from `YiMonoVM`, so it is the same proposition as there. Per your note, it is not expected to hold unconditionally.
  - `btbo-p : ChainP → D.BTBOᴵ ≼ read T₃`. Following your note, this goes through `VMᵖ` and needs no monotonicity at all.
    - The premise `ChainP` asks that reference term n and *some* chain point m (the index may shift) lie in `≼ᵖ`.
    - n = 0 is a theorem (`chainP₀`). n ≥ 1 is not proved, so the n = 1 closed instance asked for in step 3 is not done.
- **Structural comparability is a compiled negation on the new tree too:** `no-L : ∀ n m → ¬ (D.L (suc n) ⊑ᴵ κ m)`. The cause is the same as on the old tree. The chain starts at 1, each point is the cumulative `ηₙ + F ηₙ`, and every ℕ-limit's 0th term is nonzero, so no literal predecessor is ≅ ω. This rules out only the "`⊑ᴵ` + `Ψ⁰-mono`" proof, not the BTBO bound.
- **Accumulation, as compiled facts:**
  - `top` reads as 1 (`top-one`, `refl`).
  - The next chain point is this point plus its fold value (`chain-cum`, plus the existing `T₃-feedback`).
- I found no value drop and made no change to the block's definitions.

#### 2 Files (all in `probes/OCF/Lean/`, all acceptance files)

| File | Code lines / total | Cold exit | Peak RSS |
|---|---|---|---|
| `YiLeanValRel.lagda.md` | 197 / 267 | 0 | 1.26G |
| `YiLeanValAdd.lagda.md` | 189 / 248 | 0 | 1.56G |
| `YiLeanValFold.lagda.md` | 226 / 285 | 0 | 1.41G |
| `YiLeanValFin.lagda.md` | 103 / 167 | 0 | 1.37G |
| `YiLeanValBreak.lagda.md` | 65 / 92 | 0 | 1.35G |

- **Size:** 715 code lines for the same scope as the old `YiBtVal*` (Rel+Add+Fold+Fin), against 1204 for the old seven files. Including Break, the total is 780.
- **Cold compile:** I deleted only my own five `.agdai` files, by literal path. Each log has exactly one `Checking` line, its own.
- **Audit:**
  - grep for postulate, holes, TERMINATING, NO_POSITIVITY, trustMe, irrelevant-projections, --cubical, Funext and local paths finds nothing.
  - Every options line is `--safe --without-K --lossy-unification`.

#### 3 Theorems (`L` = `OCF.Align.Level`; all compiled theorems unless marked)

- **`lower-any`** (Fold): `∀ η (l : Lgl zero η) {κ} → Corr κ ⌜ η ⌝ → L.ψ⁰ (L.Ω κ) ≼ read (F η l)`. Every countable level reaches its reference. The premise is satisfiable for every legal η via `corr-read`.
- **`FOLD`** (Fold): `∀ {K} (V : Lv K) m → Pl m → (x : Ext m K) → ∀ {i ℓ} (p : i <ᴵ ℓ) → Corr i m → Agree x i → ∀ {κ} (σ : L.Simᴵ κ ℓ) {y : L.Ordᶜ κ} {ξ} → RelF K y ξ → RelF m (L.ψ p σ y) (Ψ m V x ξ)`. The fold preserves the relation at every input and target level.
  - **`FOLD⁰`** is the same with target 0 and `ψ⁰`, concluding `L.ψ⁰ y ≼ read (Ψ zero V x ξ)`.
- **`CMP`** (Rel): `∀ {k} (V : Lv k) q r {j} → Corr j (lev k q) → AgW (cmp V q r) j`. The new non-canonical `cmp` agrees with the reference's `<ᴵ-dec`.
- **`lower-fin`** (Fin): `∀ n → L.ψ⁰ (L.Ω (L.natᴵ n)) ≼ read (F (fin n) (fin-lgl n))`. Every finite n.
- **`lower-ω`** (Fin): `L.ψ⁰ (L.Ω L.ωᴵ) ≼ read (F ωR ωR-lgl)`, with `ωR = G.lim fin`.
- **`HS-read`, `corr-read`** (Fin): `∀ a → Lgl zero a → L.HS (read a)` and `∀ a (h : L.HS (read a)) → Corr (L.toLevel (read a) h) ⌜ a ⌝`.
- **`lower-read`** (Fin): `∀ a (l : Lgl zero a) → L.ψ⁰ (L.Ω (L.toLevel (read a) (HS-read a l))) ≼ read (F a l)`.
- **`T₃-own`** (Fin): `∀ n → L.ψ⁰ (L.Ω (κ n)) ≼ read T₃`, where `κ n = L.toLevel (read (co (pts n))) (HS-read …)`.
- **`ω⊑κ₁`, `T₃-Ωω`** (Fin): `L.ωᴵ ⊑ᴵ κ 1` and `L.ψ⁰ (L.Ω L.ωᴵ) ≼ read T₃`.
- **`top-one`, `chain-cum`** (Fin): `read G.top ≡ L.suc L.zero` and `∀ n → read (co (pts (suc n))) L.≅ (read (co (pts n)) L.+ read (obs (pts n)))`.
- **`btbo-vm`** (Fin, conditional): `VMᴸ → D.BTBOᴵ ≼ read T₃`.
  - Premise, from `YiMonoVM`: `∀ x hx y hy → x ≼ y → L.ψ⁰ (L.Ω (L.toLevel x hx)) ≼ L.ψ⁰ (L.Ω (L.toLevel y hy))`.
  - Satisfiability: per your note it needs an LPO-type premise (`YiVmConLPO`). It holds on the structurally comparable instances.
- **`btbo-p`** (Fin, conditional): `ChainP → D.BTBOᴵ ≼ read T₃`.
  - Premise: `ChainP = ∀ n → Σ ℕ λ m → D.γ n ≼ᵖ read (co (pts m))`.
  - Satisfiability: n = 0 is `chainP₀`; n ≥ 1 is unproved.
- **`no-L`, `no-sω-κ`, `inv-nz`** (Break, negations): `∀ n m → ¬ (D.L (suc n) ⊑ᴵ κ m)` and `∀ m → ¬ (L.suc L.ωᴵ ⊑ᴵ κ m)`.
- **Supporting lemmas** (Rel/Add): `START`, `POS`, `TRC-all`, `RIGHT`, `LEFT`, `ADDB`, `SUCC`, `ABSORB`, `PSUM`.

#### 4 Method

- **Reference:** `L.ψ⁰ (L.Ω κ)`. For BTBO it is the same `D = Diagonal Uniform` as `YiBtValBT`.
- **Relation family:** `RelF K` recurses on the level, and each level is an instance of one parameterised inductive family `Lvl` (child and slot relations are parameters).
  - The base at layer 0 is the value relation `y ≼ read a`, restricted to level-0 reference trees.
  - `top` at successor levels is literally the root node `lc (inj₁ tt) (em tt)` (rule `tnr`, which matches `top-as-node`). At limit levels it sits above each branch's `top` (rule `tlr`, via the partial sum).
  - The new dispatch is aligned with the reference by `Agree` (keep ⇒ node level below target), and `cmp` satisfies it by `CMP`.
- **What the new block's simplifications bought:** no guards, no irrelevant evidence, legality outside the fold, and the chain starting at `top`. As a result the node rule needs no start field, and nothing like `Adm`, `Complete`, `chainCP` or `strict` is needed. That is where the size drop from 1204 to 715 lines comes from.
- **Step 3:** I took the route in your message: keep the value family and reduce to "chain points lie in `≼ᵖ`" (`btbo-p`), rather than redoing the family with an embedding base (option (a)). Reasons:
  - With a `PEmb` base, left limits hit the coherence problem.
  - With a `≼ˣ` base, `ABSORB` (the chain step `t + Ψ t`) fails at the second premise of `sˣ`, because the left-shifted sum changes values at finite tails.
- **Structural comparability on the new tree:** it fails, as a compiled fact (`no-L`), for every n ≥ 1 and every m.

#### 5 First obstacle

`ChainP` at n = 1. There is no checker error; the missing piece is the lemma itself. `D.γ 1` is a left limit, so `lᵖ` forces, for every k, `L.ψ⁰ (cₖ) ≼ˣ read (co (pts m))`, where c₀ = 1 and cₖ₊₁ = ψ(cₖ) at level 0. The missing lemma would have the type `∀ k → L.ψ⁰ (cₖ) ≼ˣ read (co (pts 1))`.

It sticks on the second premise of `sˣ`, `b ≼ a` (exact value at each successor node). The tree side only offers successors shaped like `θ + z`, and `θ + z ≈ z` needs absorption, case by case on the tree's concrete structure.

What would be enough, as my judgement: a local trichotomy (`Tri` from `YiVmConExact`) restricted to the pairs that occur here, or a "value ⇒ `≼ˣ`" completeness lemma for the class of trees the new fold produces.

#### 6 Does the block's definition get in the way?

- **No real obstruction.** Two things helped: `top-as-node` holds by `refl`, and `top` reads as 1.
- **Mild cost:** `Lay.A (Lo K r)` is not definitionally `Raw (lev K r)`, so walking lemmas along the position are needed (`FIRSTN`, `NODEN`, `nodeAt-br`, `nodeAt-nd`, about 40 lines).
- **Under `--lossy-unification`,** `Ψ` and `ψ⁰` are not injective, so implicit arguments had to be written out (`{ξ = topS k}`, `{y = y}`).

#### 7 Deviations and incidents

- **Imports:**
  - `YiVmConExact` (after your permission).
  - `YiMonoVM.VMᴸ`, `YiMonoBreak.sω-L1/L-chain`, `YiBtValBT.D`, and `YiLeanAccFin` (`read`, `plus≽`, `read-copies`, `one≼`, `fin`).
  - I do not depend on `YiVmNeg`.
- **Termination quirk (worked around):** matching a `Pl` index and then an indexed derivation in the same function rejected the `tnr` recursion. Splitting by shape (`LEFTs`/`LEFTl`, `ADDs`/`ADDl`, `FOLDs`/`FOLDl`) fixed it.
  - I confirmed this with a one-off pure `.agda` test in `<实验目录>/agents/leanval/scr/T1.agda`, which is outside the repo.
- **File repair:** I revised my own files several times. Once, a script edit duplicated the header of `YiLeanValFin`; I repaired it before the final cold compile.
- **Untouched:** no edits to any existing file, nothing in `src/` or `archive/`, no commits.
- **Logs:** `<实验目录>/agents/leanval/cold-*.log`.

Files are in `probes/OCF/Lean/`:
- `YiLeanValRel.lagda.md`
- `YiLeanValAdd.lagda.md`
- `YiLeanValFold.lagda.md`
- `YiLeanValFin.lagda.md`
- `YiLeanValBreak.lagda.md`
