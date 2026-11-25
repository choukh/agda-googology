# 第 1 层的 BTBO 下界 (YiL1)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 04:18 至 05:29 |
| 工具调用 / agda 编译 (粗数) | 90 / 20 |
| token (usage 字段，按消息去重) | 输出 403819；新写入缓存的输入 1257575；读缓存的输入 28993640；其余输入 162 |
| 写过的仓库文件 | `YiL1Base.lagda.md`, `YiL1Emb.lagda.md`, `YiL1Nrm.lagda.md`, `YiL1NrmEmb.lagda.md`, `YiL1Read.lagda.md`, `YiL1Stmt.lagda.md` |
| 文件前缀 | `YiL1` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: 第 1 层的 BTBO 下界一路返回并复核; 主审补一行推论 (主审)” 一节 |
| 主审复核后的一句结论 | base₁ 无前提；T⁺ʷ 与 TΛ 到 ψ₀(Ω_Ω+ψ₁(Ω_Ω))（读法判断）；ψ₀(Ω_Ω+Ω₂) 未走通；六件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的指示是 "朝着最终目标的关键路径走"; 作者这一批选了 **"第 1 层的 BTBO 下界"**: 树的第 1 层折叠值对 BTBO 对角线上一切可数层号 L 的 ψ₁(Ω_L) 的下界, 照第 0 层那条 (`YiBtboLower`) 的办法做成可复用的引理; 做成后试 ψ₀(Ω_Ω+Ω₂). 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇 (特别是 Agda 一节, "用记号验收强度", "中间站给界", "结论的写法"); `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 与 §5.4.
2. **第 0 层的样板**: `probes/OCF/Lean/YiBtboLower.lagda.md` 全读 (链上只带值序, 每步经累加规范化层号 `V2′` (在 `YiBtboV2`) 与主线一侧的 `V3m` 造前驱嵌入, 再 `Ψ-emb`); 说明 `probes/Survey/RR7-BtboLower.md`. 搬到一致折叠上的办法: `YiDlVBtbo.lagda.md`, `YiDlVRel.lagda.md` (读回互模拟 `obs≅`).
3. **要用它的地方**: `YiShpTwo.lagda.md` (条件定理 `X₂′≼ᶜ : Sync₂ → X₂′ ≼ NA.read W.T⁺ʷ`, `Sync₂-0` 已证; `ψ₁ᴸ-lim`: 参照的 ψ₁(Ω_{ℓ₀}) 字面是 ℕ 极限; `γ₂`, `e₂`), `YiShpEps.lagda.md` (第 1 层的读回关系 `Lv1.Ψ₁⊴Φ`, `fold1`, `Tψ`), `YiShpSq.lagda.md` (`ctxY`, `Bq`). 回报 `probes/Survey/Reports-2026-11-12/YiShp.md` §5 写了缺的那条引理 (按它的证法, 判断): 底情形是 `∀ n ζ → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (proj₁ ψ₁ᴸ-lim n)) ≼ NA.read (Ψ₀ (Bq ζ))`, 即树的第 1 层的值 `Tψ η` 对 BTBO 对角线上可数层号的 ψ₁(Ω_L) 的下界; 并说用现成的 `⊴` 直接做走不通 (结点规则只在同一下标的分支之间比较, 前几支太小).
4. 第九次审查: `probes/Survey/RR9-OmegaOmega2.md` (它判断要一条参照框架的树与 `Raw (tw 2)` 的树之间的跨层值关系, 台账 U25).
5. 折叠: `YiDlFold.lagda.md` (对派发参数化, 实例 `dl`); 读回 `YiNextAcc.lagda.md`. 参照框架 `probes/OCF/Align/Level.lagda.md` (`ψ`, `ψ⁰`, `Ω`, `add`, `toLevel`), `Diagonal.lagda.md` (`D.γ`, `D.L`).
查签名用检索, 大文件不要整篇读.

#### 1 要交的, 分步; 每做成一步先交

1. **陈述**: 写出 "第 1 层的 BTBO 下界" 的确切 Agda 类型 (在第 1 层上, 参照的 ψ₁(Ω_{D.L n}) 一类不高于树第 1 层的某个规范折叠值的读回; 或你认为合适的、能被 `Sync₂` 用到的形式), 说明它是第 0 层 `btbo` 的哪一种推广.
2. **证明**, 先最小的情形 (例如 n = 0, 1), 再一般的 n. 办法自选 (照 `YiBtboLower` 经规范化层号造嵌入; 或对第 1 层建一条错位的读回关系; 或别的).
3. **接上**: 用它证 `Sync₂` (或它的足够的部分), 得到 ψ₀(Ω_Ω+Ω₂) 的参照 (`S2.X₂` 经 `X₂≅`) 不高于 `NA.read W.T⁺ʷ`.
4. 做不过去时: 给出确切的缺口 (缺的引理的 Agda 类型), 并说清它与派发 (保留还是折叠) 有没有关系.

只要下界 (作者 2026-11-11 的原则): 不引入上界, 同值, 逐项精确. 下界从已闭合的最高锚点往上做.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K; 堆到 6G 仍耗尽 (先按手册 §4.2). 做不成的部分写成带确切类型的前提. 没有编译的否定时只写 "未走通".

#### 2 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiL1` (模块名 `OCF.Lean.YiL1…`). 都是验收文件, 文首标 "验收文件". 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提.
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 堆墙多出在比较具体闭项的地方: 陈述逐字写, 不用别名; 大参照树放 `opaque`; 经非单射的头求解的隐式参数显式写出 (手册第 4 节).
- 仓库文件里不写本机路径. 不要把仓库整个拷到临时目录.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽. 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块; 另有两路也在编译.
- 你的临时目录: `<实验目录>/agents/l1`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 过程要求: 读完上面的文件后尽快动手, 第一个文件在 20 分钟内写出并编译; 每次回复都要有工具调用, 不要在一次回复里只思考.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 3 回报格式 (只在回报里交一次)

1. 判决: 做到第几步; 一段话说对目标意味着什么 (第 1 层的下界是否成立; ψ₀(Ω_Ω+Ω₂) 是否证出).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 用到的参照与它的读法是否有逐项一致证明.
4. 办法: 与 `YiBtboLower` 相比新用到了什么.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### 1 判决

**做到第 2 步，第 3 步没有走通。**

- 第 1 层的 BTBO 下界已成立，是无前提的编译定理。`base₁ : Base₁` 说的是：对一切 n 与 ζ，参照 ψ⁰(Ω_{ℓ₀} ⊕ ψ₁(Ω_{L_n})) 不高于读回的 `Ψ₀ (Bq ζ)`。这正是 YiShp 回报 §5 说缺的那条底情形。逐项的形式是 `chain₁ : ∀ n → F₁ (suc n) ⊴ K₁ (δq 1)`：每个参照项都落在 Ω₁ 结点 `ψ₁ top` 的链的第 1 点的分支之下。
- 推论 `Xψ₁≼ʷ`：参照 ψ⁰(Ω_{ℓ₀} ⊕ ψ₁ᴸ(Ω_{ℓ₀})) 不高于 `NA.read W.T⁺ʷ`。读作 ψ₀(Ω_Ω+ψ₁(Ω_Ω))，这个读法是判断。`T⁺ʷ` 已证的最高下界因此从 ψ₀(Ω_Ω+ε_{Ω₁+1}) 升到 ψ₀(Ω_Ω+ψ₁(Ω_Ω))，仍低于 ψ₀(Ω_Ω+Ω₂)。
- **ψ₀(Ω_Ω+Ω₂) 没有证出。** `Sync₂` 的第 1 项起未走通，没有编译的否定。缺的是一条能在加法上下文里携带"静态对角线"的第 1 层关系，见 §5。
- 这个缺口与派发无关（判断，依据见 §5）。

#### 2 文件表

六个文件都在 `probes/OCF/Lean/`。删掉全部自己的接口后，按依赖次序逐个冷编译：退出码都是 0，每个日志只有自己模块的 `Checking` 行。内存峰值是 `/usr/bin/time -l` 量的常驻内存峰值。

| 文件 | 总行 / 代码行 | 冷编退出码 | 内存峰值 |
|---|---|---|---|
| `YiL1Stmt.lagda.md` | 67 / 42 | 0 | 1.71 GB |
| `YiL1Read.lagda.md` | 169 / 124 | 0 | 1.71 GB |
| `YiL1Emb.lagda.md` | 318 / 259 | 0 | 3.09 GB |
| `YiL1NrmEmb.lagda.md` | 250 / 192 | 0 | 1.68 GB |
| `YiL1Chain.lagda.md` | 86 / 60 | 0 | 1.70 GB |
| `YiL1Base.lagda.md` | 137 / 99 | 0 | 1.72 GB |

- 检索 `postulate`、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`--irrelevant-projections`、`--cubical`、`{!`、`Funext`，结果为 0。
- 每个文件只有规定的选项行，没有本机路径，模块不带参数，没有用函数外延。

#### 3 定理表

记号：
- `F₁ n = proj₁ ψ₁ᴸ-lim n`，满足 `F₁-form : F₁ n ≡ L.ψ (σB L.zero) (λ q → L.lim n q) (L.Ω (S2.ℓ₀ L.[ n ]ᴵ))`（refl），即 ψ₁(Ω_{L_n})。
- `δq = chain zero (λ ζ → Ψ₀ (G₂ (plus (suc zero) G.top (K₁ ζ))))`。
- `T₁ a l = W.Ψ (suc zero) (Vw a l) (λ r → W.cmpw V2 s₂ (a , l , r)) G.top`。`Tψ η` 定义性地是 `T₁ (nrmk zero η) _`。
- `κ₁ a l = L.toLevel (MA.read (toM a)) (MV.HS-read (toM a) (toM-lgl a l))`。

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `point→base` | `∀ n → Σ ℕ (λ m → F₁ n ⊴ K₁ (δq m)) → ∀ ζ → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (F₁ n)) ≼ NA.read (Ψ₀ (Bq ζ))` | 第 n 项落到某个链点的分支下，就推出 `Base₁` 的第 n 项 | Stmt | 编译定理 |
| `chain→base` | `Chain₁ → Base₁` | 同上，对一切 n | Stmt | 条件定理 |
| `lower₁` | `∀ a (l : Lgl zero a) {κ} → Corr κ MT.⌜ toM a ⌝ → ∀ {ℓ} (p : L.suc L.zero L.<ᴵ ℓ) (σ : L.Simᴵ κ ℓ) θ → L.ψ p σ (L.Ω κ) ⊴ plus (suc zero) θ (T₁ a l)` | 第 1 层的 `lower-read`：对一切合法的第 0 层树 a，ψ₁(Ω_κ) 不高于目标层 1 的折叠 | Read | 编译定理 |
| `lower₁ᴱ` | `∀ a (l : Lgl zero a) {L₀} (P : PEmb L₀ (κ₁ a l)) (r₁ : L.suc L.zero L.≺ᴵ L₀) → PEmb.map P r₁ L.≅ᴵ L.suc L.zero → ∀ {a₀ ℓ} → a₀ L.≅ᴵ L₀ → ∀ (p : L.suc L.zero L.<ᴵ ℓ) (σ : L.Simᴵ a₀ ℓ) θ → L.ψ p σ (L.Ω a₀) ⊴ plus (suc zero) θ (T₁ a l)` | 参照层号经一个把 1 映到 1 的前驱嵌入落进树的层号，ψ₁ 的值就过去 | Emb | 编译定理 |
| `base₁-0` | `∀ ζ → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (F₁ 0)) ≼ NA.read (Ψ₀ (Bq ζ))` | 第 0 项，经 F₁ 0 ≅ γ 1 1 与 `Xε≼Bq` | Emb | 编译定理 |
| `nrmkE` | `∀ ξ (l : Lgl zero ξ) → PEmb (ℓv ξ l) (ℓv (WL.nrmk zero ξ) (WL.nrmk-lgl zero ξ))` | 规范化 `nrmk` 不降层号（前驱的保序嵌入） | NrmEmb | 编译定理 |
| `fix1` | `∀ W (l : Lgl zero (plus zero G.top W)) → ZF W → ∀ (r : L.suc L.zero L.≺ᴵ ℓv (plus zero G.top W) l) → PEmb.map (nrmkE (plus zero G.top W) l) r L.≅ᴵ L.suc L.zero` | 树形如 top + Z 且 Z 不含零时，嵌入把 1 映到 1 | NrmEmb | 编译定理 |
| `ZF-fold` | `∀ {k} (V : WL.Lw k) (x : Ext zero k) ξ → ZF (W.Ψ zero V x ξ)` | 第 0 层的折叠值不含零 | NrmEmb | 编译定理 |
| `one≺κ` | `∀ m → L.suc L.zero L.≺ᴵ κ (suc m)` | 主线链点的层号在 1 之上 | Chain | 编译定理 |
| `cpδ` | `∀ k → Cp zero (G.suc (plus zero G.top (psum zero DB.obs k))) (δq 1)` | 一致折叠的链点（的后继）在 δq 的第 1 点之下 | Chain | 编译定理 |
| `chain₁` | `∀ n → F₁ (suc n) ⊴ K₁ (δq 1)` | 第 1 层的链上 BTBO 下界 | Base | 编译定理 |
| `base₁` | `Base₁`，即 `∀ n ζ → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (F₁ n)) ≼ NA.read (Ψ₀ (Bq ζ))` | 第 1 层的 BTBO 下界 | Base | 编译定理 |
| `Xψ₁≼ʷ` | `Xψ₁ ≼ NA.read W.T⁺ʷ`，其中 `Xψ₁ = L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (L.ψ (σB L.zero) (λ r → r) (L.Ω S2.ℓ₀)))` | ψ₀(Ω_Ω+ψ₁(Ω_Ω)) ≤ T⁺ʷ | Base | 编译定理；读法是判断 |

- 参照 `F₁ n` 与 `Xψ₁` 都没有逐项一致证明（`Lab`），ψ₁ / ψ₀ 的读法是判断。
- `Chain₁` 对 n = 0 没有证。`Base₁` 的第 0 项另走 `Xε` 的路。

#### 4 办法（与 `YiBtboLower` 相比新用到的）

**第 0 层的嵌入原样复用。** 用的是 `YB.emb (suc n) m w : PEmb (D.L (suc n)) (κ (suc m))`。它的像是 κ_m ⊕ c，都在 1 之上（`one≺κ`）。

**固定 0 与 1（`Fix01`）。** 第 1 层的 `Le-ψ`（BTBOFullLe）要求目标层号满足 E 1 1，所以先把嵌入改成在 0、1 上取自身，由此得到 `PE.sub r₁ refl`。

**参照一侧比较，再一次换成第 1 层的关系。**
- 参照一侧用 `Le-ψ`（目标层 1），代替第 0 层的 `Ψ-emb`。
- 树一侧用主线 `YiLeanValFold.FOLD`，目标层取 1，派发取 `x₁`（层号字面为 0 才保留）。
- `wr₁` 证明它与一致折叠里的 `cmpw V2 s₂ = dlev 1` 对齐。再经互模拟 `ΨRʷ`（目标层 1）。
- `TB₁` 把三样东西一次换成 `NA._⊴_`：`Le`、`RelF 1`、`RR`。结论加在任一 θ 之上，因为主线的 `tnr` 落到 `topS`，一致折叠一侧没有对应的结点，`plus 1 θ top` 正好是那个结点。

**`nrmk` 规范化（新的）。** 树在 Ω₁ 结点上的分支族 `Kfk` 取 `nrmk` 规范化的层号，所以目标层号是 `nrmk (top + obs 0 + … + obs m)` 的层号。
- `nrmkE` 在极限处按块构造：先用 `dec` 判定前驱是否已在上一块出现，`dec` 沿第一位置对树做结构递归，用到 `<ᴵ-dec` 与 `sim`；未出现的平移到部分和之上。
- 一致性由 `cohJ` 给出，接 `PEmb-limˡ`。
- `fix1` 与 `ZF-fold` 保证 1 不动。
- 主线链点到一致折叠链点：经 `ptRʷ` 的读回互模拟，以及加法结合律（`assoc-read`）。

**落点。** 用 `cpδ` 经 `W.Tw 2` 落到 δq 的第 1 点。

**没有用的东西。** 没有用值单调、上界、同值、`FUNC`、`KEYsuc`。

#### 5 第一个障碍（ψ₀(Ω_Ω+Ω₂)）

**在哪里断。** 没有写过过不了检查器的证明，所以没有报错原文。`Sync₂ (suc n)` 按 fold1 的形状需要 e₂ (n+1) = ψ₁(Ω_{ℓ₀} + e₂ n) 不高于 ψ₁(G₂ (γ₂ n))。以 `Sync₂ 1` 为例，按 YiShp 的分支引理证法：
- 底情形 y = 0 就是 `base₁`，已证。
- 后继情形要 ψ⁰(Ω_{ℓ₀} ⊕ (A·k + F₁ n))，其中 A = ψ₁(Ω_{ℓ₀}+y)。前缀 A·k 含静态对角线 ψ₁ᴸ(Ω_{ℓ₀}) = lim F₁。
- `NA._⊴_` 不能把 lim F₁ 放到保留的结点 `G.lc (inj₁ tt) K₁` 之下：`⊴b` 只到 `K₁ top`，`nd` 只认 limᵢ 形的参照。
- 所以 `⊴-add₁` 一类的加法上下文用不上。

**缺的部件（判断，未编译）。** 是 `NA._⊴_` 加一条规则：
```agda
dg : ∀ {F : ℕ → T₁} {h : R → R₁} →
  (∀ n → Σ ℕ λ m → ∀ a → Cp zero (G.suc (plus zero G.top (psum zero DB.obs m))) a → F n ⊴⁺ h a) →
  L.lim F ⊴⁺ G.lc (inj₁ tt) h
```
以及两条引理：
```agda
fold1⁺ : ∀ {X : T₁} {η} → X ⊴⁺ η → X L.≅ X → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA X) ≼ NA.read (Ψ₀ (G₂ η))
Fold₁ᴾ : ∀ {X : T₁} {η} → X ⊴⁺ η → X L.≅ X → L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σA X) ⊴⁺ ψ₁ (G₂ η)
```
然后对 n 归纳证 `e₂ n ⊴⁺ γ₂ n`，即得 `Sync₂`。

理由（判断）：
- `fold1⁺` 的 `dg` 情形可以照 `chain₁` 做。`cpδ` 的论证对任意形如 `chain zero (λ ζ → Ψ₀ (G₂ (h ζ)))` 的链都成立，因为对一切 x 都有 `Cp top (G₂ x)`。`dg` 对 `plus θ` 也封闭。
- F₁ 0 那一项还要直接证 `F₁ 0 ⊴ Tψ top`，估计 20 行左右。
- 我对整个关系 ⊴⁺ 的规模估计是 300 到 400 行，这只是估计。它就是 RR9 / 台账 U25 说的跨层值关系。

**与派发的关系（判断，依据编译事实）。** 要用到的位置上，派发在目标层有槽位时保留（`dl-p₀`、`dl-keep`），在 `s₂` 处没有槽位时折叠，都是对的。分支里的 `nrmk` 来自保留结点的分支族 `Kfk`，不来自派发，已由 `nrmkE` 处理。缺口在关系一侧：参照的静态对角线对树的保留结点。

#### 6 偏离与事故

**改过、删过、写错过的东西。**
- 多次修改自己的新文件。`YiL1Stmt` 拆出 `point→base`。`YiL1Emb` 去掉了中途的条件版本：`lower₁ᴾ`、`Emb₁`、`emb→base`。
- 中途有一个文件 `YiL1Nrm`（条件定理 `nrm→base`），在 `Nrm` 被证出以后改名为 `YiL1Chain`，只留部件。原文件和它的接口 `probes/_build/2.8.0.2/agda/OCF/Lean/YiL1Nrm.agdai` 用字面路径删掉了。
- `YiL1Emb` 第一次写出时含一个洞 `{!!}`，在编译前就替换掉了，没有带洞编译过。最终检索为 0。

**过程中的编译错误，都已修好。**
- `NoParseForLHS`：缺 `just` 的导入。
- `ParseError`：类型里的绑定写法。
- `AmbiguousName Le`：与 `YiNextCore.Le` 撞名，改用 `hiding`。
- `UnequalTerms`：Dn 与 Cp 混用。
- `UnsolvedConstraints` 三次：`σB` 写成字面时极限证据成了 meta；`plus-weak` 的参数；`ZF-fold` 的派发参数没有显式写出。
- `WrongHidingInLHS`：`≤′-step` 的隐式参数。
- `ImpossibleConstructor`：`fix1` 的 top 情形。

**其他。**
- 编译命令外面加了 `/usr/bin/time -l` 来量内存。退出码不经管道，直接取自 agda。
- 没有用 `--ignore-interfaces`，没有把仓库拷到临时目录，没有碰已有文件、`src/`、`archive/`。
- tracked 文件的 M 状态在开工时就已存在。
- 日志在 `<实验目录>/agents/l1/`。
