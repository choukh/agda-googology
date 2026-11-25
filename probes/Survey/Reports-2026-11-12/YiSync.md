# 第 1 层关系补规则拿 ψ₀(Ω_Ω+Ω₂) (YiSync)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 06:57 至 07:13 |
| 工具调用 / agda 编译 (粗数) | 38 / 6 |
| token (usage 字段，按消息去重) | 输出 97556；新写入缓存的输入 228942；读缓存的输入 4919758；其余输入 66 |
| 写过的仓库文件 | `YiSyncDiag.lagda.md`, `YiSyncFold.lagda.md`, `YiSyncRel.lagda.md`, `YiSyncTwo.lagda.md` |
| 文件前缀 | `YiSync` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: 第 1 层关系补规则一路返回并复核; TΛ 到 ψ₀(Ω_Ω+Ω₂) (主审)” 一节 |
| 主审复核后的一句结论 | X₂≼TΛ 无前提（读法判断）；sync₂；新关系的对角规则；四件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的方针: "边重构边做, 只动值的前沿碰到的那块"; 你这一路是值的那一路: **给第 1 层的读回关系补上能在加法上下文里携带静态对角线的规则, 证 `Sync₂`, 得到 ψ₀(Ω_Ω+Ω₂) 的下界, 并搬到 `TΛ` 上.** 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇 (Agda 一节, "用记号验收强度", "中间站给界", "结论的写法"); `probes/Survey/EBOHandbook.md` §4.1 到 §4.5 与 §5.4.
2. **上一路的回报** `probes/Survey/Reports-2026-11-12/YiL1.md` 全读, 特别是 §5: `Sync₂ (suc n)` 按 `fold1` 的形状要 e₂ (n+1) = ψ₁(Ω_{ℓ₀} + e₂ n) 不高于 ψ₁(G₂ (γ₂ n)); 后继情形里前缀含静态对角线 ψ₁ᴸ(Ω_{ℓ₀}) = lim F₁; `NA._⊴_` 不能把它放到保留结点 `G.lc (inj₁ tt) K₁` 之下 (`⊴b` 只到 `K₁ top`, `nd` 只认 limᵢ 形的参照). 执行方给的草案 (判断, 未编译):
   ```agda
   dg : ∀ {F : ℕ → T₁} {h : R → R₁} →
     (∀ n → Σ ℕ λ m → ∀ a → Cp zero (G.suc (plus zero G.top (psum zero DB.obs m))) a → F n ⊴⁺ h a) →
     L.lim F ⊴⁺ G.lc (inj₁ tt) h
   fold1⁺ : ∀ {X : T₁} {η} → X ⊴⁺ η → X L.≅ X → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA X) ≼ NA.read (Ψ₀ (G₂ η))
   Fold₁ᴾ : ∀ {X : T₁} {η} → X ⊴⁺ η → X L.≅ X → L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σA X) ⊴⁺ ψ₁ (G₂ η)
   ```
   然后对 n 归纳证 `e₂ n ⊴⁺ γ₂ n`, 即得 `Sync₂`.
3. 代码 (都在 `probes/OCF/Lean/`): `YiL1Base.lagda.md` (`base₁`, `chain₁`, `Xψ₁≼ʷ`), `YiL1Stmt`, `YiL1Chain` (`cpδ`), `YiShpTwo.lagda.md` (`Sync₂`, `Sync₂-0`, `X₂′≼ᶜ`, `X₂≅`, `γ₂`, `e₂`, `ψ₁ᴸ-lim`), `YiShpEps.lagda.md` (`Lv1`, `fold1`, `Tψ`), `YiShpSq.lagda.md` (`ctxY`, `Bq`, `node≼T`), 读回关系 `YiNextAcc.lagda.md` 的 `_⊴_` 一节, 搬到 `TΛ` 的办法 `YiIntoTw3.lagda.md` (`T⁺ʷ≼TΛ`) 与 `YiL1Lam.lagda.md`. 折叠 `YiDlFold.lagda.md`. 参照 `probes/OCF/Align/Level.lagda.md`, `Stage2.lagda.md` (`X₂`, `X₂-unlabel`).
查签名用检索, 大文件不要整篇读.

#### 1 要交的, 分步; 每做成一步先交

1. 关系 `⊴⁺` (或你认为合适的扩充), 含携带静态对角线的规则; 证它与 `⊴` 的关系 (例如 `⊴` 推出 `⊴⁺`) 以及要用的传递或加法上下文引理.
2. `fold1⁺`, `Fold₁ᴾ` 一类的引理 (第 1 层的关系经前缀 Ω_{ℓ₀} 送到第 0 层的值, 以及经第 1 层的 ψ 保持).
3. `e₂ n ⊴⁺ γ₂ n` 对一切 n, 从而 `Sync₂`, 从而 `S2.X₂` (经 `X₂≅`) 不高于 `NA.read W.T⁺ʷ`, 再经 `T⁺ʷ≼TΛ` 不高于 `NA.read W.TΛ`.
4. 做不过去时: 给出确切的缺口 (缺的引理的 Agda 类型), 说清它与派发有没有关系.

只要下界 (作者 2026-11-11 的原则): 不引入上界, 同值, 逐项精确. 参照 `X₂` 没有逐项一致证明 (`X₂-unlabel`), 它的读法 ψ₀(Ω_Ω+Ω₂) 是判断, 照实写.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K; 堆到 6G 仍耗尽 (先按手册 §4.2). 没有编译的否定时只写 "未走通".

#### 2 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiSync` (模块名 `OCF.Lean.YiSync…`). 都是验收文件, 文首标 "验收文件". 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞 (写入文件时也不要留洞), `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提.
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 堆墙多出在比较具体闭项的地方: 陈述逐字写, 不用别名; 大参照树放 `opaque`; 经非单射的头求解的隐式参数显式写出 (手册第 4 节).
- 仓库文件里不写本机路径. 不要把仓库整个拷到临时目录.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽. 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块; 另有两路也在编译.
- 你的临时目录: `<实验目录>/agents/sync`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 过程要求: 读完上面的文件后尽快动手, 第一个文件在 20 分钟内写出并编译; 每次回复都要有工具调用, 不要在一次回复里只思考.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 3 回报格式 (只在回报里交一次)

1. 判决: 做到第几步; 一段话说对目标意味着什么 (ψ₀(Ω_Ω+Ω₂) 的下界在 `T⁺ʷ` 与 `TΛ` 上是否成立).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断).
4. 办法: 与 `YiL1` 相比新用到了什么.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### 1 判决

**三步都做到了，没有停在第 4 步。**

ψ₀(Ω_Ω+Ω₂) 的下界在 `T⁺ʷ` 和 `TΛ` 上都已证出，是无前提的编译定理：
- `X₂≼ʷ : S2.X₂ ≼ NA.read W.T⁺ʷ`
- `X₂≼TΛ : S2.X₂ ≼ NA.read W.TΛ`

参照 `S2.X₂ = ψ⁰ (add (Ω ℓ₀) σ₂ (Ω 2))` 读作 ψ₀(Ω_Ω+Ω₂)。这个读法是判断：它没有逐项一致证明（`Stage2` 的 `X₂-unlabel`）。

已证的最高下界因此从 ψ₀(Ω_Ω+ψ₁(Ω_Ω))（YiL1 的 `Xψ₁≼ʷ`）升到 ψ₀(Ω_Ω+Ω₂)。只证了下界，没有引入上界、同值或逐项精确。`YiShpTwo` 的条件定理 `X₂′≼ᶜ` 的前提 `Sync₂` 现在已无条件成立（`sync₂`）。

#### 2 文件表

四个文件都在 `probes/OCF/Lean/`。先删掉这四个接口，再按依赖次序逐个冷编译。每个日志只有自己模块的 1 行 `Checking`。内存峰值是 `/usr/bin/time -l` 量的常驻内存峰值。

| 文件 | 总行 / 代码行 | 冷编退出码 | 内存峰值 |
|---|---|---|---|
| `YiSyncRel.lagda.md` | 155 / 123 | 0 | 1.78 GB |
| `YiSyncDiag.lagda.md` | 85 / 63 | 0 | 1.74 GB |
| `YiSyncFold.lagda.md` | 113 / 89 | 0 | 1.93 GB |
| `YiSyncTwo.lagda.md` | 47 / 26 | 0 | 1.72 GB |

- 每个文件约 10 秒。
- 检索 `postulate`、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`irrelevant-projections`、`--cubical`、`{!`、行尾 `?`、`Funext`、本机路径，结果为 0。
- 选项行都是 `--safe --without-K --lossy-unification`。没有改任何已有文件。

#### 3 定理表

**记号：**
- `ψ₁ = W.Ψ (suc zero) V2 (W.cmpw V2 s₂)`：树的目标层 1 折叠。
- `G₂`, `A`：`YiShpSq` 的前缀族。
- `F₁ n = proj₁ ψ₁ᴸ-lim n`。
- `K₁ = WL.Kfk zero Tψ`；`ψ₁ G.top ≡ G.lc (inj₁ tt) K₁`。

**档：** 下表每一行都是编译定理，都无前提。最后两行另有一条判断：参照的读法 ψ₀(Ω_Ω+Ω₂)。

| 名字 | 逐字陈述 | 白话 | 文件 |
|---|---|---|---|
| `_⊴⁺_` | `data _⊴⁺_ : T₁ → R₁ → Set`：`NA._⊴_` 的各规则限于第 1 层，加 `dg : ∀ {F : ℕ → T₁} {g : R → R₁} → (∀ n a → Cp zero (plus zero G.top (W.Tw 2)) a → F n ⊴⁺ g a) → L.lim F ⊴⁺ G.lc (inj₁ tt) g` 和 `≅⊴ : ∀ {x y : T₁} {η} → x L.≅ y → y ⊴⁺ η → x ⊴⁺ η` | 新关系：参照的 ℕ 极限逐项落在保留结点的分支之下（`top + Tw 2` 以上的一切分支）；左边可以按 ≅ 换代表 | Rel |
| `⊴→⊴⁺` | `∀ {x : T₁} {η} → x NA.⊴ η → x ⊴⁺ η` | 旧关系推出新关系 | Rel |
| `⊴⁺-cp` | `∀ {x η η′} → x ⊴⁺ η → Cp (suc zero) η η′ → x ⊴⁺ η′` | 右边沿第一位置上移 | Rel |
| `⊴⁺-+ˡ` | `∀ θ {x η} → x ⊴⁺ η → x ⊴⁺ plus (suc zero) θ η` | 右边左侧加前缀 | Rel |
| `⊴⁺-+ʳ` | `∀ {x η} → x ⊴⁺ η → ∀ η′ → x ⊴⁺ plus (suc zero) η η′` | 右边右侧加 | Rel |
| `⊴⁺-add₁` | `∀ {x : T₁} {η} → x L.≅ x → x ⊴⁺ η → ∀ {x′ : T₁} {η′} → x′ ⊴⁺ η′ → (x L.+ x′) ⊴⁺ plus (suc zero) η η′` | 加法上下文（左加数要 ≅ 自反） | Rel |
| `suc-step⁺` | `∀ {A : T₁} {β} → A L.≅ A → A ⊴⁺ β → L.lim (iterᴸ (A L.+_) L.zero) ⊴⁺ succ (suc zero) β` | ω 倍 | Rel |
| `chain₁′` | `∀ n → F₁ (suc n) NA.⊴ K₁ (G.suc (ξ (proj₁ (YB.chainV (suc n)))))` | YiL1 的 `chain₁` 去掉最后一步 | Diag |
| `F₁0≅` | `F₁ 0 L.≅ γ 1 1` | 对角线第 0 项换代表 | Diag |
| `F₁⊴K` | `∀ n a → Cp zero (plus zero G.top (W.Tw 2)) a → F₁ n ⊴⁺ K₁ a` | 对角线每项在门槛以上的一切分支之下 | Diag |
| `Diag` | `L.ψ (σB L.zero) (λ r → r) (L.Ω S2.ℓ₀) ⊴⁺ ψ₁ G.top` | 静态对角线 ψ₁(Ω_{ℓ₀}) 在 Ω₁ 结点 `ψ₁ top` 之下 | Diag |
| `fold1⁺` | `∀ {X : T₁} {η} → X ⊴⁺ η → X L.≅ X → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA X) ≼ NA.read (Ψ₀ (G₂ η))` | 第 1 层的关系经前缀 Ω_{ℓ₀} 送到第 0 层的值 | Fold |
| `Z⊴` | `∀ (B : Raw (tw 2)) → L.ψ (σB L.zero) (λ r → r) (L.Ω S2.ℓ₀) ⊴⁺ ψ₁ (plus (tw 2) G.top B)` | 底情形 | Fold |
| `CtxA` | `∀ {y b : T₀} → y ≼ b → ∀ a → b ≡ NA.read a → L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ⊴⁺ ψ₁ (A a)` | 嵌入情形（第 1 层版的 `ctxA`） | Fold |
| `Fold₀ᴾ` | `∀ {y : T₀} {η} → y NA.⊴ η → L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ⊴⁺ ψ₁ (G₂ η)` | 第 0 层参照经第 1 层的 ψ | Fold |
| `Fold₁ᴾ` | `∀ {X : T₁} {η} → X ⊴⁺ η → X L.≅ X → L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σA X) ⊴⁺ ψ₁ (G₂ η)` | ψ₁(Ω_{ℓ₀}+X) 不高于 ψ₁(G₂ η)，关系保持 | Fold |
| `e₂⊴γ₂` | `∀ n → e₂ n ⊴⁺ γ₂ n` | 参照第 n 项在层号 1 的链的第 n 点之下 | Two |
| `sync₂` | `Sync₂` | `YiShpTwo` 条件定理的前提 | Two |
| `X₂≼ʷ` | `S2.X₂ ≼ NA.read W.T⁺ʷ` | ψ₀(Ω_Ω+Ω₂) ≤ T⁺ʷ | Two |
| `X₂≼TΛ` | `S2.X₂ ≼ NA.read W.TΛ` | ψ₀(Ω_Ω+Ω₂) ≤ TΛ | Two |

#### 4 办法（与 YiL1 相比新用到的）

**`dg` 的门槛与草案不同。** 草案要对每个 n 给一个 m，门槛是 `suc (top + psum obs m)`。我改成一个统一的门槛 `top + Tw 2`，并对一切 n、一切过门槛的 a 要求 `F n ⊴⁺ g a`。
- 理由：目标层 0 在前缀 `G₂` 下折叠这个结点时，链的第 1 点是 `top + Ψ₀ (G₂ (g top))`，它总在 `top + Tw 2` 之上（`Ψ₀ top` 就是 `Tw 2`）。所以 `fold1⁺` 的 `dg` 情形是 `≼l 1`。
- 每个 YiL1 门槛 `suc (top + psum obs m)` 都在 `top + Tw 2` 之下（`c₁`），所以草案的前提推出我的前提。
- n = 0 也落在同一门槛下（`c0`）。

**新规则 `≅⊴`。**
- 用处：`F₁ 0` 与 `γ 1 1` 的 Sim 不同，只有 `≅`，没有 `≡`。
- 代价：`⊴⁺-add₁` 与 `suc-step⁺` 的左加数要 ≅ 自反。
- 两条折叠引理各用 `ψ⁰-≅` / `ψ-≅` 处理这种情形。

**`Fold₁ᴾ` 的结构。** 它照 `Lv1.Ψ₁⊴Φ` 与 `fold1` 写，用到三处保留：
- 派发在 `s₀″` 处保留（`dl-keep`），所以 `ψ₁ (G₂ (lc (inj₁ tt) g))` 定义性地是 `lc (inj₁ tt) (ψ₁ ∘ G₂ ∘ g)`。由此，`⊴b`、`nd`、`dg` 三种情形都原样过去。
- 参照的 `limᵢ` 在 ψ₁ 下是穿透情形，对上 `nd`。
- 根位置的保留（`dl-p₀`）给出 `ψ₁ top = lc (inj₁ tt) K₁`，这是 `Diag` 的落点。

**`chain₁′`。** 照抄 YiL1 的 `chain₁`，只去掉最后的 `⊴-cp`。

**没有用的东西。** 值单调、上界、同值、`FUNC`、`KEYsuc`、函数外延都没有用。

#### 5 第一个障碍

**交给我的范围内没有障碍**，所以没有报错原文，也没有缺的引理。

以下是判断，没有编译过：
- `dg` 的门槛（`top + Tw 2`）、`Diag`、`Fold₁ᴾ` 都只对前缀 `G₂`（`top + Tt top + gm₂ η`）与 Ω₁ 结点 `ψ₁ top` 陈述。
- 往上一站，例如参照里出现 Ω₂·2 或 Ω₃，大概要按新的结点与前缀重陈述门槛，并给出新的 `Diag`。是否可以对位置参数化，没有试过。

#### 6 偏离与事故

- **一次编译错误，已修好。** `YiSyncFold` 第一次编译报 `UnsolvedConstraints`（`blocked on _b_…`）：`⊴s` 情形里 `G₂mono (inj₂ (inj₁ refl))` 的隐式参数 b 要经 `W.Ψ` 反解，解不出。修法是在 `Fold₀ᴾ` 与 `Fold₁ᴾ` 的 `⊴s` 情形里匹配 `{η = G.suc η}`，并显式写 `{a = η} {b = G.suc η}`。
- **修改方式。** 这次修改是在我自己的文件上用 python 字符串替换做的，没有用 Edit 工具。
- **编译命令。** 外面加了 `/usr/bin/time -l` 来量内存。退出码不经管道，直接取自 agda。
- **没做的事。** 没有用 `--ignore-interfaces`。只删过自己四个模块的接口，用的是字面路径。没有碰已有文件、`src/`、`archive/`。
- **日志位置。** `<实验目录>/agents/sync/`，其中冷编日志是 `cold-YiSync*.log`。
