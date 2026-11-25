# 对目标层 k 一般的读回关系 (YiRelK)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 12:21 至 13:08 |
| 工具调用 / agda 编译 (粗数) | 61 / 11 |
| token (usage 字段，按消息去重) | 输出 272199；新写入缓存的输入 785176；读缓存的输入 16110695；其余输入 112 |
| 写过的仓库文件 | `YiRelK.lagda.md`, `YiRelKFold.lagda.md`, `YiRelKInst.lagda.md`, `YiRelKOne.lagda.md`, `YiRelKTwo.lagda.md` |
| 文件前缀 | `YiRelK` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: 对目标层 k 一般的读回关系一路返回并复核; 第九批合读 (主审)” 一节 |
| 主审复核后的一句结论 | 一条关系 Rel k 与一条一般折叠引理；k = 1 实例无前提重证 X₂≼TΛᴷ；ψ₀(Ω_Ω+Ω₃) 条件于 Chain₂ᴿ；五件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的指示是 "朝着最终目标的关键路径走", 方针 "边重构边做, 只动值的前沿碰到的那块"; 你这一路是 **对目标层 k 一般的读回关系**: 对 k 递归定义带对角规则的关系与折叠引理, 一条定理给出一切层; 先重新得到第 1, 2 层, 再求第 k 层的 BTBO 链点与 ψ₀(Ω_Ω+Ω₃). 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 背景 (事实)

- 现折叠: 燃料搜索的一致折叠 `probes/OCF/Lean/YiDlFold.lagda.md`; 闭项 `TΛ`, `T⁺ʷ`. 无前提的最高下界: `YiSyncTwo.X₂≼TΛ` (参照读作 ψ₀(Ω_Ω+Ω₂), 读法判断).
- 现有的分层写法 (都在 `probes/OCF/Lean/`):
  - 第 0 层: `YiNextAcc.lagda.md` 的 `_⊴_` 与 `read`; `YiDlVOne` 的 `ctx`.
  - 第 1 层: `YiSyncRel.lagda.md` 的 `_⊴⁺_` (对角规则 `dg`, 门槛 `top + Tw 2`, `≅⊴`), `YiSyncDiag` (`Diag`), `YiSyncFold` (`fold1⁺`, `Fold₁ᴾ`), `YiL1*` (第 1 层的 BTBO 下界 `base₁`, `chain₁`; 主线 `YiLeanValFold.FOLD` 在目标层 1 上).
  - 第 2 层: `YiStepRel2.lagda.md` 的 `_⊴²_` (规则 `n1`, `t1`, `n0`, `dg` 等), `YiStepFold2` (`F2.Fold22`, `F2.Fold21`, `F2.fold2²`, 条件于 `Diag₂`), `YiStepDiag2` (`Chain₂`, `chain→diag`, `X₃≼ᵇ : Chain₂ → X₃ ≼ NA.read W.TΛ`, `F₂0⊴K`), `YiStepMain2` (`foldM₂`, `R₂ᵗ`), `YiStepPfx` (第 1 层引理对分支族参数化).
- 回报 `probes/Survey/Reports-2026-11-12/YiStep.md` 全读, 特别是 §4, §5: 第 2 层的 BTBO 链点 `Chain₂` 断在把主线的 `RelF 2` 换成 `⊴²` 时第 1 层槽位上的规则, 缺 `∀ {y a} → y ⊴⁺ a → Σ a′ (RelF 1 y a′ × RR 1 1 a′ a)`, 执行方判断它一般不成立 (因为 `⊴⁺` 有对角规则而 `RelF 1` 没有), 并判断要在一致折叠一侧对层号 ≥ 3 的层建关系, 层号 1 的槽位用带 `dg` 的关系, 主线的 `RelF` 家族在那里不能借用. 执行方的翻译账: `n1`, `t1`, `n0`, `n0′` 的形状读自参照 ψ 的穿透规则.
- 产出端折叠上的同一缺口: `probes/Survey/Reports-2026-11-12/YiWay.md` §5 (非零目标层上的值下界).

#### 要交的, 分步; 每做成一步先交

1. **一般的关系**: 对目标层 k (至少 k 取有限数; 写成对层号参数化最好) 定义带对角规则的读回关系 `_⊴[ k ]_` (或你认为合适的写法), 以及加法上下文, ω 倍, 第一位置上移等引理, 一条定理对一切 k 成立. 检验: 第 1, 2 层的实例给出 `YiSyncRel._⊴⁺_`, `YiStepRel2._⊴²_` 能证的东西 (例如重新证出 `Diag` 与 `X₂≼TΛ`, 或证它们与新关系的对应).
2. **一般的折叠引理**: 目标层 k, k−1, …, 0 的折叠引理对 k 一般地陈述与证明 (`Fold22`, `Fold21`, `fold2²` 的一般形).
3. **第 k 层的 BTBO 链点**: 一般 k 的 BTBO 链点 (第 1 层的 `chain₁` 与 `Chain₂` 的一般形), 不借用主线的 `RelF` 在层号 1 槽位上的部分 (若执行方的判断对, 那里不能借); 由它得到 ψ₀(Ω_Ω+Ω₃) 的参照不高于 `NA.read W.TΛ`, 再往一切有限 n.
4. **做不过去时**: 给出确切的缺口 (缺的引理的 Agda 类型, 检查器报错原文), 并说清它在关系一侧还是派发一侧.

**翻译账**: 回报里写清关系的每条规则读自什么 (树侧的需要, 还是参照 ψ 的规则), 新加的规则是否有树侧的理由.

只要下界 (作者 2026-11-11 的原则). 参照的读法没有逐项一致证明时写成判断.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K; 堆到 6G 仍耗尽 (先按手册 §4.2). 没有编译的否定时只写 "未走通".

#### 先读什么

`AGENTS.md` (Agda 一节, "攀爬与摆脱翻译要平衡", "中间站给界", 文字预算, 结论的写法); `probes/Survey/EBOHandbook.md` §4.1 到 §4.5 与 §5.4; 上面列的 YiSync, YiStep 文件全读; `YiL1Base`, `YiL1Read`, `YiL1Emb` 检索要用的名字; 参照 `probes/OCF/Align/Level.lagda.md` (`ψ`, `ψ⁰`, `Ω`, `add`, `Simᴵ`, `tr⁻`), `Stage2.lagda.md` (`ℓ₀`, `X₂`). 查签名用检索.

#### 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiRelK` (模块名 `OCF.Lean.YiRelK…`). 都是验收文件, 文首标 "验收文件". 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞 (写入文件时也不要留洞), `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提.
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 堆墙多出在比较具体闭项的地方: 陈述逐字写, 不用别名; 大参照树放 `opaque`; 经非单射的头求解的隐式参数显式写出 (手册第 4 节).
- 仓库文件里不写本机路径. 不要把仓库整个拷到临时目录.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽. 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块; 另有一路也在跑.
- 你的临时目录: `<实验目录>/agents/relk`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 过程要求: 读完上面的文件后尽快动手, 第一个文件在 25 分钟内写出并编译; 每次回复都要有工具调用, 不要在一次回复里只思考.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 回报格式 (只在回报里交一次)

1. 判决: 做到第几步; 一段话说对目标意味着什么 (有没有对 k 一般的关系; `TΛ` 已证的最高下界; 停在哪里).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断).
4. 办法与翻译账.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 中途消息（主审发给这一路）

转录时间戳 2026-11-12 12:53 (UTC)：

主审转告一条已复核的事实 (第十次独立审查, 主审已在自己的目录冷编, 退出码 0), 供你参考, 是否采用由你判断, 不改变你的简报.

1. 主线 `OCF.Lean.YiLeanValFold.FOLD` 本来就对一切可数层号、一切满足 `Pl m` 的目标层成立; `YiL1` 的 `foldM₁` 与 `YiStepMain2.foldM₂` 都是它的实例.
2. 审查者在主线的关系族 `YiLeanValRel.Lvl` 里加了一条一般的对角规则:
   `dgr : ∀ {j} {r g} {F : ℕ → L.Ordᶜ j} (θ : Lay.A (Lo K r)) → Corr L.zero (lev K r) → (∀ n a → Le (Lo K r) θ a → F n ⊴ g a) → L.lim F ⊴ G.lc r g`
   主线 `FOLD` 加前提 "目标层在层号 0 之上" 后原样通过 (dgr 结点上派发由 `Agree` 必保留, 折叠分支是荒谬); 目标层 2 的实例 `foldM₂ᵈ` 通过, 并且层号 1 的槽位上的关系定义性地就是带 dgr 的 `RelF 1` (`slot₁ = refl`). 所以 YiStep 回报 §5 "第 1 层槽位上借不过来" 的障碍是换族造成的, 把 dgr 加进同一族即可重用 FOLD (对目标层 ≻ 0).
3. 审查者的判断 (未编译): YiStep 的 `n1`, `n0`, `n0′` 是主线 `Lvl.ndr` 的实例, `t1` 是 `tnr ∘ ndr`, 不是读自参照 ψ 的规则; 剩下要做的是 (A) 把这一族搬到一致折叠上, (B) 目标层 0、Ω_{ℓ₀} 前缀下的一般前缀折叠定理 (dgr 在这里有门槛义务), (C) 对 m 一般的 `Chain_m` (要 `TB_m` 与固定 0..m 的嵌入).
4. 实验文件 (纯 .agda, 可读): `<实验目录>/agents/review10/` 下的 `R10Rel.agda` (Lvl 加 dgr), `R10Add.agda`, `R10Fold.agda` (FOLD 加前提), `R10Inst.agda` (foldM₂ᵈ, slot₁, dg-inst). 只读, 不要改它们, 也不要在那个目录写文件.

## 回报原文

#### 1 判决

**做到第 2 步, 第 3 步未走通。**

- **对 k 一般的关系有了, 是一条定义。** `Rel k` 对 k ∈ ℕ 递归, 槽位关系 `Hyp` 与它互递归, 对角规则 `dg` 放在每一层层号 0 的槽位上。右加、左加、加法上下文、ω 倍、第一位置上移, 各是一条对一切 k 的编译定理。
- **两个实例做了检验。**
  - `Rel 1` 与 `⊴⁺` 在 T₁ 上互推 (`from1`, `to1`), `⊴²` 进 `Rel 2` (`from2`)。
  - 第 1 层: 经一般折叠引理, 无前提地重新证出 `X₂≼TΛᴷ : S2.X₂ ≼ NA.read W.TΛ`。
  - 第 2 层: 经同一引理重新得到 YiStep 的条件定理 (`X₃≼ᵀ`)。
- **一般的折叠引理有了 (第 2 步)。** `FoldK.Fold` 对一切输入层 K、目标层 t、Sim σ 是一条定理, 取代 `Fold22`/`Fold21`/`fold2²` 及其部件。它的条件是接口 `Pf`, 里面是树一侧的事实和各目标层的对角线 `Z`。接口在 k = 1 上全部是编译定理; k = 2 上只差一个前提 `Diag₂ᴿ`, 其余字段的派发事实都是 `refl`。
- **`TΛ` 已证的最高无前提下界没有变**, 仍是 ψ₀(Ω_Ω+Ω₂) 的参照 (读法是判断)。ψ₀(Ω_Ω+Ω₃) 仍是条件定理, 前提归约到 `Rel 2` 上的第 2 层 BTBO 链点 `Chain₂ᴿ` (`X₃≼ʰ`); `chain₂→ : Chain₂ → Chain₂ᴿ`, 所以新前提不比原来的强。
- **停在第 2 层的 BTBO 链点, 原因在关系一侧, 不在派发** (详见 §5)。一般 k 的链点、ψ₀(Ω_Ω+Ω₃) 的无前提下界、一切有限 n, 都没有做到。

#### 2 文件表

都在 `<仓库>/probes/OCF/Lean/`。先删掉这 5 个文件自己的接口, 再按依赖次序冷编译。每个日志只有自己模块的 1 行 `Checking`。检索 `postulate`、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`irrelevant-projections`、`--cubical`、洞、`Funext`、本机路径, 结果都是 0。选项行都是 `--safe --without-K --lossy-unification`。

| 文件 | 总行 / 代码行 | 冷编译退出码 | 常驻内存峰值 |
|---|---|---|---|
| `YiRelK.lagda.md` | 256 / 186 | 0 | 1.95 GB |
| `YiRelKInst.lagda.md` | 134 / 100 | 0 | 1.95 GB |
| `YiRelKFold.lagda.md` | 344 / 260 | 0 | 1.84 GB |
| `YiRelKTwo.lagda.md` | 290 / 212 | 0 | 1.87 GB |
| `YiRelKOne.lagda.md` | 161 / 123 | 0 | 1.89 GB |

冷编译日志在 `<实验目录>/agents/relk/cold-*.log`。

#### 3 定理表

记号:
- `Lk k` 是第 k 层的层号, `ℓk k` 是参照层号 suc^k 0, `thr = plus zero G.top (W.Tw 2)`。
- `ρ q σ X = L.ψ q (λ r → r) (L.add (L.Ω ℓ₀) σ X)`。
- 凡含 `X₃` 或 `S2.X₂` 的行另有一条判断: 参照读作 ψ₀(Ω_Ω+Ω₃) 或 ψ₀(Ω_Ω+Ω₂), 没有逐项一致证明。

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `Rel`, `Hyp` | `Rel : (k : ℕ) → ∀ {ℓ} → L.Ordᶜ ℓ → Raw (Lk k) → Set`; `Rel zero = R0`, `Rel (suc m) = L1._⊴_ m (Rel m) (Hyp (suc m))` | 对 k 递归的读回关系 | YiRelK | 定义 |
| `Rel-cp` | `∀ k {ℓ} {x : L.Ordᶜ ℓ} {η η′} → Rel k x η → Cp (Lk k) η η′ → Rel k x η′` | 右边沿第一位置上移 | YiRelK | 编译定理 |
| `lfR` (`Rel-+ˡ` 是它的实例) | `∀ m K (B : Bld (Lk (suc m)) (Lk K)) → Bok (suc m) K B → ∀ θ {ℓ} {x : L.Ordᶜ ℓ} {η} → Rel K x η → Rel (suc m) x (add (Lk K) B θ η)` | 左加, 对一切造结点办法 | YiRelK | 编译定理 |
| `Rel-+ʳ` | `∀ m {ℓ} {x : L.Ordᶜ ℓ} {η} → Rel (suc m) x η → ∀ η′ → Rel (suc m) x (plus (Lk (suc m)) η η′)` | 右加 | YiRelK | 编译定理 |
| `adR` (`Rel-add` 是它的实例) | `∀ m K (B : Bld (Lk (suc m)) (Lk K)) → Bok (suc m) K B → ∀ {ℓx} {x : L.Ordᶜ ℓx} {θ} → x L.≅ x → Rel (suc m) x θ → ∀ {ℓ} (σ : L.Simᴵ ℓ ℓx) {y : L.Ordᶜ ℓ} {a} → Rel K y a → Rel (suc m) (L.add x σ y) (add (Lk K) B θ a)` | 加法上下文, 右加数可在任一参照层号 | YiRelK | 编译定理 |
| `Rel-ω` | `∀ m {ℓ} {A : L.Ordᶜ ℓ} {β} → A L.≅ A → Rel (suc m) A β → Rel (suc m) (L.lim (iterᴸ (A L.+_) L.zero)) (succ (Lk (suc m)) β)` | ω 倍 | YiRelK | 编译定理 |
| `Ω⊴top` | `∀ m → Rel (suc m) (L.Ω (ℓk (suc m))) G.top` | 起点 | YiRelK | 编译定理 |
| `from1`, `to1` | `∀ {x : T₁} {η} → x S.⊴⁺ η → Rel 1 x η`; `∀ {x : T₁} {η} → Rel 1 x η → x S.⊴⁺ η` | 第 1 层在 T₁ 上与 `⊴⁺` 互推 | YiRelKInst | 编译定理 |
| `from2` | `∀ {ℓ} {x : L.Ordᶜ ℓ} {η} → x R2.⊴² η → Rel 2 x η` | `⊴²` 进 `Rel 2` | YiRelKInst | 编译定理 |
| `Diag¹` | `Rel 1 (L.ψ (σB L.zero) (λ r → r) (L.Ω S2.ℓ₀)) (ψ₁ G.top)` | 第 1 层对角线 | YiRelKInst | 编译定理 |
| `TRC-all` | `∀ k → TRC (Rel k)` | 关系对层间搬运 `tr⁻`/`tr` 封闭 | YiRelKFold | 编译定理 |
| `FoldK.Fold` | `∀ K {Φ} (P : Pf K Φ) t → Tg t → ∀ {i} (q : i <ᴵ ℓ₀) → i ≅ᴵ ℓk t → ∀ {ℓ} (σ : L.Simᴵ ℓ ℓ₀) {X : L.Ordᶜ ℓ} {η} → Rel K X η → X L.≅ X → Rel t (ρ q σ X) (Φ t η)` | 前缀 Ω_{ℓ₀} 下一切输入层与目标层的折叠引理 | YiRelKFold | 条件定理 (接口 `P`) |
| `e₂⊴γ₂ᴷ` | `∀ n → Rel 1 (e₂ n) (γ₂ n)` | 第 1 层链上逐点 | YiRelKOne | 编译定理 |
| `X₂≼TΛᴷ` | `S2.X₂ ≼ NA.read W.TΛ` | 经一般引理重新证出 ψ₀(Ω_Ω+Ω₂) 的下界 | YiRelKOne | 编译定理 |
| `X₃≼ᴿ` | `Diag₂ᴿ → X₃ ≼ NA.read W.TΛ`, 其中 `Diag₂ᴿ = Rel 2 (L.ψ (σ₃ L.zero) (λ r → r) (L.Ω S2.ℓ₀)) (ψ₂ G.top)` | ψ₀(Ω_Ω+Ω₃), 前提是第 2 层对角线 | YiRelKTwo | 条件定理 |
| `X₃≼ᵀ` | `Diag₂ᵀ → X₃ ≼ NA.read W.TΛ` | 经 `from2` 重新得到 YiStep 的 `X₃≼ᵈ` | YiRelKTwo | 条件定理 |
| `chain₂→` | `Chain₂ → Chain₂ᴿ` | 新前提不比原来的强 | YiRelKTwo | 编译定理 |
| `chain→diagᴿ` | `Chain₂ᴿ → Diag₂ᴿ`, 其中 `Chain₂ᴿ = ∀ n → Σ ℕ (λ m → Rel 2 (F₂ (suc n)) (K₂ (G.suc (ξ m))))` | 对角线归约到 BTBO 链点 | YiRelKTwo | 条件定理 |
| `X₃≼ʰ` | `Chain₂ᴿ → X₃ ≼ NA.read W.TΛ` | 本路关于 Ω₃ 的最终结论 | YiRelKTwo | 条件定理 |

#### 4 办法与翻译账

**办法。**
- **关系。** 第 k+1 层的一个归纳族 `L1._⊴_` 以第 k 层的关系 `Rm` 与槽位关系 `H` 为参数; `Rel`/`Hyp` 对 k 互递归。
  - 结点规则 `nd` 对一切位置只有一条, 只要求参照结点的下标 `≅ᴵ lvI r`。
  - YiStep 的 `n1`, `n0`, `n0′` 都是 `nd` 的实例 (`from2` 逐条对应)。
  - 加法引理对 "造结点的办法" `B` 及其相容性记录 `Bok` 一般地证明; 进孩子时 `B ∘ inj₂` 的相容性定义性地传下去。
- **折叠。**
  - Sim σ 取任意, 所以 YiStep 按参照层号分开写的 `Fold22`/`Fold1²2`/`Fold0²2` 合成一条。
  - 结点按参照的 `<ᴵ-dec` 分三种: 穿透时用 `kΦ`, 分支先 `tr⁻` 搬回 (`TRC-all`); 另两种用 `fΦ`, 两条链同步。链点的假设由目标层 j 的同一引理给出。
  - 结点经 `Path` 下到 `bld π (inj₁ tt) g`, 使分支类型定义性地是 `Raw (Lk j)`。
  - `top` 用 "根位置上分支为嵌入的结点" 处理 (字段 `tp`, 实例里是 `refl`)。
- **接口实例。** k = 1 (前缀 `G₂`) 与 k = 2 (前缀 `G₃`) 的派发事实都是 `refl`。

**翻译账 (以下是判断)。**
- 零、后继、极限、第一支、嵌入 `em`、`top` (`nt`, 来自树的读回 `upT`): 树侧的结构。
- `u⊴`, `≅⊴`: 参照树的构造子与代表元的簿记, 不是 ψ 的规则。
- `nd`: 与主线 `Lvl.ndr` 同形。"下标 ≅ᴵ 位置的层号" 是两侧派发对齐的要求。`≅ᴵ` 而不是 `≡`, 是被参照的 `<ᴵ-dec` 输出的代表元逼出的。没有读自参照 ψ 穿透规则的新规则。这与 YiStep 回报对 `n1`/`n0` 的归类不同, 与第十次审查的判断一致。
- `dg` 与门槛 `thr`: 来自树侧, 即目标层 0 在 Ω_Ω 前缀下折叠时链的第 1 点过门槛 (`dfΦ` 的实例用 `thrp`)。新的只是位置: 每一层所有层号 0 的槽位都有 `dg` (`Z0`)。
- 槽位关系取带 `dg` 的同一族: 由折叠逼出, 因为链同步把目标层 j 的输出喂给槽位假设, 而那输出经 `Z` 含 `dg`。
- 接口字段都读自树的折叠 `W.Ψ`, 只有 `Z` (各层对角线) 是与参照静态对角线的接点。
- 加深翻译的标志这次没有新增: 没有读自记号基本列的新字段, 闭包定理也没有按阶段加专属前提。

#### 5 第一个障碍

**位置: `Chain₂ᴿ` (以及一般 k 的 `Chain_k`)。走过两条路。**

**(a) 经主线 `FOLD` 再经互模拟 `RR` 换到一致折叠。** 这条路即使在主线族里加上审查者的 `dgr` 也不通。障碍不在 `dg`, 而在层号 1 槽位上的反向翻译:
- 主线结果的 `ndr` 假设要对一切一致折叠的下标 b 给出主线的 b′, 且 `RR b′ b`。
- 第 0 层有 `toM-R`。第 1 层的对应在 Ω₁ 结点处断开。
- 实验文件 `<实验目录>/agents/relk/t/T5.agda` 写了 `toM₁` 与 `toM₁-R`, 检查器报错原文:
```
T5.agda:31.48-61: error: [UnequalTerms]
η′ != fromM η of type
N.G.R (N.Pre N.zero) (λ r → N.Lay.A (N.Lo N.zero r)) (N.Kid N.zero)
(λ i → N.Lay.A (N.KS N.zero i))
when checking that the expression toM₁-R (g η′) has type
OCF.Lean.YiNextValRel.GR.Rel
(OCF.Lean.YiNextValRel.PR (M.suc M.zero) (N.suc N.zero))
(OCF.Lean.YiNextValRel.LayRel (M.suc M.zero) (N.suc N.zero))
(toM₁ (g (fromM η))) (g η′)
```
- 缺的引理: `∀ (g : N.Raw N.zero → N.Raw (N.suc N.zero)) η η′ → RR M.zero N.zero η η′ → RR (M.suc M.zero) (N.suc N.zero) (toM₁ (g (fromM η))) (g η′)`。它要 `RR M.zero N.zero η η′ → fromM η ≡ η′`, 在 ℕ 极限处要函数外延 (简报的停下条件)。
- 这条路的总缺口, Agda 类型: `∀ {y : T₁} {a : NA.R₁} → Rel 1 y a → Σ (M.Raw (M.suc M.zero)) (λ a′ → RelFᵈ 1 y a′ × RR (M.suc M.zero) (suc zero) a′ a)`, 其中 `RelFᵈ` 是加了 `dgr` 的主线族。
- 判断, 没有编译的否定, 只写 "未走通"。

**(b) 直接在一致折叠上做 (关系一侧, 没做)。**
- 要一族对一切 Pl 层号定义的带对角规则的关系 `RelFᵘ`, 建在 YiNext 块上。
- 要折叠引理, 类型:
  `FOLDᵘ : ∀ {K} (V : WL.Lw K) m → Pl m → (x : Ext m K) → ∀ {i ℓ} (p : i L.<ᴵ ℓ) → Corr i m → Agree x i → ∀ {κ} (σ : L.Simᴵ κ ℓ) {y : L.Ordᶜ κ} {ξ} → RelFᵘ K y ξ → RelFᵘ m (L.ψ p σ y) (W.Ψ m V x ξ)`
  (目标层 m = Lk t, t ≥ 1), 并要 `RelFᵘ (Lk t) ⊆ Rel t`。
- 还要 `lower₁ᴱ` 在目标层 2 的对应 (层号嵌入固定 0, 1, 2), 在参照一侧。
- 派发一侧 (判断): 链点所在的 Pl 层号上, `cmpw V2 s₃` 对有限字面层号 0, 1 保留、其余折叠, 满足 `Agree`; 与 YiStep 的 `root-fold₂` 一致。

**一般 k 另缺 (派发一侧, 没做)。** 接口实例 `∀ k → (∀ t → t ≤ k → Diag_t) → Pf k (λ t a → ψ_t (G_{k+1} a))`, 要对一般 k 定义 G_{k+1}, s_{t+1}, ψ_t。还要证 `dlev (Lk t) (tw 2)` 在 `(suc^k top, tt, inj₂^d (inj₁ tt))` 上保留或折叠: 现在这些在 k = 1, 2 上都是 `refl`, 一般 k 时是关于 `finOf`, `look` 的命题等式, 还要化成 `Ψn` 能归约的形状。

#### 6 偏离与事故

- 多交了两个文件, 都在前缀内: `YiRelKOne` (第 1 层实例, 无前提重证 `X₂≼TΛ`) 与 `YiRelKTwo` (第 2 层实例与链点归约)。
- 一次编译失败, 已修好: `lfR`/`adR` 第一版终止检查失败。最小复现在实验目录 `T3`, `T4`: 对派生式的递归子句若同时匹配层号 `suc K`, 经 `u⊴` 的递归不被接受。改成层号分派 `lfR`/`adR` 与派生式递归 `lfS`/`adS` 两个函数 (后者的子句不匹配层号) 后通过。
- 复用了主线的 `TRC` 记录与 `Back` 模块 (从 `YiLeanValRel` 导入)。
- 主审转来的第十次审查事实已读。没有改用每个结点自带门槛的 `dgr`, 理由 (判断): 目标层 0 的前缀折叠要链的第 1 点过门槛 (`dfΦ`), 门槛任意时这条义务一般不成立, 所以保留固定的 `thr`。审查者的 (A)(B)(C) 中, 本路做了 (B) 与有限层号上的 (A); (C) 停在上面的缺口。
- 试验文件 `T0` 到 `T5` 是纯 `.agda`, 放在 `<实验目录>/agents/relk/t/`, 不进仓库。
- 编译外面加了 `/usr/bin/time -l` 量内存; 退出码是 agda 自己的, 没经过管道。
- 没有用 `--ignore-interfaces`。只用字面路径删过自己 5 个模块的接口。没有改已有文件, 没碰 `src/`、`archive/`, 没有写审查者的目录。
