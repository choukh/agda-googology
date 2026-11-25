# 只用下界：沿链造前驱嵌入 (YiPE)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-11 13:47 至 14:25 |
| 工具调用 / agda 编译 (粗数) | 62 / 8 |
| token (usage 字段，按消息去重) | 输出 232711；新写入缓存的输入 876484；读缓存的输入 10099837；其余输入 88 |
| 写过的仓库文件 | `YiPEBase.lagda.md`, `YiPEKey.lagda.md`, `YiPEStair.lagda.md`, `YiPEStep.lagda.md` |
| 文件前缀 | `YiPE` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 只用下界的前驱嵌入一路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 没有闭合；只用下界的 BTBO 下界归约到三条；新工具阶梯粘接与平移嵌入；四件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 任务是 **只用下界证明 "BTBO 的参照 ≼ 主线闭项"**, 不要求任何上界或两个方向的对上. 作者 2026-11-11 的原话: "只要证明 'BTBO是下界' 即可". 你的路线: 沿主线的链造前驱嵌入 (参照对角链第 n 项的层号的前驱, 保序地嵌进主线某个链点的层号的前驱), 不经一般的值单调. 另有一路 (前缀 `YiLow`) 同时用另一种办法 (严格树上的值单调) 攻同一个目标, 互不依赖. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 "第 4 层不反过来改前 3 层", Agda 一节 (选项, 文字预算, 退出码, 堆; 函数外延只准作前提), "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 与 §5.4.
3. **回报原文**: `probes/Survey/Reports-2026-11-11/YiMono.md` (全读; §5 列了这条路缺的四条引理: 第 0 层 ψ⁰ 对嵌入的函子性, 平移嵌入, 各块嵌入的一致性, 第 1 层闭项的结构刻画), `YiLeanVal.md` (主线的下界证明), `YiChain.md` §4 (第 1 个链点怎么对上的, 结构前驱与吸收), `YiOver.md` §4 (主线的累加链对一条同样累加的参照链比, 只用结构).
4. 代码 (都已定稿, 可以导入, 不许编辑):
   - **陈述与已有的一环**: `probes/OCF/Align/YiMonoEmb.lagda.md` 逐字:
     ```agda
     EmbT = ∀ n → Σ ℕ λ m → PEmb (D.L n) (κ m)
     emb→dom : EmbT → DomT
     btbo-dom : DomT → D.BTBOᴵ ≼ read T₃ᵐ
     ```
     那是对旧块的闭项写的. 你要在主线新块上写同样的东西: `κ m = L.toLevel (read (co (pts m))) …` (`probes/OCF/Lean/YiLeanValFin.lagda.md` 的 `κ`, `T₃-own : ∀ n → L.ψ⁰ (L.Ω (κ n)) ≼ read T₃`), 然后 `EmbTⁿ → D.BTBOᴵ ≼ read T₃` (由 `Ψ-emb` 与 `T₃-own`; 只用下界).
   - 前驱嵌入的工具: `probes/OCF/Align/BTBOFullEmb.lagda.md` (`PEmb`, `Ψ-emb`), `YiMonoEmb.lagda.md` (`PEmb-⊑`, `PEmb-∘`, `PEmb-limʳ`, `PEmb-suc`, `PEmb-limˡ`), `YiMonoOne.lagda.md` (旧树上的 `emb₁ : PEmb (L.suc L.ωᴵ) (κ 1)`: 在真实链点上手造嵌入的例子), `probes/OCF/Align/YiVmConExact.lagda.md` (`XEmb`, `XEmb-limˡ`: 保值时左极限不要一致性; `embˣ`).
   - 结构工具: `probes/OCF/Lean/YiChainBase.lagda.md` (`Abs.ABS`), `YiFlatObs`/`YiFlatWit`/`YiFlatAbs` (`flat`, `HS-flatΩ`, `flatΩ-≺`, `absΩ`), `YiFlatChain.lagda.md` (`X≺`, `κ≺ : ∀ n → κ n L.≺ᴵ κ (suc n)`), `YiOverRef`/`YiOverOps`/`YiOverMain` (主线树对参照树的关系 `⊵`, `≤ₚ`, `step-γ`).
   - 参照: `OCF.Align.Level` (`toLevel`, `toLevel-⊑`, `toLevel-≺`, `_⊑ᴵ_`, `_≺ᴵ_`, `Ψ⁰-mono`), `OCF.Align.Diagonal`, `OCF.Align.YiBtValBT` 的 `module D` (`D.γ`, `D.L`, `D.cert`, `D.diag-step`).
   查签名用检索, 大文件不要整篇读.

#### 1 要交的, 分步; 每做成一步先交

1. **第 1 项.** `Σ ℕ λ m → PEmb (D.L 1) (κ m)`. 参照的 `D.L 1` 是 `toLevel (D.γ 1)`; 主线的 κ m 是链点读回的层号. 已知结构可比不成立 (`YiLeanValBreak.no-L`), 但前驱嵌入不要求结构可比. 先算两边层号的前驱是什么形状 (临时目录里纯 `.agda` 规范化, 有限测试), 再手造或由引理造出嵌入.
2. **一般的 n.** 对 n 归纳: 由 `PEmb (D.L n) (κ m)` 得 `PEmb (D.L (suc n)) (κ m′)`. 参照一步是 `D.γ (suc n) = ψ⁰ (Ω (D.L n))`, 主线一步是 `η + F η` 且 `F η` 不低于 `ψ⁰ (Ω (κ m))` (值上). 要的大概是: ψ⁰ (Ω ·) 的输出的前驱结构对嵌入的函子性 (由 `PEmb a b` 得 `PEmb (toLevel (ψ⁰ (Ω a))) (toLevel (读回的 F 的输出))` 一类), 以及 "加上一段" 的平移嵌入. 只要嵌入 (单向), 不要求保值, 不要求反向.
3. **无条件的 BTBO 下界.** `EmbTⁿ` 推出 `D.BTBOᴵ ≼ read T₃` (主线). 再接到下一站: 由 `probes/OCF/Lean/YiNextValFin.lagda.md` 的 `T₃≅ : MA.read MT.T₃ L.≅ NA.read NT.T₃` 与 `probes/OCF/Lean/YiNextAcc.lagda.md` 的 `T₃≼T⁺ : read T₃ ≼ read T⁺` 得 `D.BTBOᴵ ≼ NA.read NT.T⁺`. 两条都写成无前提的定理.

**已知的边界.** 由值序推导造保初始段的嵌入推出 LPO (`YiVmNegSeg`), 把推导改写成保值的推出 LPO (`YiVmConLPO`). 你的嵌入是沿具体的链用结构造的, 不经 "对一切值序推导" 的构造, 不在这些否定的范围里; 若你发现某一步要判定什么, 把那一步的类型写进回报.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理); 堆到 6G 仍耗尽 (先按手册 §4.2). 做不成的部分写成带确切类型的模块参数, 说明前提在哪些实例上是定理. 没有编译的否定定理时只能写 "未走通".

#### 2 过程要求

- 读完上面的文件后尽快动手: 第一个文件 (哪怕只是第 1 步两边层号的形状) 在 20 分钟内写出并编译.
- 每写完一个文件就编译; 每次回复都要有工具调用, 不要在一次回复里只思考.

#### 3 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiPE` (模块名 `OCF.Lean.YiPE…`). 都是验收文件, 文首标 "验收文件"; 允许导入带记号闭包的 `OCF.Align.Value`, `OCF.Align.Level` 与旧验收文件. 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`. 同时在跑的另一路用前缀 `YiLow` (在 `probes/OCF/Lean/`), 不要动也不要依赖它的文件.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/pe`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步; 一段话说对纲领与目标意味着什么 (`D.BTBOᴵ ≼ read T₃` 与对 `T⁺` 的同一条是无条件定理了没有).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型与它的可满足性.
4. 办法: 嵌入怎么造的; 一致性 (左极限) 从哪里来; 函子性与平移怎么证的.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型; 它是不是在要求判定什么.
6. 偏离与事故.
强度写 ψ₀(Ω_x), 标明是定理还是读法; 下界不写成同值; 不用 "只差", "自然" 一类形容.

## 回报原文

#### YiPE 一路回报：只用下界证 BTBO ≼ 主线闭项

##### 1 判决

只做成了第 1 步。第 3 步只有条件版本。第 2 步（一般的 n）没有证出，只归约到三条带确切类型的前提。

- **对纲领与目标的意思：** `D.BTBOᴵ ≼ read T₃` 与对 `T⁺` 的同一条，都还不是无条件定理。
  - 现在有三层条件定理：
    - `EmbTⁿ →` 两条下界；
    - `FUNC → KEY →` 两条下界；
    - `FUNC → KEYsuc → SpineT →` 两条下界。
  - 新的编译定理里没有更高的值下界。n = 1 的嵌入经 `Ψ-emb` 给出 `D.γ 2 ≼ read T₃`，读作 ψ₀(Ω_{ε₀})，与已有的 `YiChain` 的 `T₃-γ₂` 相同。我没有另写成定理。
  - ψ₀(Ω_Ω) 仍是读法。
- **新的正面结果是一个工具：阶梯粘接 `Stair.stair`（编译定理）。**
  - 适用条件：目标逐块累加 `t n ⊕ Y (n+1) ≅ᴵ t (n+1)`，源的每一步是 `≅ᴵ` 或带证据的 `≺ᴵ`。
  - 结论：各块任给的嵌入可以粘成极限的嵌入，**不要求各块在公共前驱上一致**。
  - 这回答了 YiMono 回报 §5 第 3 条（各块嵌入的一致性）：主线的部分和与链都是累加的，在极限层号上一致性不是障碍。
  - 用它证了：`KEY` 在极限层号上归约到各支。剩下的是后继层号 (`KEYsuc`)，外加一个严格上升的前提 (`SpineT`)。
- **平移嵌入**（YiMono §5 第 2 条）已证：`PEmb-shift : PEmb b (x ⊕ b)`，`⊕` 是层号上的左加。
- **函子性**（第 1 条，这里写成 `FUNC`）没有证。

##### 2 文件表

都在 `probes/OCF/Lean/`，都是验收文件，选项行都是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。

冷编译的做法：只按字面路径删本模块的 `.agdai`，按依赖序编译，堆上限 6G，每份日志只有本模块一行 `Checking`。

| 文件 | 代码行 / 总行 | 冷编退出码 | 常驻峰值 |
|---|---|---|---|
| `YiPEBase.lagda.md` | 31 / 52 | 0 | 1.49G |
| `YiPEStep.lagda.md` | 113 / 168 | 0 | 1.59G |
| `YiPEStair.lagda.md` | 100 / 149 | 0 | 1.43G |
| `YiPEKey.lagda.md` | 105 / 161 | 0 | 1.54G |

- 冷编顺序：Base → Step → Stair → Key。
- 检索 `postulate`、`{!`、` ? `、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`irrelevant-projections`、`--cubical`、`Funext`、本机路径：都是 0 处。

##### 3 定理表

`L` = `OCF.Align.Level`，`L⁺ a = L.toLevel (L.ψ⁰ (L.Ω a)) (Un.Uniform a)`，`Fκ m = L.toLevel (read (obs (pts m))) (HS-read (obs (pts m)) (F-lgl (co (pts m)) (lw (pts m))))`。

**YiPEBase**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `EmbTⁿ` | `∀ n → Σ ℕ λ m → PEmb (D.L n) (κ m)` | 前提 (定义) | — |
| `btbo-embⁿ` | `EmbTⁿ → D.BTBOᴵ ≼ read T₃` | 由 `Ψ-emb` 与 `T₃-own`，只用下界 | 条件定理 |
| `btbo-emb⁺` | `EmbTⁿ → D.BTBOᴵ ≼ NA.read NT.T⁺` | 再接 `T₃≅` 与 `T₃≼T⁺` | 条件定理 |
| `emb₀ⁿ` | `Σ ℕ λ m → PEmb (D.L 0) (κ m)` | n = 0 | 编译定理 |
| `emb₁ⁿ` | `Σ ℕ λ m → PEmb (D.L 1) (κ m)` | n = 1，取 m = 1，由 `YiChainOne.chainP₁` 经 `embᵖ` | 编译定理 |

**YiPEStep**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `PEmb-shift` | `∀ x b → PEmb b (x ⊕ b)` | 平移嵌入 | 编译定理 |
| `toLevel-+` | `∀ (X Y : L.Ordᶜ L.zero) (hX : L.HS X) (hY : L.HS Y) (h : L.HS (X L.+ Y)) → L.toLevel (X L.+ Y) h ≅ᴵ (L.toLevel X hX ⊕ L.toLevel Y hY)` | 读回的和的层号 | 编译定理 |
| `shift-κ` | `∀ m → PEmb (Fκ m) (κ (suc m))` | 链点 m 的折叠值嵌进下一个链点 | 编译定理 |
| `FUNC` | `∀ {a b} → PEmb a b → PEmb (L⁺ a) (L⁺ b)` | 参照一侧 ψ⁰∘Ω 对嵌入的函子性 | 前提 |
| `KEY` | `∀ m → PEmb (L⁺ (κ m)) (Fκ m)` | 同一层号上，参照对主线折叠的结构下界 | 前提 |
| `emb-FK`, `btbo-FK`, `btbo-FK⁺` | `FUNC → KEY → EmbTⁿ`；`FUNC → KEY → D.BTBOᴵ ≼ read T₃`；`… ≼ NA.read NT.T⁺` | 链上一步 = `FUNC`，再 `KEY`，再平移；取 m = n | 条件定理 |
| `key₀` | `PEmb (L⁺ (κ 0)) (Fκ 0)` | `KEY` 在 m = 0 | 编译定理 |
| `func-⊑` | `∀ {a b} → a ⊑ᴵ b → PEmb (L⁺ a) (L⁺ b)` | `FUNC` 的结论在结构可比的输入上 | 编译定理 |
| `tri→FUNC`, `tri→KEY` | `Tri → FUNC`；`Tri → KEY` | 经典模型里成立；`Tri` 推出 LPO (`YiVmConLPO`) | 编译定理 |
| `PEmb-≅ʳ`, `PEmb-≅ˡ`, `HS-≅` | 沿 `≅ᴵ`/`≅` 搬运 | 引理 | 编译定理 |

**YiPEStair**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `glue` | `∀ {a a′ T Y T′} → PEmb a T → PEmb a′ Y → (a ≅ᴵ a′) ⊎ (a ≺ᴵ a′) → (T ⊕ Y) ≅ᴵ T′ → PEmb a′ T′` | 一块的粘接 | 编译定理 |
| `glue-ext` | `… {c} (r : c ≺ᴵ a) (r′ : c ≺ᴵ a′) → map (glue Q P d eT) r′ ≅ᴵ map Q r` | 粘接延拓旧嵌入 | 编译定理 |
| `Stair.stair` | `PEmb (L.lim f s) B` | 阶梯粘接 | 编译定理 |

`Stair.stair` 的模块参数都是输入，不是假设：

```agda
(f : ℕ → Ordᴵ) (s : ∀ n → f n ⊑ᴵ f (suc n))
(dec : ∀ n → (f n ≅ᴵ f (suc n)) ⊎ (f n ≺ᴵ f (suc n)))
(t Y : ℕ → Ordᴵ) (P : ∀ n → PEmb (f n) (Y n))
(t0 : Y 0 ≅ᴵ t 0) (tY : ∀ n → (t n ⊕ Y (suc n)) ≅ᴵ t (suc n))
(tB : ∀ n → t n ⊑ᴵ B)
```

**YiPEKey**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `ψ⁰-≺` | `∀ {x y : L.Ordᶜ L.zero} → x L.≺ y → L.ψ⁰ x L.≺ L.ψ⁰ y` | 第 0 层的 ψ⁰ 结构严格单调 | 编译定理 |
| `ψ⁰Ω-≺` | `∀ {a b} → a ≺ᴵ b → L.ψ⁰ (L.Ω a) L.≺ L.ψ⁰ (L.Ω b)` | 经压平 (`flatΩ-≺`, `ψ⁰-flat`) | 编译定理 |
| `KEYat η l` | `PEmb (L⁺ (L.toLevel (read η) (HS-read η l))) (L.toLevel (read (F η l)) (HS-read (F η l) (F-lgl η l)))` | 定义 | — |
| `key-zero`, `key-top`, `key-suc₀` | `KEYat G.zero tt`；`KEYat G.top tt`；`KEYat (G.suc G.zero) tt` | 层号 0 与 1 | 编译定理 |
| `KeyLim.key-lim` | `KEYat (G.lim f) (st , lf)`，参数 `ss : ∀ n → (f n ≡ f (suc n)) ⊎ (read (f n) L.≺ read (f (suc n)))` 与 `kf : ∀ n → KEYat (f n) (lf n)` | 极限层号归到各支 | 编译定理 (参数是输入) |
| `key-spine` | `KEYsuc → ∀ {η l} → Spine η l → KEYat η l` | 沿极限脊柱归纳 | 条件定理 |
| `key-from` | `KEYsuc → SpineT → KEY` | | 条件定理 |
| `btbo-FS`, `btbo-FS⁺` | `FUNC → KEYsuc → SpineT → D.BTBOᴵ ≼ read T₃`；`… ≼ NA.read NT.T⁺` | | 条件定理 |
| `spine₀` | `Spine (co (pts 0)) (lw (pts 0))` | m = 0 | 编译定理 |
| `tri→KEYsuc` | `Tri → KEYsuc` | | 编译定理 |

剩下的两个前提：

```agda
KEYsuc = ∀ a (l : Lgl zero a) → KEYat (G.suc a) l
SpineT = ∀ m → Spine (co (pts m)) (lw (pts m))
```

- `Spine η l` 的意思：从根沿极限各支往下，直到后继、零或 `top`；每个极限的相邻两支要么 `≡`，要么读回严格上升。

**前提的可满足性：**
- `FUNC`：
  - 在 `Tri` 下成立 (`tri→FUNC`)，所以经典模型里成立。
  - 结构可比的输入上，结论是定理 (`func-⊑`)。
  - 没有无条件的非平凡实例。
- `KEY`：m = 0 是定理 (`key₀`)；在 `Tri` 下成立。
- `KEYsuc`：a = 0 是定理 (`key-suc₀`)；在 `Tri` 下成立。
- `SpineT`：
  - m = 0 是定理。
  - m ≥ 1 是判断：成立，理由是链点都由累加和与折叠造出，极限的相邻两项读回严格上升。
  - m = 1 只涉及第 0 层，估计约 100 行可证。m ≥ 2 要第 1 层以上折叠的严格单调。都没有证。

##### 4 办法

- **n = 1：** `chainP₁` (`D.γ 1 ≼ᵖ read (co (pts 1))`) 经 `embᵖ` 得嵌入。这里的一致性来自第 0 层的精确值 (`XEmb-limˡ`)，不是一般的值单调。
- **平移：**
  - `⊕` 定义在 `Ordᴵ` 上：左加，与 `⊕-⊑`/`⊕-≅`/`⊕-<`/`⊑⊕` 互递归，和 `toLevel` 同样的写法，停机检查直接通过。
  - 平移嵌入是全局映射 c ↦ x ⊕ c，所以一致性自动成立。
  - 接到链点用 `toLevel-+` 与 `chain-cum`。
- **一步的约化：** `D.L (n+1)` 定义性地就是 `L⁺ (D.L n)`。所以一步 = `FUNC` (参照) ∘ `KEY` (同一层号) ∘ `shift-κ`。
- **阶梯里的一致性从哪里来：**
  - 逐块造 `Q (n+1) = glue (Q n) (P (n+1)) …`。
  - 分界用 `f (n+1)` 前驱上的有界三歧 `<ᴵ-dec`：在 `f n` 之下的前驱用旧嵌入；其余（含 `f n` 本身）映到 `t n ⊕ P c`。
  - 所以后一块按构造延拓前一块 (`glue-ext`)，任意两块的一致由 `cmpℕ`/`far` 归纳给出，再喂 `PEmb-limˡ`。
- **放下的写法：** 起初让分界元映到 `t n`。这要 `zero ≺ᴵ Y`，而它对退化极限不成立：`zero ⊀ suc (lim (λ _ → zero))`。改成映到 `t n ⊕ P a` 就不需要它了。这一版没有编译过就重写了。
- **用到主线上：** 极限坐标上 `F (lim f)` 定义性地是 `lim (psum zero (λ n → F (f n) _))`，按块累加，正好是阶梯的目标。
  - 源的第 n 项是 ψ⁰(Ω_{κf n})。
  - 源的每一步由 `ss`、`ψ⁰Ω-≺` 与 `toLevel-≺` 给出：相等给 `≅ᴵ`，严格给 `≺ᴵ`。

##### 5 第一个障碍

没有检查器报错，缺的是引理本身。都是 n = 1 → 2 那一步：

1. **`FUNC` 的第一个实例：** `PEmb (L⁺ (D.L 1)) (L⁺ (κ 1))`，即从 `emb₁ⁿ` 得到。判断：
   - 后继情形：比较层号 a′ 与 b′ 上的两条塌缩链，而 a′、b′ 之间只有嵌入，没有结构对应。这是 YiMono 的 `Crux` 的结构版，等于 `BTBOFullLe` 的 LeE 换成结构结论。
   - 极限情形：目标 ψ⁰(Ω_b) 不是累加的，阶梯不适用，`PEmb-limˡ` 要的一致性只能来自构造的自然性。
2. **`KEYsuc` 的第一个需要的实例：** `KEYat (G.suc G.top) tt`，即层号 2。
   - 它在 η₁ 的脊柱上：η₁[0][0] = top + top = `G.suc G.top`。
   - 内容：ψ₀(Ω₂) = lim ψ⁰(γₖ)（γ 在第 1 层），对主线 `F (suc top)` = lim Ψ⁰(cₖ)（cₖ 在第 1 层累加）。
   - 判断：用 `≼ᵖ` 走，需要第 1 层上的 `≼ˣ` 精确性，也就是 YiChain 的 `P2 1` 那一处。YiOver 的 `over₂` 只给值，不给 `≼ˣ`。
3. **`SpineT` 在 m = 1：** `Spine (co (pts 1)) (lw (pts 1))`。缺的是主线第 0 层折叠对加法的严格单调：read (Ψ⁰ c) ≺ read (Ψ⁰ (c + d))。

**是不是在要求判定什么：**
- 阶梯需要源的每一步判定：`(f n ≡ f (suc n)) ⊎ (read (f n) L.≺ read (f (suc n)))`。
- 合法性 `Cp` 只给 `≡` 或字面下降。只经过极限分支的下降只给 `⊑`，不给 `≺`。
- 判断：对一切合法树作这个判定推出 LPO。反例：`f 0 = zero`，`f 1 = lim g`，其中 g k 在二进制序列出现第一个 1 之前取 `zero`，之后取 `suc zero`，这是合法的。
- 所以这一条作为对具体链点的命题 `SpineT` 出现，不作为对一切合法树的引理。
- `FUNC` 与 `KEYsuc` 没有发现要判定的东西。也没有编译的否定，只能写 "未走通"。

##### 6 偏离与事故

- **改动范围：** 只新建了上面四个文件。没改已有文件，没碰 `src/`、`archive/`，没有提交。
- **导入：** 没有依赖 `YiLow*`。导入了已定稿的：
  - `YiChainOne` (`chainP₁`, `cc`, `Gc`, `module Phi`)；
  - `YiZeroAccP.ψ⁰ˣ`；`YiChainBase.transˣ`；
  - `YiChainFlat`, `YiFlatWit`, `YiFlatChain`；
  - `YiVmConExact`, `YiMonoEmb`, `BTBOFullEmb`, `BTBOFullLe.⊑≅`；
  - `YiNextValFin.T₃≅`, `YiNextAcc.T₃≼T⁺`。
- **编译中途的错误（都是我自己的，各改一次）：**
  - `PHI` 不是 `YiChainOne` 的顶层导出，改为 `module Phi`；
  - `HS-≅` 有两个不可达子句，已删；
  - `YiPEKey` 里误写 `Stair.⊕`，改为导入 `_⊕_`。
- 对自己的文件用过几次 `sed` 做小改，改后都重编过。
- **接口：** 只按字面路径删过自己四个模块的 `.agdai`。没有用 `--ignore-interfaces`。
- **试验：** 没有写临时的 `.agda`，形状靠读定义与 `refl` 的类型检查确认。
- **日志：** `<实验目录>/agents/pe/cold-*.log`

文件（按依赖序冷编）：
- <仓库>/probes/OCF/Lean/YiPEBase.lagda.md
- <仓库>/probes/OCF/Lean/YiPEStep.lagda.md
- <仓库>/probes/OCF/Lean/YiPEStair.lagda.md
- <仓库>/probes/OCF/Lean/YiPEKey.lagda.md
