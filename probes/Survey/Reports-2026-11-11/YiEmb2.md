# 两个方向的嵌入给出的折叠单调 (YiEmb2)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-11 11:26 至 11:38 |
| 工具调用 / agda 编译 (粗数) | 30 / 5 |
| token (usage 字段，按消息去重) | 输出 75045；新写入缓存的输入 230400；读缓存的输入 4195298；其余输入 54 |
| 写过的仓库文件 | `YiEmb2.lagda.md`, `YiEmb2Le.lagda.md` |
| 文件前缀 | `YiEmb2` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 两向嵌入一路返回并复核; 与 BTBO 持平只剩 P2₂ (主审)” 一节 |
| 主审复核后的一句结论 | 参照框架一侧的加强无条件解决；与 BTBO 持平只剩主线一侧的一条两向陈述；两件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 任务是 **参照框架 (Level 族) 上的一条引理: 两个方向的保值嵌入给出定义域版的折叠单调**, 用它把 "与 BTBO 持平" 缺的两条加强之一 (`P1`) 往前推. 这条只谈参照框架, 与被验收的树无关. 另有两路同时在做另外两条引理 (前缀 `YiUB`, `YiFlat`), 互不依赖. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 Agda 一节 (选项, 文字预算, 退出码, 堆; 函数外延只准作前提), "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 与 §5.4.
3. **回报原文, 全读**: `probes/Survey/Reports-2026-11-11/YiChain.md` (§5: `P1 1` 要什么), `YiVmCon.md` (保值嵌入 `XEmb` 与定义域 `≼ˣ`, `≼ᵖ` 的来历), `YiVmNeg.md` (哪些写法推出全知原则: 保初始段的嵌入, 不读推导的写法).
4. 代码 (都已定稿, 可以导入, 不许编辑):
   - `probes/OCF/Align/YiVmConExact.lagda.md`: 记录 `XEmb a b` (字段 `P : PEmb a b`, `ex`, `ex′`: 每个前驱的像与它值相等); `XEmb-⊑`, `XEmb-∘`, `XEmb-limˡ`, `XEmb-limʳ`, `XEmb-suc`, `XEmb-sucʳ`; `≈→≅`; `_≼ˣ_` (`zˣ`, `sˣ : a ≼ˣ b → b ≼ a → L.suc a ≼ˣ L.suc b`, `wˣ`, `≼lˣ`, `lˣ`), `_≼ᵖ_`; `embˣ : ∀ x hx y hy → x ≼ˣ y → XEmb (toLevel x hx) (toLevel y hy)`; `embᵖ`, `VMᵖ` (结论是值序 `≼`, 不是 `≼ˣ`).
   - `probes/OCF/Align/BTBOFullEmb.lagda.md` (`PEmb`, `Ψ-emb : PEmb a b → ψ⁰ (Ω a) ≼ ψ⁰ (Ω b)` 与它的证法 `PE.Ψ-emb′`), `probes/OCF/Align/BTBOFullLe.lagda.md` (模块 `LeE`: 对一般的嵌入关系 E 的折叠单调 `Le-ψ`, 及 `clashᴸ₄` 用的 `eq-pres`; 执行方建议照它改写).
   - `probes/OCF/Lean/YiChainBase.lagda.md` (`transˣ`), `probes/OCF/Lean/YiZeroAccP.lagda.md` (`ψ⁰ˣ : a ≼ˣ b → L.ψ⁰ a ≼ˣ L.ψ⁰ b`, `+ˣ`; 只导入这两条), `probes/OCF/Lean/YiChainCond.lagda.md` (`P1`, `P2`, `chain-cond`), `YiChainBack.lagda.md` (`γ₁≈`: 第 1 步两个方向都在 `≼ˣ` 里).
   - 参照: `OCF.Align.Level` (`Ordᶜ`, `Ordᴵ`, `ψ`, `ψ⁰`, `Ω`, `toLevel`, `HS`, `_⊑ᴵ_`, `_≅ᴵ_`, `Ψ⁰-mono`), `OCF.Align.Value`, `OCF.Align.YiBtValBT` 的 `module D`.
   查签名用检索, 大文件不要整篇读.

#### 1 问题是什么

`P1` (在 `YiChainCond`) 逐字:
```agda
P1 = ∀ n → D.γ n ≼ˣ read (co (pts n)) → L.ψ⁰ (L.Ω (D.L n)) ≼ˣ L.ψ⁰ (L.Ω (κ n))
```
其中 `D.L n = toLevel (D.γ n) …`, `κ n = toLevel (read (co (pts n))) …`. 它只谈参照框架: 两个带证书的第 0 层树 x, y 落在 `≼ˣ` 里, 推出它们层号上的 ψ⁰ (Ω ·) 也落在 `≼ˣ` 里. 现有的 `VMᵖ` 只给值序 `≼`. 要 `≼ˣ`, 结论里每个 "后继对后继" 都要顶的值相等, 执行方判断这要反向的值单调, 所以合适的形式大概要两个方向的嵌入.

#### 2 要交的, 分步; 每做成一步先交

1. **定义域版的折叠单调.** 下面两种之一 (或你找到的更合适的形式, 说明理由):
   ```agda
   VMˣ₂ : ∀ {a b} → XEmb a b → XEmb b a → L.ψ⁰ (L.Ω a) ≼ˣ L.ψ⁰ (L.Ω b)
   VMˣ  : ∀ x hx y hy → x ≼ˣ y → y ≼ˣ x → L.ψ⁰ (L.Ω (L.toLevel x hx)) ≼ˣ L.ψ⁰ (L.Ω (L.toLevel y hy))
   ```
   办法: 照 `BTBOFullLe` 的 `LeE.Le-ψ` (对一般的嵌入关系的折叠单调) 改写, 结论从 `≼` 换成 `≼ˣ`, 在需要顶值相等的地方用另一个方向的嵌入给反向的值不等式.
2. **最小的实例.** n = 1: 由 `γ₁≈` 得 `L.ψ⁰ (L.Ω (D.L 1)) ≼ˣ L.ψ⁰ (L.Ω (κ 1))` (这就是 `P1 1` 的结论).
3. **`P1` 的一般形式.** 若你的引理要两个方向的前提, 给出 `P1` 的两向版本 `P1₂ = ∀ n → D.γ n ≼ˣ read (co (pts n)) → read (co (pts n)) ≼ˣ D.γ n → (两个方向的结论)`, 并说明 `chain-cond` 的不变量要相应地带两个方向 (另一路 `YiUB` 在做 `P2`, 已被要求尽量交两个方向). 能写一条 "两向版的 `chain-cond`" 的条件定理就写.

**已知的边界 (不要撞上).** 对一切值序推导造 "按值对齐" 的嵌入推出 LPO (`YiVmConLPO.tri→LPO`, `YiVmNegSeg.embVᴰ→LPO`); 不读推导的写法推出 Markov 原则 (`YiVmNegIrr`). 你的引理以 `XEmb` 或 `≼ˣ` 的推导为前提, 是带数据的, 不在这些否定的范围里; 若你发现某一步要判定什么, 把那一步的类型写进回报.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理); 堆到 6G 仍耗尽 (先按手册 §4.2). 做不成的部分写成带确切类型的模块参数. 没有编译的否定定理时只能写 "未走通".

#### 3 过程要求

- 读完上面的文件后尽快动手: 第一个文件 (哪怕只是零与后继两种情形) 在 20 分钟内写出并编译.
- 每写完一个文件就编译; 每次回复都要有工具调用, 不要在一次回复里只思考.

#### 4 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiEmb2` (模块名 `OCF.Lean.YiEmb2…`). 都是验收文件, 文首标 "验收文件"; 允许导入带记号闭包的 `OCF.Align.Value`, `OCF.Align.Level` 与旧验收文件. 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`. 同时在跑的另两路用前缀 `YiUB`, `YiFlat` (都在 `probes/OCF/Lean/`), 不要动也不要依赖它们的文件.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/emb2`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 5 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步; 一段话说对纲领与目标意味着什么 (定义域版的折叠单调是无条件的定理了没有; `P1` 做到哪个 n; 要不要两个方向).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型与它的可满足性.
4. 办法: 照 `BTBOFullLe` 改了哪些地方; 哪里用到另一个方向.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型; 它是不是在要求判定什么.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### YiEmb2 一路回报：两个方向的保值嵌入给出定义域版的折叠单调

##### 1 判决

三步都做成了。

**对纲领与目标的意思：**
- 定义域版的折叠单调 `VMˣ₂` / `VMˣ` 是无条件的编译定理。它要两个方向的前提 (`XEmb a b` 与 `XEmb b a`，或者 `x ≼ˣ y` 与 `y ≼ˣ x`)。
- **`P1`：**
  - 它的两向版 `p1₂ : P1₂` 对一切 n 都是无条件定理。
  - `P1 1` 是定理 (`p1₁`；结论 `p1-one`)。
  - 另有 `P2₂→P1 : P2₂ → P1`，所以原来 `chain-cond` 的两个前提可以收成一个 `P2₂`。
- **"与 BTBO 持平" 现在只差主线一侧：**
  - 条件定理是 `btbo-cond₂ : P2₂ → D.BTBOᴵ ≼ read T₃`。
  - `P2₂ 0` 是定理 (`p2₂-0`)。
  - `P2₂ n` (n ≥ 1) 未证。它是主线一侧的事，有两个方向：`T₃-own` 加上链的一步落在 `≼ˣ` 里，以及反向的吸收或上界 (`YiUB` 那一路)。
- **要不要两个方向：** 这个证法要。只有一个方向时 (`x ≼ˣ y`)，结论是否成立：未证，也没有否定。见 §5 的判断。
- **记号：** 没有借用记号。没有新的树强度定理，`T₃` 的 ψ₀(Ω_Ω) 仍是读法。

##### 2 文件表

两个文件都在 `probes/OCF/Lean/`，都是验收文件。冷编译前只删了自己两个模块的 `.agdai`，堆上限 6G，每份日志只有本模块一行 `Checking`。

| 文件 | 总行 / 代码行 | 冷编译退出码 | 常驻峰值 | 用时 |
|---|---|---|---|---|
| `YiEmb2Le.lagda.md` | 339 / 293 | 0 | 1.87G | 10.6s |
| `YiEmb2.lagda.md` | 135 / 97 | 0 | 1.49G | 7.9s |

- **选项行：** 都是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。
- **检索：** `postulate`、洞、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`irrelevant-projections`、`--cubical`、`Funext`、本机路径，都是 0 处。
- **导入：** 从 `YiZeroAccP` 只导入了 `+ˣ`。没有依赖 `YiUB*`、`YiFlat*`。

##### 3 定理表

`L` = `OCF.Align.Level`；`YiEmb2Le` 里的名字在模块 `Two` / `Two.WithLaws` 内。

| 名字 | 逐字的陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `one≼ˣ` | `∀ {k} (y : Ordᶜ k) → suc zero ≼ˣ ψ⁰ y` | 1 在定义域里不高于任何一层的 ψ⁰ | Le | 编译 |
| `iterˣ` | `∀ {A A′ : Ordᶜ zero} → A ≼ˣ A′ → A′ ≼ A → ∀ n → iter (A +_) zero n ≼ˣ iter (A′ +_) zero n` | ω 倍的有限部分和 | Le | 编译 |
| `Two.L-add` | `Lx a a′ → B.Le a′ a → Lx b b′ → Lx (add a σ b) (add a′ σ′ b′)` | 带反向推导的加法 | Le | 编译 |
| `Two.WithLaws.Le-ψ` | `(ei : E i i′) (p : i <ᴵ ℓ) (σ : Simᴵ k₁ ℓ) (p′ : i′ <ᴵ ℓ′) (σ′ : Simᴵ k ℓ′) → Lx x y → Lx (ψ p σ x) (ψ p′ σ′ y)` | 关系 `Lx` 对折叠封闭 | Le | 编译 (对模块参数) |
| `Two.WithLaws.Le-ψ⁰ˣ` | `∀ {k₁ k} {x : Ordᶜ k₁} {y : Ordᶜ k} → Lx x y → ψ⁰ x ≼ˣ ψ⁰ y` | `Lx` 推出定义域 `≼ˣ` | Le | 编译 (对模块参数) |
| `Two.WithLaws.Ψ⁰ˣ` | `∀ {a a′} → E a a′ → ψ⁰ (Ω a) ≼ˣ ψ⁰ (Ω a′)` | 一般的 E 上的结论 | Le | 编译 (对模块参数) |
| `Inst.flip` | `∀ {i i′} → PX.E i i′ → PY.E i′ i` | 两个保值嵌入使嵌入关系可以翻转 | YiEmb2 | 编译 |
| `VMˣ₂` | `∀ {a b} → XEmb a b → XEmb b a → L.ψ⁰ (L.Ω a) ≼ˣ L.ψ⁰ (L.Ω b)` | 第 1 步要的引理 | YiEmb2 | 编译 |
| `VMˣ` | `∀ x (hx : HS x) y (hy : HS y) → x ≼ˣ y → y ≼ˣ x → L.ψ⁰ (L.Ω (toLevel x hx)) ≼ˣ L.ψ⁰ (L.Ω (toLevel y hy))` | 同上，前提是 `≼ˣ` 推导 (经 `embˣ`) | YiEmb2 | 编译 |
| `p1₂` | `P1₂`，其中 `P1₂ = ∀ n → D.γ n ≼ˣ read (co (pts n)) → read (co (pts n)) ≼ˣ D.γ n → (L.ψ⁰ (L.Ω (D.L n)) ≼ˣ L.ψ⁰ (L.Ω (κ n))) × (L.ψ⁰ (L.Ω (κ n)) ≼ˣ L.ψ⁰ (L.Ω (D.L n)))` | `P1` 的两向版，对一切 n | YiEmb2 | 编译 |
| `p1-one` | `L.ψ⁰ (L.Ω (D.L 1)) ≼ˣ L.ψ⁰ (L.Ω (κ 1))` | `P1 1` 的结论 (由 `γ₁≈`) | YiEmb2 | 编译 |
| `p1₁` | `D.γ 1 ≼ˣ read (co (pts 1)) → L.ψ⁰ (L.Ω (D.L 1)) ≼ˣ L.ψ⁰ (L.Ω (κ 1))` | 就是 `P1 1` | YiEmb2 | 编译 |
| `p2₂-0` | `(L.ψ⁰ (L.Ω (κ 0)) ≼ˣ read (co (pts 1))) × (read (co (pts 1)) ≼ˣ L.ψ⁰ (L.Ω (κ 0)))` | `P2₂ 0` (`p2₀` 与 `back₁`) | YiEmb2 | 编译 |
| `γ₂≈κ₁` | `(D.γ 2 ≼ˣ L.ψ⁰ (L.Ω (κ 1))) × (L.ψ⁰ (L.Ω (κ 1)) ≼ˣ D.γ 2)` | 参照第 2 项与主线中间点两个方向 | YiEmb2 | 编译 |
| `chain-cond₂` | `P2₂ → ∀ n → (D.γ n ≼ˣ read (co (pts n))) × (read (co (pts n)) ≼ˣ D.γ n)` | 两向版的 `chain-cond` | YiEmb2 | 条件 |
| `P2₂→P1` / `P2₂→P2` | `P2₂ → P1` / `P2₂ → P2` | 原来的两个前提都由 `P2₂` 推出 | YiEmb2 | 条件 |
| `btbo-cond₂` | `P2₂ → D.BTBOᴵ ≼ read T₃` | BTBO 下界只剩 `P2₂` | YiEmb2 | 条件 |
| `γ₂-cond` | `(L.ψ⁰ (L.Ω (κ 1)) ≼ˣ read (co (pts 2))) × (read (co (pts 2)) ≼ˣ L.ψ⁰ (L.Ω (κ 1))) → (D.γ 2 ≼ˣ read (co (pts 2))) × (read (co (pts 2)) ≼ˣ D.γ 2)` | n = 2 只缺 `P2₂ 1` | YiEmb2 | 条件 |

**`YiEmb2Le` 的模块参数：** E、E′ 与各自的 `resp`；E 的 `lt-pres`、`eq-pres`；`ℒ′ : B.Laws`；`flip`；`Ωlaw : E a a′ → Lx (Ω a) (Ω a′)`。在 `YiEmb2.Inst` 里全部由定理填上：`PE.lt′`、`PE.eq′`、`PE.ℒ (P Y)`、`flip`，以及照 `PE.Ω′` 写的 `Ω′`。所以 `VMˣ₂` 没有剩下的前提。

**条件定理的前提 `P2₂`：**
- 类型：`∀ n → (L.ψ⁰ (L.Ω (κ n)) ≼ˣ read (co (pts (suc n)))) × (read (co (pts (suc n))) ≼ˣ L.ψ⁰ (L.Ω (κ n)))`。
- 可满足性：n = 0 是定理 (`p2₂-0`)；n ≥ 1 未证。

##### 4 办法

**照 `BTBOFullLe.LeE` 改了哪些地方：**
- **新关系 `Lx`：** 与 `LeE.Le` 同形，取 `Allow = ⊥`，所以去掉了 `Lb`，也不需要 `L-add-l`、`Sbt`、`gen`、`one-ψ`、`S-ψ`。唯一的改动在后继对后继：`Ls : Lx₊ a b → B.Le b a → Lx₊ (suc a) (suc b)`，多带一条反向推导，其中 `B = LeE E′ resp′ ⊥` 是现成的模块。`Lii` 的假设与 `Lur` 用 `Lx` 自己的低层版本 `X<`，嵌套写法与 `L<` 相同。
- **`Le-ψ⁰ˣ`：** 与 `Le-ψ⁰` 逐支对应。只有 `Ls` 一支要 `+ˣ` 的反向值，取 `Bψ⁰ rd`。`Lz` 一支用推广到一切层的 `one≼ˣ`。其余各支是 `lˣ` / `≼lˣ`。
- **搬运八个函数：** 逐字照抄。在 `Ls` 处，右边的搬运对应 `B` 的左边搬运 (例如 `Lr-tr e (Ls d rd) = Ls (Lr-tr e d) (B.Ll-tr e rd)`)。
- **`L-add`：** 多一个左加数的反向推导 `ra`，`Ls` 处取 `B.L-add ra rd`。

**哪里用到另一个方向：**
- `Le-ψ` 的 `Ls` 支：`iter-Lx (Le-ψ … d) (Bψ (flip ei) p′ σ′ p σ rd) n`。这里要折叠后的反向推导，也就是 E′ 上的 `Le-ψ`，它要 `flip ei : E′ i′ i` 和 E′ 的 `Laws` (来自 `XEmb b a` 的 `PEmb`)。
- `flip` 的 `sub` 支要把 `i` 与 `map P′ (r′)` 认成 `≅ᴵ`：两者都是 a 的字面前驱，值相等由 `ex`/`ex′` 用了四次给出，再用 `≈→≅`，也就是有界三歧 `<ᴵ-dec` 加值序无自反。
- 没有判定值，没有用 `Tri`。

##### 5 第一个障碍

三步内没有障碍，没有检查器报错留下，没有带确切类型的模块参数留着不填。

- **BTBO 下界还缺的：** 只剩 `P2₂ n` (n ≥ 1)，类型见 §3。它不谈参照框架，是主线一侧的上界或吸收，不在本路范围。
- **一个方向够不够 (判断，没有编译)：** 反向推导只在 E 相关的两层之间的 `Ls` 处需要。E 把值相等的层配对，所以要的正是每一对配对层之间有一个反向的前驱嵌入。只有 `XEmb a b` 时，从 i′ 回到 i 的嵌入要求像覆盖初始段，而那就是 `YiVmNegSeg` 推出 LPO 的那种写法。所以单向的 `VMˣ` 若成立，要换证法。我没有试，它也不是链上需要的：链上的对本来就是两个方向。

##### 6 偏离与事故

- **编译错误：** 只有一次，是我自己的。`YiEmb2Le` 里的 `clash₁` 与 `Level.clash₁` 重名 (`ClashingDefinition`)，在自己的文件里改名为 `clashˣ₁/₂/₄` 后通过。其余一次通过。
- **简报没要求、多加的：** `P2₂→P1`、`P2₂→P2`、`γ₂≈κ₁`、`γ₂-cond`、`p2₂-0`。这些是为了说清两向不变量现在只差什么。
- **改动范围：** 没有改已有文件，没碰 `src/`、`archive/`，没有提交。
- **接口：** 只删过自己两个模块的 `.agdai`，写的是字面路径。没有在临时目录写 `.agda` 试验。
- **日志：** 用 `/usr/bin/time -l` 测了常驻内存，日志在 `<实验目录>/agents/emb2/` (`cold-YiEmb2Le.log`, `cold-YiEmb2.log`)。

主审冷编请按依赖序：
1. `<仓库>/probes/OCF/Lean/YiEmb2Le.lagda.md`
2. `<仓库>/probes/OCF/Lean/YiEmb2.lagda.md`
