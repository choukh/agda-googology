# 第 1 层以上吸收的两条结构事实 (YiFlat)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-11 11:26 至 11:50 |
| 工具调用 / agda 编译 (粗数) | 49 / 11 |
| token (usage 字段，按消息去重) | 输出 146884；新写入缓存的输入 452362；读缓存的输入 8216624；其余输入 82 |
| 写过的仓库文件 | `YiFlatAbs.lagda.md`, `YiFlatChain.lagda.md`, `YiFlatObs.lagda.md`, `YiFlatWit.lagda.md` |
| 文件前缀 | `YiFlat` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 结构事实一路返回并复核; 与 BTBO 持平只差 FoldB (主审)” 一节 |
| 主审复核后的一句结论 | 两条结构假设成了定理；第 1 层以上的吸收两个方向无条件；主线一侧的两向陈述归到主线折叠值的两向界；四件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 任务是 **参照框架 (Level 族) 上第 1 层以上吸收要的两条结构事实**: 证 `ABSΩ` 的两个假设在链上要用的那些对象上成立, 从而让第 1 层以上的吸收成为无条件的定理. 这条只谈参照框架, 与被验收的树无关. 另有两路同时在做另外两条引理 (前缀 `YiUB`, `YiEmb2`), 互不依赖. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 Agda 一节 (选项, 文字预算, 退出码, 堆; 函数外延只准作前提), "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 与 §5.4.
3. **回报原文**: `probes/Survey/Reports-2026-11-11/YiChain.md` 全读 (§4 第 0 层的吸收怎么做的; §5 第 1 层以上缺什么).
4. 代码 (都已定稿, 可以导入, 不许编辑):
   - `probes/OCF/Lean/YiChainBase.lagda.md`: 模块 `Abs` (参数 `hx : L.ψ⁰ c ≼ˣ X`, `hv : X ≼ L.ψ⁰ c`) 的 `ABS : ∀ (b : T₀) → L.HS b → c L.≺ b → L.ψ⁰ b ≼ˣ (X L.+ L.ψ⁰ b)` 与 `VABS` (对 `c L.≺ b` 的推导分 `≺z`, `≺s`, `≺l` 三种); `transˣ`; `step`.
   - `probes/OCF/Lean/YiChainFlat.lagda.md`: `flat : ∀ {k} → L.Ordᶜ k → T₀` (把任意层的参照树压成第 0 层的树: 后继, ℕ 极限逐项, `limᵢ` 按它的链展开成 ℕ 极限, `up` 透明), `ψ⁰-flat : ∀ {k} (s : L.Ordᶜ k) → L.ψ⁰ s L.≅ L.ψ⁰ (flat s)`, 以及
     ```agda
     ABSΩ : ∀ {X c : T₀} → L.ψ⁰ c ≼ˣ X → X ≼ L.ψ⁰ c → ∀ {k} (s : L.Ordᶜ k) → L.HS (flat s) → c L.≺ flat s →
       L.ψ⁰ s ≼ˣ (X L.+ L.ψ⁰ s)
     ```
     两个假设: `L.HS (flat s)` (压平后的树带证书: 极限处相邻两项结构步进) 与 `c L.≺ flat s` (压平后的树上的一个结构前驱见证).
   - 参照: `OCF.Align.Level` (`Ordᶜ`, `ψ`, `ψ⁰`, `Ω`, `limᵢ`, `HS` (`hz`, `hs`, `hl`), `_⊑⁰_`, `_⊑_`, `_≺_` 与它的构造子, `toLevel`, `toLevel-⊑`, `Ψ⁰-mono`, `iter`), `OCF.Align.Uniform` (`Uniform : ∀ a → HS (ψ⁰ (Ω a))`: 参照的 ψ⁰ (Ω a) 带证书; 看它怎么证的, 执行方判断你要的是同一类结构单调的理论), `OCF.Align.Diagonal`, `OCF.Align.YiBtValBT` 的 `module D`; 主线一侧只需要知道链上出现的 s 是什么: `probes/OCF/Lean/YiLeanValFin.lagda.md` (`κ n = L.toLevel (read (co (pts n))) …`), `YiChainCond.lagda.md` (`P2 n : L.ψ⁰ (L.Ω (κ n)) ≼ˣ read (co (pts (suc n)))`).
   查签名用检索, 大文件不要整篇读.

#### 1 要交的, 分步; 每做成一步先交

1. **压平保持证书.** `L.HS (flat s)` 对哪些 s 成立: 至少对 `s = L.Ω ℓ` (ℓ 任意的层号, 或 ℓ = toLevel x h), 以及它们的 ψ 一类的输出; 能对一切 "规范" 的 s (由 Ω, ψ, 加法, 极限构成的参照树) 一般地证最好. 照 `Uniform` 的证法. 注意 `HS` 只要求相邻两项 `⊑⁰` (不严格).
2. **结构前驱见证.** 对 `s = L.Ω (κ n)` 一类 (链上 `P2` 要的), 给出合适的 c 与 `c L.≺ flat s`, 并使 `L.ψ⁰ c` 与左加数 X 值相等 (X 是链点 `read (co (pts n))`; 两个不等式 `L.ψ⁰ c ≼ˣ X`, `X ≼ L.ψ⁰ c` 不是你的任务, 但请写明你选的 c 让这两条变成什么陈述, 供另两路接). 先 n = 1 (κ 1 是极限层号).
3. **无条件的第 1 层以上的吸收.** 把 1, 2 接进 `ABSΩ`, 得到对链上那些 s 无条件的 `L.ψ⁰ s ≼ˣ (X L.+ L.ψ⁰ s)` (以 X 的两个值不等式为前提的那种条件定理也算, 写清前提).
4. **反向.** 若顺手, 给出反向 `(X L.+ L.ψ⁰ s) ≼ˣ L.ψ⁰ s` 的同类版本 (第 0 层的反向在 `YiChainBack` 的 `AbsR`).

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理); 堆到 6G 仍耗尽 (先按手册 §4.2). 做不成的部分写成带确切类型的模块参数. 若发现某条事实不成立 (例如压平后某个极限的相邻两项不步进), 写成编译的否定交回, 说明它对哪种 s.

#### 2 过程要求

- 读完上面的文件后尽快动手: 第一个文件 (哪怕只是 `flat (L.Ω ℓ)` 在有限 ℓ 上的证书) 在 20 分钟内写出并编译.
- 每写完一个文件就编译; 每次回复都要有工具调用, 不要在一次回复里只思考.

#### 3 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiFlat` (模块名 `OCF.Lean.YiFlat…`). 都是验收文件, 文首标 "验收文件"; 允许导入带记号闭包的 `OCF.Align.Value`, `OCF.Align.Level` 与旧验收文件. 中文 literate Agda (`.lagda.md`). 不改任何已有文件 (含 `YiChainFlat`), 不碰 `src/`, `archive/`. 同时在跑的另两路用前缀 `YiUB`, `YiEmb2` (都在 `probes/OCF/Lean/`), 不要动也不要依赖它们的文件.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/flat`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步; 一段话说对纲领与目标意味着什么 (第 1 层以上的吸收是无条件的定理了没有, 对哪些 s).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型与它的可满足性.
4. 办法: 压平的证书怎么证的; 见证 c 怎么取的, 它让 X 的两个值不等式变成什么.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 中途消息（主审发给这一路）

转录时间戳 2026-11-11 11:39 (UTC)：

主审通知 (你的任务不变, 只把第 4 步从 "顺手" 改成必交): 两向嵌入那一路 (`YiEmb2`) 已返回并经主审冷编复核, 参照框架一侧的 `P1` 已无条件解决 (`OCF.Lean.YiEmb2` 的 `VMˣ`, `p1₂`; 定稿, 你可以导入, 但你的任务用不到它). "与 BTBO 持平" 现在只剩主线一侧的一条两向陈述:
```agda
P2₂ = ∀ n → (L.ψ⁰ (L.Ω (κ n)) ≼ˣ read (co (pts (suc n)))) × (read (co (pts (suc n))) ≼ˣ L.ψ⁰ (L.Ω (κ n)))
```
(在 `OCF.Lean.YiEmb2`; `btbo-cond₂ : P2₂ → D.BTBOᴵ ≼ read T₃`). 链点 `co (pts (suc n))` 是 `co (pts n) + obs (pts n)`, 所以两个方向都要吸收: 正向 `L.ψ⁰ s ≼ˣ (X L.+ L.ψ⁰ s)` (`ABSΩ`), 反向 `(X L.+ L.ψ⁰ s) ≼ˣ L.ψ⁰ s` (第 0 层的反向是 `YiChainBack` 的 `AbsR`). 请两个方向都交, 先 n = 1 (s = `L.Ω (κ 1)`, X = `read (co (pts 1))`). 另一路 `YiUB` 在做主线折叠的上界并会以你的两条结构事实为前提; 你的结论写成它能直接接上的形状 (对链上的 s 与 X, 以 X 与 `L.ψ⁰ c` 的两个值不等式为前提也可以, 写清 c).

## 回报原文

#### 1 判决

四步都做完了，第 4 步按中途通知交了两个方向。

**对纲领与目标的意思。** 这一路只碰参照框架，没有改树、折叠或合法性的定义。
- `ABSΩ` 原先挂着两个结构假设，现在都是无条件的编译定理：
  - 证书 `HS (flat (Ω ℓ))` 对一切层号 ℓ 成立；更一般地，对一切好树 s (Good s，且 s ≅ s) 都有 `HS (flat s)`。
  - 见证 `flat (Ω a) ≺ flat (Ω b)` 对一切 `a ≺ᴵ b` 成立。
- 所以第 1 层以上的吸收，两个方向都成了编译定理 (`absΩ`, `absΩR`)，对任意 `a ≺ᴵ b` 与任意第 0 层的 X 都成立。剩下的前提只有 X 与 ψ⁰(Ω_a) 的两向值比较 (一向 `≼ˣ`，一向 `≼`)。
- **链上：**
  - n = 0 无前提 (`absorb₁`)：s = Ω(κ 1)，X 取第 1 个链点，正向和反向都成立。
  - 一般的 n 是条件定理 (`absorb n`)，前提恰好是 `YiEmb2.P2₂` 的第 n 项。
  - 见证需要的 `κ n ≺ᴵ κ (suc n)` 对一切 n 无条件成立 (`κ≺`)。
- **顺带的归约：** `P2₂` 归约到主线折叠值的两向界 `FoldB m` (m ≥ 1)，见 `p2-from-fold`。`FoldB` 我没有证。

#### 2 文件表

四个文件都在 `probes/OCF/Lean/`，都是验收文件，选项行都是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。冷编译前只删了本模块的 `.agdai`，每份日志只有本模块一行 `Checking`，堆上限 6G。

| 文件 | 总行 / 代码行 | 冷编译退出码 | 常驻峰值 |
|---|---|---|---|
| `YiFlatObs.lagda.md` | 443 / 355 | 0 | 2.00G |
| `YiFlatWit.lagda.md` | 135 / 93 | 0 | 1.44G |
| `YiFlatAbs.lagda.md` | 46 / 23 | 0 | 1.44G |
| `YiFlatChain.lagda.md` | 97 / 62 | 0 | 1.46G |

- **检索：** `postulate`、洞、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`irrelevant-projections`、`Funext`、本机路径，四个文件都是 0 处。
- **主审冷编按依赖序：** Obs → Wit → Abs → Chain。

#### 3 定理表

记号：`L` = `OCF.Align.Level`，`T₀ = L.Ordᶜ L.zero`。在 Obs 和 Wit 里 Level 是不加限定打开的。

**`YiFlatObs` (都是编译定理)**

| 名字 | 逐字的陈述 | 白话 |
|---|---|---|
| `flat-≅` | `∀ {k₁ k₂} {a : Ordᶜ k₁} {b : Ordᶜ k₂} → a ≅ b → flat a ≅ flat b` | 压平尊重 ≅ |
| `HS-flat` | `∀ {k} {x : Ordᶜ k} → Good x → x ≅ x → HS (flat x)` | 好树压平后带证书 |
| `HS-flatΩ` | `∀ ℓ → HS (flat (Ω ℓ))` | 第 1 步的主要实例 |
| `HS-flatψ` | `∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordᶜ k} → Good x → x ≅ x → HS (flat (ψ p σ x))` | ψ 的输出压平后带证书 |
| `flat-mono` | `∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → x ⊑ᵒ y → flat x ⊑ flat y` | 压平保持观测前序 |
| `flatΩ-mono` | `∀ {a b} → a ⊑ᴵ b → flat (Ω a) ⊑ flat (Ω b)` | 压平后 Ω 单调 |

`Good`、`Good-Ω`、`Good-ψ`、`Good-ψ⁰`、`Good-add` 是本文件自己的版本，用加了 `flo` 的观测前序 `⊑ᵒ` 定义，不是 Uniform 的那一个。

**`YiFlatWit` (都是编译定理)**

| 名字 | 逐字的陈述 | 白话 |
|---|---|---|
| `flatΩ-suc` | `∀ a → flat (Ω a) ≺ flat (Ω (suc a))` | 基本一步 |
| `flatΩ-≺` | `∀ {a b} → a ≺ᴵ b → flat (Ω a) ≺ flat (Ω b)` | 第 2 步：层号的结构前驱给出压平后的结构前驱 |
| `ψW` | `∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordᶜ k} → W0 x → flat (Ω i) ≺ flat (ψ p σ x)` | ψ_i 在非零输入上严格高于 Ω_i |
| `addW` | `∀ {k ℓ} {a : Ordᶜ ℓ} {σ : Simᴵ k ℓ} {y : Ordᶜ k} → W0 y → flat a ≺ flat (add a σ y)` | 加一棵带 0 前驱的树是严格上升 |
| `W0Ω`, `W0-≅` | `∀ i → W0 (Ω i)`；`W0 x → x ≅ y → W0 y` | 辅助 |

**`YiFlatAbs` (都是编译定理)**

| 名字 | 逐字的陈述 | 白话 |
|---|---|---|
| `ABSΩR` | `∀ {X c : T₀} → X ≼ˣ L.ψ⁰ c → L.ψ⁰ c ≼ X → ∀ {k} (s : L.Ordᶜ k) → L.HS (flat s) → c L.≺ flat s → (X L.+ L.ψ⁰ s) ≼ˣ L.ψ⁰ s` | `ABSΩ` 的反向 |
| `absΩ` | `∀ {a b} → a L.≺ᴵ b → ∀ {X : T₀} → L.ψ⁰ (L.Ω a) ≼ˣ X → X ≼ L.ψ⁰ (L.Ω a) → L.ψ⁰ (L.Ω b) ≼ˣ (X L.+ L.ψ⁰ (L.Ω b))` | 第 1 层以上的正向吸收 |
| `absΩR` | `∀ {a b} → a L.≺ᴵ b → ∀ {X : T₀} → X ≼ˣ L.ψ⁰ (L.Ω a) → L.ψ⁰ (L.Ω a) ≼ X → (X L.+ L.ψ⁰ (L.Ω b)) ≼ˣ L.ψ⁰ (L.Ω b)` | 第 1 层以上的反向吸收 |

**`YiFlatChain`**

| 名字 | 逐字的陈述 | 白话 | 档 |
|---|---|---|---|
| `Z-top` | `∀ {k} (V : Lv k) (x : Ext zero k) → L.𝟎 {L.zero} L.≺ read (Ψ zero V x G.top)` | 主线折叠在 `top` 处的值有 0 这个结构前驱 | 编译 |
| `X≺` | `∀ n → read (co (pts n)) L.≺ read (co (pts (suc n)))` | 链点在结构上严格上升 | 编译 |
| `κ≺` | `∀ n → κ n L.≺ᴵ κ (suc n)` | 链点的层号严格上升 | 编译 |
| `absorb` | `∀ n → (L.ψ⁰ (L.Ω (κ n)) ≼ˣ read (co (pts (suc n)))) × (read (co (pts (suc n))) ≼ˣ L.ψ⁰ (L.Ω (κ n))) → (L.ψ⁰ (L.Ω (κ (suc n))) ≼ˣ (read (co (pts (suc n))) L.+ L.ψ⁰ (L.Ω (κ (suc n))))) × ((read (co (pts (suc n))) L.+ L.ψ⁰ (L.Ω (κ (suc n)))) ≼ˣ L.ψ⁰ (L.Ω (κ (suc n))))` | 链上的两向吸收 | 条件 |
| `absorb₁` | `(L.ψ⁰ (L.Ω (κ 1)) ≼ˣ (read (co (pts 1)) L.+ L.ψ⁰ (L.Ω (κ 1)))) × ((read (co (pts 1)) L.+ L.ψ⁰ (L.Ω (κ 1))) ≼ˣ L.ψ⁰ (L.Ω (κ 1)))` | n = 0 无前提 | 编译 |
| `step₂` | `∀ n → P2at n → FoldB (suc n) → P2at (suc n)` | 链的一步归约到折叠的两向界 | 条件 |
| `p2-from-fold` | `(∀ n → FoldB (suc n)) → ∀ n → P2at n` | `P2₂` 归约到 `FoldB` | 条件 |

两个前提的定义：

```agda
P2at n = (L.ψ⁰ (L.Ω (κ n)) ≼ˣ read (co (pts (suc n)))) × (read (co (pts (suc n))) ≼ˣ L.ψ⁰ (L.Ω (κ n)))
FoldB m = (L.ψ⁰ (L.Ω (κ m)) ≼ˣ read (obs (pts m))) × (read (obs (pts m)) ≼ˣ L.ψ⁰ (L.Ω (κ m)))
```

**可满足性：**
- `P2at` 与 `YiEmb2.P2₂` 的第 n 项逐字相同。`P2at 0` 是定理 (`p2₀ , back₁`)，n ≥ 1 未证。
- `FoldB m`：
  - 正向的值版本是已有定理 (`lower-read`)。
  - 反向的值版本是主线折叠的上界，没有证 (是 `YiUB` 那一路的题)。
  - 判断：若这个上界成立，`Tri` (`tri→cplˣ`) 就推出 `FoldB`，所以 `FoldB` 在经典模型里成立。

#### 4 办法

**压平的证书 (第 1 步)。**
- 把 Uniform §1–§7 的观测前序搬了过来，只多一种观测 `flo O`：先压平 `flat`，再接着观测。
- 每条对观测归纳的引理多一个情况，形状同 `ψ⁰o`。只有两处不同：
  - `suc-r`：压平保留后继；
  - `zero-l`：压平保留零，这里用到 `flat-≅`。
- `HS-flat` 对好树归纳。`gl` 与 `gi` 的步进取观测 `flo idO`；`gi` 沿 ψ⁰ 用的那条链 (`chain-step`)，它和 `flat` 的 `limᵢ` 一行是同一条链 (定义性地相等)。
- Uniform 本身导入不了这一步，因为它的观测里没有压平。

**见证 c (第 2 步)。**
- 取 c = `flat (Ω a)`，其中 a ≺ᴵ b。
- 基本一步走 Ω_{a+1} 的链的第 1 项 ψ_a(Ω_a)。`ψW` 在后继处取第 2 项 ψy + ψy；`addW` 说明它含后继 ψy + 1，因为 ψy 沿各极限的第 0 支有 0 前驱 (`W0`)。
- 穿透分支要求 `W0` 对一切 ≅ Ω_j 的支成立，所以证了 `W0-≅`。
- 一般的 a ≺ᴵ b 由 `flatΩ-mono (s⊑′ h)` 抬上去。

**c 让 X 的两个值不等式变成什么。** ψ⁰ c ≅ ψ⁰ (Ω a) (`ψ⁰-flat`)，所以前提可以对 ψ⁰(Ω_a) 陈述：
- 正向要 `ψ⁰ (Ω a) ≼ˣ X` 与 `X ≼ ψ⁰ (Ω a)`；
- 反向要 `X ≼ˣ ψ⁰ (Ω a)` 与 `ψ⁰ (Ω a) ≼ X`。
- 在链上，a = κ n，X = `read (co (pts (suc n)))`，两向的 `≼ˣ` 恰好是 `P2₂ n`；值序的两条由 `ˣ→≼` 得到。
- `YiUB` 可以直接用 `absΩ (κ≺ n)` 和 `absΩR (κ≺ n)`，对任意 X 成立，前提就是上面这两组。

**链上的 κ≺。**
- 由 `toLevel-≺` 归到 `X≺`。
- 下一点是这一点加折叠值 (`chain-cum`)；而 X ≺ X + Y 只要 0 是 Y 的结构前驱 (`lead0`)。
- `Z-top` 对 `Lv` 归纳：
  - `v0`：`succ` 的第 0 项是 1；
  - `vs`：`Way zero` 只有 `fold` (`Pre zero = ⊥`)，第 0 项是 `gm top`；
  - `vl`：部分和的第 0 项。

#### 5 第一个障碍

我这一路的范围里没有未过的。两次检查器报错都改好了：
- `HS-flat` 的 `gu` 情况报 ``[UnequalTerms] k != (suc k) of type Ordᴵ when checking that the expression g has type Good (up zero x)``。原因是 lossy unification 把隐式参数解成了 `up zero x`；显式写 `{x = x}` 后通过。
- `lead0` 报 ``[SplitError.UnificationStuck] ... {ℓ₁} ≟ {_ℓ₁_61 (X = X)}``。原因是 `≺` 左边的 `L.zero` 层号不定；改写成 `L.𝟎 {L.zero}` 后通过。

**"与 BTBO 持平"还缺的。** 现在只差主线一侧的 `FoldB m` (m ≥ 1)，类型见第 3 节。其中值的上界一半即 `YiUB` 的上界；`≼ˣ` 的两个方向都要。

#### 6 偏离与事故

- **`YiFlatObs` 是 Uniform 的副本。** 它是 Uniform §1–§7 的逐字副本 (加 `flo`)，约 355 行代码。从 Uniform 只导入了 ≅ 的小引理、`chain`、`chain-≅`、`self-back`、`self-back⁻`。
- **简报外的新增：** `YiFlatChain` §3 的归约 (`step₂`, `p2-from-fold`)。它可能与 `YiUBRed` 有重叠；`YiUB*` 的文件我没有读，也没有依赖。按中途通知可以导入 `YiEmb2`，但我没有导入。
- **我改动的范围：**
  - 没有改任何已有文件，没碰 `src/`、`archive/`，没有提交。
  - 只删过自己 4 个模块的 `.agdai`，写的是字面路径。
  - 两处用 python 改过自己的 `YiFlatChain` (一处字面替换，一处追加 §3)。
- **临时目录里的东西：** 日志和一份抽取 Uniform 代码块的草稿 (`uniform_code.agda`，没有用到)。冷编日志在 `<实验目录>/agents/flat/cold-*.log`。

文件：
- <仓库>/probes/OCF/Lean/YiFlatObs.lagda.md
- <仓库>/probes/OCF/Lean/YiFlatWit.lagda.md
- <仓库>/probes/OCF/Lean/YiFlatAbs.lagda.md
- <仓库>/probes/OCF/Lean/YiFlatChain.lagda.md
