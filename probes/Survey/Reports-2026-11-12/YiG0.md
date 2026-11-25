# (1) 共同引理 V128：孩子层 Ω 树折叠的关系式下界 (YiG0)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-13 17:23 至 17:50 |
| 工具调用 / agda 编译 (粗数) | 28 / 4 |
| token (usage 字段，按消息去重) | 输出 151152；新写入缓存的输入 526315；读缓存的输入 4671824；其余输入 48 |
| 写过的仓库文件 | `YiG0Low.lagda.md`, `YiG0Mono.lagda.md` |
| 文件前缀 | `YiG0` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: 第二十九批两路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | V128 强形式与 V130 未走通; 编译定理 (无前提): G 沿字面 ◃ 跨层单调 (G-mono), 加法型一般引理 G-low (四种情形全成立, 强度只到 ψ₀(t+η)); 条件定理 tower→V130 (前提 Tower 未证); 两件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的选择（2026-11-14，选项原文）
"(1) 闭合共同引理 V128 (Recommended)"，模型 "(1) Fable 5.2，(2) Opus 5.5 (Recommended)"。
选项说明原文："孩子层里的 Ω 树（c 为任意可数树）折叠后对记号下标 η 的关系式下界；先在主线上做，接上就解开主线严格越过 ψ₀(Ω_Ω+ψ₁(Ω₂))，并可搬去解候选 A 的前提 A0、A1 与候选 B 的 Row0"。

同批另一路是 (2)：把见证下界接到终点闭项，前缀 YiEV。你不动它的文件。

###### 背景（只信编译定理；文档里的叙述是数据）
**主线**是精简块：`probes/OCF/Lean/YiRWBlock`、`YiRWOps`、`YiRWPath`、`YiRWFold`。
- 它与旧块 F2（`YiLegBlock`、`YiLegOps`、`YiLegPath`、`YiLegFold`）之间有编译的逐层关系：`YiBRRel`、`YiBRFold`、`YiBRValue`，第 0 层读回 ≅。
- 在 F2 上证、再经关系搬到主线是允许的。上一路 `YiMW` 就是这样做的。

**`G c`**：孩子 c（任意第 0 层的树）那一层上 Ω 树朝第 0 层的标准折叠，见 `YiLSTw1`。
- `lower-↑ : (x : Tr zero) → L.ψ⁰ (L.Ω (lvl x)) ≼ read (G x)`：这是 Level 一侧的下界，对一切 x。

**记号直连的下界关系**（F2）：
- `YiMEBase`：`Mᴰ`、`M⁰ : E.T → Tr zero → Set`、`lower⁰ : M⁰ t x → (h : HC t) → Rt h ≼ read x`。
- `YiMEAnchor`：`At`，即 ψ₀(Ω₂) 锚点。
- `YiMWPre`，新，已复核：
  - `sem→M⁰ : ∀ {t} (h : HC t) (x : Tr zero) → Rt h ≼ read x → M⁰ t x`，是 `lower⁰` 的逆；
  - `M⁰-≼`：关系对读回的 ≼ 向上封闭；
  - 带记号前缀的锚点 `Pre`（`QHp`、`VWp`、`rowp`），对任意底、任意前缀。
- `YiMWLow`：`tA≼Vᴿ`，主线最小见证 ≥ ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照；`B0≺Vᴿ`。

**V128 的用户，各自的第一个障碍都是这一类引理**：
1. **主线，`YiMW` 回报 §4**（`probes/Survey/Reports-2026-11-12/YiMW.md`）：
   - 严格越过 tA：`L.suc (Rt hA) ≼ readRW Vᴿ`（台账 V130）；
   - tB 的第 1 行：`M⁰ (fsn tB 1) DR.V`，读作 ψ₀(Ω_Ω+ψ₁(Ω_Ω+Ω₁))。
   - 执行方的判断：`Mᴰ` 的种子形式不可得，因为树一侧 β₁ 的分支 Ω₁ + G c 不是结点，关系太刚；要改在折叠之后比较。缺的是：对高于 BTBO 的 c 与 `M⁰ η c`，`Rt(ψ₀(Ω_Ω+ψ₁(Ω_η))) ≼ read (G c)` 一类。
2. **候选 A，`YiKVValue`**（回报 `YiKV.md` §6）：
   - `A0 = (η : E.T) (c : Tr zero) (w : zero ≤ h₁ c) → M⁰ η c → M⁰ (ψ₀ᵗ (E.Ωt η)) (proj₁ (A0f c w))`；
   - `A1` 是第 1 层的版本，只对候选块成立，主线上判断不成立。
   - 对 `M⁰ η c` 归纳：极限情形已编译（`YiKVInst.a0-lim`、`a1-lim`）；零、后继、松弛（`mw`）三种情形未证。
   - 后继要孩子层号 h₁ c′ 上的关系与跨层单调；松弛要 `g₁`/`G` 对 c 沿 ◃ 的跨层单调。
3. **候选 B，`YiBPAccept.Row0`**：同类，在另一块上。

**第十六次独立审查的判断**（纸面，回报 `Review16.md`）：
- 树上的 ψ⁰(Ω_c)，c 高于 BTBO 时不塌缩，量级对应记号 ψ₀(Ω_Ω+ψ₁(Ω_c))，不是 ψ₀(Ω_Ω+Ω_c)。
- 机制：ℕ 极限层号上的 Ω 是固定基本列的 ℕ 和。

**相关的值工具**：
- `YiVR*`：块侧值关系 `Le`、折叠保持 `fl`，到塔第 1 项；缺跨孩子层的关系 `GMono`，台账 V120。
- `YiNFO`：`mono<`、`up≼`，标准形上项序推出参照值序。
- `YiNFOCase`：`tA`、`tB`、`hA`、`hB`、`A≺B`、`btbo≺A`。

**AGENTS 的当前最佳实践**："量化域先取带证据的读回域"。封闭与保持定理先对规范构造的读回域陈述，不对 "一切合法树"；连续两条同形的退化反例就停下来查量化域。

###### 要做
1. **一般引理**：在 F2 或主线上，给出 `G c`（孩子 c 层上 Ω 树的折叠）对记号的关系式下界。
   - 形式由你定，例如 `M⁰ η c → M⁰ (ψ₀ᵗ (E.Ωt η)) (G c)`；或带前缀的 `M⁰ (ψ₀ᵗ (tΩ ++ ψ₁ᵗ (E.Ωt η))) (G c)`，前提是 c 高于 BTBO。
   - 量化域可以取规范读回域。
   - 写清它对 `M⁰ η c` 的哪几种情形成立。
2. **用在主线上**：至少交其中一条；都做不到就交第一个挡住的引理。
   - (a) V130：`L.suc (Rt hA) ≼ readRW Vᴿ`；
   - (b) tB 第 1 行：`(h : HC (fsn tB 1)) → Rt h ≼ readRW Vᴿ`。
3. **可选**：说明这条引理能否搬去解 `YiKVValue.A0`。写成定理或一句判断即可，不要求搬完。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiG0`（模块名 `OCF.Lean.YiG0…`）。不改任何已有文件，不碰 `src/`、`archive/`。这是验收文件，文首标明；树、折叠、合法性一行不改。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
  - 堆墙：不要在具体推导上直接比较两个 `Rt`（`YiMW` 在这里耗尽过一次），对一般推导陈述再代入；具体参照树放 `opaque`；见 `probes/Survey/EBOHandbook.md` 第 4 节。
- 临时目录：`<实验目录>/agents/g0`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽；连续两条同形的退化反例。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：一般引理在什么量化域、哪几种情形成立；(a)(b) 是否编译成立；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档；值写成 ψ₀(Ω_x)，并写清参照的读法依据。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 回报：V128（`G c` 对记号的关系式下界），前缀 YiG0

##### 1. 判决

**V128 的强形式没有编译出来，(a) V130 与 (b) tB 第 1 行都没有编译出来，也没有编译的否定。只能写 "未走通"。**

编译出来的是三件，都在 F2 上，无前提：

- **`G` 沿第一位置序跨层单调**（`G-mono`）：对一切第 0 层的树 x、y，有字面的 `x ◃ y` 就有 `read (G x) ≼ read (G y)`。这是 A0 型归纳里的松弛情形，也是台账 V120 在 "字面 ◃" 下的版本。按值的 `GMono`（x、y 只有读回的 ≼）仍未证。
- **加法型的一般引理**（`G-low`）：`M⁰ (ψ₀ᵗ t) (G c₀) → M⁰ η y → M⁰ (ψ₀ᵗ (t ++ η)) (G (c₀ + y))`。
  - 量化域：一切第 0 层的树 c₀、y，一切前缀 t。
  - 对 `M⁰ η y` 的零、后继、极限、松弛四种情形都成立。
  - 强度只是界：`G (c₀ + y)` 不低于 ψ₀(t+η)。取 c₀ = `E₀`、t = Ω_Ω 时是 ψ₀(Ω_Ω+η)，不是所要的 ψ₀(Ω_Ω+ψ₁(Ω_η))。
- **V130 的条件归约**（`tower→V130`）：前提 `Tower` 推出 `O.suc (R2.Rt h) ≼ readRW Vᴿ`，对一切 `h : HC tA`。`Tower` 没有证也没有否定，所以这条是条件定理。

**对纲领与目标。**
- 两个文件都是验收文件，不进成品；树、折叠、合法性一行未改。
- `G-low` 的后继步只用到 "`G (suc x)` 的第 1 行在 `G x` 之上"，没有用到后继层号上 Ω 塔的折叠，所以够不到 tA 之上。
- 主线仍停在 "见证值 ≥ ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照"（`YiMWLow.tA≼Vᴿ`，非严格）。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| V128 强形式：`M⁰ η c → M⁰ (ψ₀ᵗ (tΩ ++ ψ₁ᵗ (E.Ωt η))) (G c)` 一类 | 无 | 未走通 |
| (a) V130：`L.suc (Rt hA) ≼ readRW Vᴿ` | 只有条件定理 `YiG0Low.tower→V130` | 未走通（前提 `Tower` 未证） |
| (b) tB 第 1 行 | 无 | 未尝试 |
| `G` 沿字面 ◃ 的跨层单调 | `YiG0Mono.G-mono`、`G-mono⊴` | 编译定理 |
| 关系沿孩子的 ◃ 搬运（松弛情形） | `YiG0Low.G-mw` | 编译定理 |
| 加法型一般引理，四种情形 | `YiG0Low.G-low`，实例 `G-lowE` | 编译定理 |
| `G` 膨胀；`G (suc x)` 严格高于 `G x` | `YiG0Low.G-infl`、`G-strict` | 编译定理 |
| 按值的 `GMono`（V120 原陈述） | 无 | 未做 |
| `Tower` 成立 | §4 | 判断，未编译 |

##### 2. 文件表

都在 `<仓库>/probes/OCF/Lean/`。删自己的两个接口后冷编，堆上限 8G，每份日志只有本模块一行 `Checking`。禁用构造与本机路径检索为 0。

| 文件 | 总行 / 代码行 | 冷编退出码 | 内存（`+RTS -s` total in use） |
|---|---|---|---|
| `YiG0Mono.lagda.md` | 157 / 104 | 0 | 1874 MiB |
| `YiG0Low.lagda.md` | 178 / 106 | 0 | 2016 MiB |

冷编日志在 `<实验目录>/agents/g0/`，文件名 `YiG0Mono.cold.log`、`YiG0Low.cold.log`。

##### 3. 定理表

记号：
- `G`、`h₁`、`εh`、`ρh` 是 `YiLSTw1` 的；`read` 在 Mono 里是 `YiLSRead.read`（Low 里写 `S.read`），Low 里不带前缀的 `read` 是 `YiMEBase.read`。
- `E₀`、`c₁`、`V` 是 `YiDropRow` 的；`tΩ`（ψ₀ᵗ tΩ 即 ψ₀(Ω_Ω)）是 `YiMWLow` 的；`tA` 是 `YiNFOCase` 的记号项 ψ₀(Ω_Ω+ψ₁(Ω₂))。
- 参照的读法依据：参照是 `HC` 推导沿记号基本列造的树，ψ₀(Ω_x) 的写法来自项本身。

| 名字 | 逐字的陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `toR`、`toR-R` | `toR : F.Tr F.zero → Tr zero`；`toR-R : (x : F.Tr F.zero) → RelT zero F.zero (toR x) x` | F2 的第 0 层的树搬到精简块，与原树相关 | Mono | 编译定理 |
| `G-R` | `(c′ : F.Tr F.zero) → RelT zero F.zero (Gᴿ (toR c′)) (T1.G c′)` | 两块上孩子层 Ω 树的折叠相关，对一切孩子 | Mono | 编译定理 |
| `rowᴿ` | `(g : ℕ → L) (o : Ok (nd sL g)) (n : ℕ) → NoΩ (g n) → (X : Tr (nd sL g)) → readRW (proj₁ (ψ₀ (g n) (proj₂ o n) (proj₁ (Ωt (g n))))) ≼ readRW (proj₁ (ψ₀ (nd sL g) o (up X n (proj₁ (Ωt (g n))) (proj₂ (Ωt (g n))))))` | 主线：ℕ 极限层号上第 n 行的折叠不低于孩子 n 自己的折叠 | Mono | 编译定理 |
| `limᴿ` | `(f : ℕ → Tr zero) (a : (n : ℕ) → zero ⊢ f n ◃ f (suc n)) (n : ℕ) → readRW (Gᴿ (f n)) ≼ readRW (Gᴿ (lim f a))` | 主线：极限孩子的 `G` 不低于各项的 | Mono | 编译定理 |
| `G-mono` | `{x y : F.Tr F.zero} → F.zero F.⊢ x ◃ y → read (T1.G x) ≼ read (T1.G y)` | F2：`G` 沿字面 ◃ 单调 | Mono | 编译定理 |
| `G-mono⊴` | `{x y : F.Tr F.zero} → F.zero S.⊢ x ⊴ y → read (T1.G x) ≼ read (T1.G y)` | 同上，自反闭包 | Mono | 编译定理 |
| `formS` | `(x : Tr zero) → G (suc x) ≡ limc (rowS x) (nzS x)` | 后继孩子的 `G` 是链 `zs x` 上各行的部分和极限 | Low | 有限测试（`refl`） |
| `G-strict` | `(x : Tr zero) → O.suc (S.read (G x)) ≼ S.read (G (suc x))` | `G (suc x)` 严格高于 `G x` | Low | 编译定理 |
| `G-suc` | `∀ {s p} (x : Tr zero) → cof s ≡ cω → (∀ n → fsn s n ≡ replicate n p) → M⁰ (p ∷ []) (G x) → M⁰ s (G (suc x))` | p 对着 `G x`，则基本列为 p·n 的项对着 `G (suc x)` | Low | 编译定理 |
| `G-mw` | `∀ {s} {x x′ : Tr zero} → M⁰ s (G x) → zero ⊢ x ◃ x′ → M⁰ s (G x′)` | 关系沿孩子的 ◃ 搬运 | Low | 编译定理 |
| `G-infl` | `(y : Tr zero) → S.read y ≼ S.read (G y)` | `G y` 不低于 y | Low | 编译定理 |
| `G-low` | `∀ {t} (c₀ : Tr zero) → M⁰ (ψ₀ᵗ t) (G c₀) → ∀ {η y} → M⁰ η y → M⁰ (ψ₀ᵗ (t ++ η)) (G (c₀ + y))` | `G (c₀+y)` 不低于 ψ₀(t+η) | Low | 编译定理 |
| `mE₀` | `M⁰ (ψ₀ᵗ tΩ) (G DR.E₀)` | ψ₀(Ω_Ω) 对着 `G E₀` | Low | 编译定理 |
| `G-lowE` | `∀ {η y} → M⁰ η y → M⁰ (ψ₀ᵗ (tΩ ++ η)) (G (DR.E₀ + y))` | `G (E₀+y)` 不低于 ψ₀(Ω_Ω+η)（界） | Low | 编译定理 |
| `E₀2◃c₁` | `zero ⊢ suc (suc DR.E₀) ◃ DR.c₁` | 链点 c₁ 之下字面地有 E₀+2 | Low | 编译定理 |
| `Tower` | `Tower = ∀ n → M⁰ (fsn tA n) (G (suc DR.E₀))` | 陈述：tA 的各基本列项对着 `G (E₀+1)` | Low | 陈述，未证 |
| `tower→V` | `Tower → (h : HC tA) → O.suc (R2.Rt h) ≼ S.read DR.V` | F2：前提下见证值严格高于 tA 的参照 | Low | 条件定理 |
| `tower→V130` | `Tower → (h : HC tA) → O.suc (R2.Rt h) ≼ readRW Vᴿ` | 主线：同上，即 V130 | Low | 条件定理 |

`G-mono` 的证法：F2 的树搬到主线（`toR`），用 `YiBRTw.tw-E 1` 取出孩子层的证据关系，再用主线已有的 `YiVRRead.kid-Ω`（孩子 c 到 c+1）与 `fold-≼`（默认底不高于由前面部分和造的孩子底，`infl`），最后经 `rel≅` 搬回。

##### 4. 第一个障碍（精确到引理）

**第一个挡住的是 `Tower`**：`∀ n → M⁰ (fsn tA n) (G (suc E₀))`，其中 `fsn tA n` 是 ψ₀(Ω_Ω+ψ₁(γₙ))（`YiMWLow.tA-fs`，`refl`）。它成立则 V130 成立（`tower→V130`）。

**为什么关系式的证法在这里停下**（判断，未编译）：
- `G (suc E₀)` 是层号 `h₁ E₀`（记作 a）上链 `zs` 的折叠。`zs 2` 之下字面地有一个结点：槽位是 a 的子层号 2 上的那个（分支取第 1 层的树 u），分支是 `next (Up one d (Ωt a) u)`。`h₁ E₀` 的 (0,0) 位置的子层号是 2，这一点我只做了纸面展开，没有编译。
- 要让 ψ₀(Ω_Ω+ψ₁(γₙ)) 对着这个结点的折叠，需要照 `YiMEAnchor.At` 的三条保持（`PF`、`QH`、`VW`），但对象换成 `Up one d (Ωt a) u`（第 1 层的树上折进层号 a）。缺两条：
  1. **起点沿槽位路径的折叠不低于 BTBO**：`D.BTBOᴵ ≼ read (ψs a … (B₀ a) zero (posW a p₁) (Ωt zero) … (Ωt a))`，p₁ 是 a 里分支为第 0 层的那个槽位。已有的 `YiLSTw1.KG` 只管 `lift` 形的路径（`LiftP`），`posW` 走 `inl`，不在它的域里。
  2. **后继情形的上折**：`ψs`、`ψ⊥` 作用在 `next (Up … u)` 上不是 `next` 的形状，要靠 `Ωt a` 之下字面的 `up … (suc zero)` 换出一步，三条保持各要一份。
- 在层号 a 上直接写 `Mᴰ` 的实例走不通：`Ωt a` 在 a 层的第一位置序下没有可数的结构，它的值只在折到第 0 层后出现。这与 `YiMW` §4 的判断同一类，仍是 "关系太刚"，不是数学障碍。

**`Tower` 是否成立**：我的纸面推演与第十六次审查的说法方向一致（Ω_a 的塔的指数位置里有真正的 Ω₂），但没有编译，按规则不能写成定理。

**可选项 3（搬去 `YiKVValue.A0`）**（判断）：
- 松弛情形的做法可以照搬：把孩子搬到有值关系的块上，用折叠对底的单调，再搬回。但候选 A 的块上有没有 `fold-≼` 一类的工具我没有查。
- 零情形由单调加一个起点得到。
- 后继情形挡在同一类引理上（后继层号上 Ω 塔的折叠对记号的下界），本路没有解开。

##### 5. 偏离与事故；没有读、只凭转述引用的东西

- **偏离**：
  - 一般引理交的是加法型（ψ₀(t+η)），不是简报举例的 ψ₀(Ω_η) 或带 ψ₁ 的形式。
  - (a) 只交了条件定理，前提未证；按 "前提要可满足" 的规则，这条前提的可满足性只有纸面判断。
  - 第一个文件没有在 30 分钟内写出：前面读定义与比较路线用时较长。
  - 没有做 Level 一侧的桥，没有碰 (b)。
- **事故**：`YiG0Low` 第一次编译报 `ClashingDefinition`（局部名 `P` 与 `YiLegBlock` 的记录字段重名），改名 `P₁` 后通过。没有堆耗尽。
- 临时目录里只有编译日志。`rm` 只删了自己的两个 `.agdai`。没有碰别人的文件，没有提交。
- **没有读或只读了一部分**：
  - `Review16.md`、`YiKV.md`、`YiKVValue`、`YiKVInst`、`YiBPAccept`、`YiNFO`、`YiNFOCase`、`EBOHandbook.md` 第 4 节、`IdeaLedger`（只检索了 V120 一行）：没有读。关于审查结论的说法取自简报与 `YiMW.md` 里的转述。
  - `YiLSFold`、`YiLSBtbo`、`YiInv`、`YiT2Frame`、`YiRWOps`、`YiRWPath`、`YiVRRel`、`YiVRFold`、`YiBRFold`、`YiBROps`、`YiBRLem`、`YiBRTw`：只看了签名与用到的几段。
  - `Level.lagda.md` 读了 §1、§4、§8、§9 的定义，其余没有读。
