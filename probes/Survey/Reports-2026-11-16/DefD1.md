# D1：高一阶框架与第 1 层以上 ex 的内部 View（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-17 15:30 至 16:00 |
| 工具调用 / agda 编译 (粗数) | 39 / 10 |
| token (usage 字段，按消息去重) | 输出 185075；新写入缓存的输入 392124；读缓存的输入 7614851；其余输入 76 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `DefD1` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 两项都通过：二阶改用自然 op 的进框架迭代子，E2 的 ho-bare 那一格改为保留并与 ψ♯ 同为保留（ho-both），端到端第二次回灌给 Ω 结点而 E2 给 ℕ 极限（有限测试）；第 1 层以上 ex 的内部 View brwView 编译，对一切层号成立；实验文件主审删接口 6G 冷编都退出 0（附件 attachments/DefD1-*.txt）；定义文件无排中律；余项：第三阶仍不开框架，忘回模式在二阶孩子框架里又有裸判定（fg-bare），View 的部分良基与 val 和读回的关系未证；仍只有形状没有值 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b93/D1.md`。先用 Read 工具完整读它，再逐条照做（含 "止损"、"规则" 与回报格式）。所有文件只放简报指定的实验目录，不改仓库里任何文件。全程用中文。最后一条消息就是你的全文回报。

## 回报原文

#### D1 回报（Opus 5.5）

##### 0. 结论
两项都编译通过，止损没有触发（两项都是第一种写法就通过了）。

- **高一阶带框架：** 二阶改用自然 op 的进框架迭代子 `E₂en`。E2 里 `ho-bare` 那一格是 `nothing`，现在是 `just`，与 ψ♯ 的 `kp♯` 同为保留（`ho-both`）。
  - 端到端有限测试：同一个闭项第二次回灌时，D1 给出 q 上的 Ω 结点（`second-feed₂`），E2 给出 ℕ 极限（`D1Contrast.old-feed2`）。
  - 膨胀律、`Emh`、停机都照旧编译通过。
- **第 1 层以上 `ex` 的内部 View：** `brwView` 已编译，对一切层号成立。View 五条按 S2 §2.1 写出，值与对应构造子作用在部分的值上互相 `≼`。
- **对纲领的意义：**
  - 定义文件没有排中律，没有公设，也不引用记号；导入闭包只有 stdlib、D1*、`BrwViewDef`。
  - 本轮只有形状和 View，没有折叠的值定理，强度仍只有 BTBO 那一档。

##### 1. 新文件、关键定理与档位
工作目录是 `<实验目录>/cl/D1/`，仓库没有改动。

| 文件 | 行数 | 内容 |
|---|---|---|
| `D1Block.agda`、`D1Ops.agda`、`D1Path.agda` | 288 / 107 / 170 | 与 E2 的对应文件相同，只改了模块名 |
| `D1Fold.agda` | 514 | 新的二阶、三阶，其余同 E2Fold |
| `D1Check.agda` | 约 305 | 判据 |
| `D1Contrast.agda` | 63 | 在 E2 折叠上做的对照，要 `-i cl/E2` |
| `D1Val.agda` | 255 | 值 |
| `D1View.agda` | 157 | View |

`mid.agda.part` 是拼接用的草稿片段，不是模块，可以忽略；按规则没有删。

**1.1 高一阶框架（`D1Fold`）【编】**

新增的构件：
- 框架延伸 `data Ext ρ w`，以及 `embE`、`dropE`、`trE`。它们只看链的构造子，不比较孩子。
- 出框架 `leave`，逐点严格序 `Rl`。
- 自然 op：`record NOp w₀`，字段 `nrun : Ext w₀ w → Op w → Op w` 与 `ninf`。它对基框架的一切延伸都给出严格膨胀的变换。

二阶 `E₂en o d e x K G`（树框架与元素框架都是 d）：
- Ω 行：判定是 `kpT d o p t`，走链目标是 `hereT d (posW m p)`，即框架写法。
- up 行：`leave d c (E₂en o (down d c) (exd ex0 c) y (Kup o d e K x) (enter d c (E₂en o d e x K G)))`。
  - 也就是进孩子框架，从 `E₂ x K G` 起，把 "E₂ x K" 在孩子框架上的自然分量迭代 ω^y 次，再出框架。
  - 起点改成 `E₂ x K G`、不从 G 起，是因为这样单调的 `◃u` 行只要膨胀律，不要求深框架分量在外层目标上与本框架字面相等。
  - 两种起点的序数值相差的是吸收 1+ω^y = ω^y【纸，没有定理】。
- 深框架上的分量走忘回版本：一阶的 `EF` 与二阶的 `E₂fg`。元素框架固定，树的孩子框架不进，判定是 "忘到公共根再进树框架"。
- 分派：`E1`（一阶）和 `E₂at`（二阶）按延伸是否为 `ex0` 选择进框架或忘回。分派只匹配链的构造子。
- 第三阶（指数的指数里再有 ex）：仍用 E2Block 的通用 `Eh`，载体 `A₃` 是 `NOp`，不开框架，与 E2 的 A₂ 同形。
- 一阶 E 的 ex 行：`run (E₂en o d ex0 x (Kb o d b nb) (op (E o d a F) …))`。
  - `Kb` 在本框架上就是 E：`e-kb : nrun (Kb …) ex0 G ≡ op (E o d b G) …`，refl。
- 律：`E₂eninf`、`E₂enmono`、`E₂fginf`、`E₂fgmono`、`EFmono`、`E1inf`、`E₂at0`；三阶的 ◃x 行用 `Emh`。
- 写法上的一个要点：互递归块里，被证明用来归约的定义必须排在证明之前。

**1.2 判据（`D1Check`，都是 refl；标出的是有限测试）**
- **E1 的 (a)(b)(c) 重跑：** `top-chain`、`child-keep`、`step-node`、`first-feed`、`second-feed`、`old-k6`、`k-both`、`k-bare`、`k-bare-flat`、`c-base`、`c-chain`、`c-sharp`，全部通过。
- **E2 的 (d)(f)(g)(e′) 重跑：** `rd-zero`、`rd-suc`、`ok-child`、`f-zero`、`tw2-ok`、`tw2-head`、`e-fold-head`，全部通过。
- **(e) 改述为新写法：** `e-row`、`e-nest`（转到 A₃）、`e-up`（上面那条 up 行）、`e-at`、`e-kb`。E2 原来的 `e-up` 和 `e-nest` 是旧 A₂ 的形状，已被取代。
- **(h) 取代 E2 的 `ho-chain` / `ho-bare`：**
  - `ho-chain`：在框架 d₁ = [2] 里，二阶 Ω 行走链的回灌目标是 `inj₁ τ`。E2 里是被忘成的 `inc 2 τ`。
  - `ho-keep`：框架 d₂ = [2, tt] 的 q 结点在目标 `inj₂ (inj₁ τ)` 上，输出是 `Ω q _`。
  - `ho-both lem : IsJust (kp♯ …) × IsJust (kpT d₂ o₁ q (inj₂ (inj₁ τ)))`。
- **端到端【有限测试】：** 闭项 `tm₃ = ex 0 b (ex 0 b (up 0 2 (Ωt lvl2)))`。
  - `top-chain₂`：顶结点走链。
  - `first-feed₂`：第一次回灌，头部为 `lim H`，`H 0 ≡ Ω q _`。
  - `second-feed₂`：第二次回灌，`lim H`，`H 0 ≡ lim H′`，`H′ 0 ≡ Ω q _`。这一次的 q 结点由二阶判定保留。
- **对照（`D1Contrast`）【有限测试】：**
  - `old-top`：确认 `sTopᴼ` 就是 E2 折叠在 `tm₃` 上的走链一步。
  - `old-feed2`：同一处 E2 给出 `H′ 0 ≡ lim H″`，是 ℕ 极限。
- **(i) 代价【编，形状】：**
  - `fg-chain`：一阶树在更深的元素框架上用 EF 跑时，自己孩子顶结点走链的目标被忘成 `inj₂ (inc 2 τ)`。
  - `fg-bare`：再下一层的 q 结点对它的判定是 `nothing`，即 k-bare 那一格。
  - E2 在这里用 E 进框架，给 `just`。所以两种写法互不包含【判】。

**1.3 值与 View（`D1Val`、`D1View`）【编】**
- **值：** `val ℓ (ex a b _ x _) = Ev (val ℓ x) (_⊹ val ℓ b) (val ℓ a)`。
  - `Ev` 是 V 上 "F 迭代 ω^x 次"；其余行同 YiVWVal（V 只有零、后继、ℕ 极限、本层槽位的 Ω，up 经孩子嵌入摊平）。
- **`Ev` 的律：**
  - `Ev-monoᵘ`：对底单调。
  - `Ev-monoˣ`：对指数按 `≼` 单调，按推导归纳。
  - `Ev≈`：对指数 ≈ 相合。
  - `Ev-infl`：严格膨胀。
  - `Ev-step`：对指数按 ◁ 严格单调。
  - `val-mono`：◃ 映到 ◁，含 `◃e`、`◃x` 两行。
- **View：** `brwView : BrwView SigY Tr val (λ _ → ⊤)`，用通用记录 `OCF.Align.BrwViewDef`。ex 行由 `exView` 按 x 的 View 分情形：
  - x 为零：给 a + b。由 `addView` 从 b 的 View 生成，部分是 `exz a y`，其中 `val (exz a y) ≡ val a ⊹ val y`。
  - 后继：ℕ 极限，逐项 `ex (前一项) b x′`（`itx`、`val-itx`），步进由 `Ev-infl` 给出。
  - ℕ 极限：逐项 `ex a b (f n)`，步进由 `Ev-step` 给出。
  - 结点：同一槽位上的 Ω 极限，`ex a b (g z)`。
  - x = up …：x 的 View 已由 `mapUp` 按 y 读出。
- 部分都是同层的树，值的一致由 `Ev≈`、`lim≡`、`⊹≈` 给出。

##### 2. 编译结果
- 命令从仓库根目录跑：`agda +RTS -M6G -RTS --library-file=<scratchpad>/libraries -i src -i probes -i <cl/D1> [-i <scratchpad>/math/S1 | -i <cl/E2>] <文件>`。
- 用完整文件名删掉自己的 8 个 `.agdai` 后冷编，退出码都是 0：

| 入口 | 依次检查的模块 | 峰值驻留 | 用时 |
|---|---|---|---|
| `D1Check` | D1Check、D1Block、D1Ops、D1Path、D1Fold | 346 MB | 6.9 s |
| `D1View` | D1View、D1Val | 335 MB | 3.5 s |
| `D1Contrast` | 只重编自己 | 159 MB | 2.0 s |

- 之后加了 (i) 两条，单独重编 `D1Check`，退出码 0。
- 警告只有 `UnsupportedIndexedMatch`（104 条）。
- 检索过：没有 postulate、洞或编译指示；排中律只在 `D1Check` 里作参数。
- E2 目录的 `.agdai` 没有被改写（时间戳仍是 23:24）。

##### 3. 对下一步的意义
下一个必经缺口，按位置排：
1. **值。** 折叠没有任何值定理。BTBO 下界一族（`bho-lower`、`bho-tw1`）要对 `ex` 自身行、`E₂en`、`EF`、`E₂fg` 重证。与记号接得上的值仍只有 BTBO。
2. **第三阶不开框架。** A₃ 的写法同 E2 的 A₂，所以 ho-bare 现象会在 "指数的指数的指数" 一层再现【判，没有测】。
   - 可以把 `E₂en` 的写法推广到通用的带框架代数：自然 op 加进框架 up 行，从 `E x K G` 起迭代。三阶起每阶都要一套 en/fg 与分派。
3. **忘回模式的代价（`fg-bare`）。** 二阶孩子框架里跑一阶树时，它自己的孩子框架不进。
   - 候选：让 EF 内部的目标取 "树框架 ⊎ 元素框架" 的和，树内部的走链目标按树框架判定【纸，没有写】。
   - 已知的难点：状态 `St w` 只有元素框架的项，树框架局部目标的状态只能取忘回的值；它对膨胀律是否无害，没有验。
4. **View 的余项。**
   - 部分良基没有做：`itx n`、`exz` 不是字面子项。
   - `val` 与读回 `↑`（`Eh`）的关系没有定理。
   - `val` 与二阶 "起点改为 E₂ x K G" 的值相同，只是纸面判断。

规模：相对 E2，净增约 740 行（Fold +213、Check +70、Val 255、View 157、Contrast 63）。

##### 4. 没有读、只凭转述引用的
- 没有读 E1 的回报 `RedefN2.md` 原文；E1 判据的含义来自 E2 回报的转述，判据本身是原样重跑的。
- 没有重读 `YiAbsObs`、`YiAbsFrame` 和 `obs→dec` 一族的陈述，也没有写配对的否定。
  - 新的派发是 `E1` 与 `E₂at` 按 `Ext` 的构造子分派，以及 `kpT` 配 `embE`/`dropE`。只看链的结构，不比较孩子，也不搜索。
  - "不触犯 `obs→dec`" 是纸面判断。
- 没有读 `EBOHandbook`；本轮没有遇到堆的问题。
- 读过的：`AGENTS.md`，DefE2 回报，E2 的五个文件，RedefS2 §2（View 五条取自 §2.1），`YiVWVal`，`YiVWView`，`BrwViewDef`。
- ψ♯ 一侧只复用了 E2Check 里 `k-both` 对 `kp♯` 的调用，没有读 S1Sharp 全文。
