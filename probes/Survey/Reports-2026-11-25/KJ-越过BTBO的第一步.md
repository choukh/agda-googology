# KJ：越过 BTBO 的第一步（Opus 5.5，续做）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-24 16:42 至 04:45 |
| 工具调用 / agda 编译 (粗数) | 72 / 2 |
| token (usage 字段，按消息去重) | 输出 141848；新写入缓存的输入 625766；读缓存的输入 14323402；其余输入 124 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `KJ` (在 `<实验目录>/m8/`) |

## 简报原文

你的任务简报全文在这个文件里，请先完整读它，再严格照做（它是自足的，背景、任务、约束、回报格式都在里面，其中第一步是读公共约束文件）：

<实验目录>/briefs/M5.md

要点提示（以简报为准）：这是一个 Agda 形式化任务（--safe --without-K）。以已编译的接口陈述 KLowIface.LOWERᵂ（可数层号上 W4 的折叠不低于参照系统在镜像码上的折叠）为唯一的模块参数，证 tr₀ Ord-Ord.BTBO ≼ read EBOᶜ。做法照搬仓库里旧主线的先例（probes/Survey/RR7-BtboLower.md，probes/OCF/Lean/YiBtboLower.lagda.md 与 YiBtboV2.lagda.md）：链上只带值序，每步造到下一个链点层号码的前驱嵌入；其中与块无关的两段可以直接导入，第三段（链点的规范化层号嵌进 W4 折叠值的字面前驱）要写 W4 版，简报里给了推广到一切运行的建议写法（是纸面判断，不成立就照实报）。共享基目录是 scratchpad/w5（不是 w4）。只在你的工作目录 <实验目录>/m5 里写，模块前缀 KAs；不改仓库、W4 与共享基目录里的任何文件；同时只跑一个 agda，堆上限 6G；不提交。做不完时把没证的部分写成带确切陈述的模块参数，使文件整体编译。你的最终消息就是回报原文，中文，按公共约束里的回报格式。

## 中途消息（主审发给这一路）

转录时间戳 2026-11-25 04:34 (UTC)：

新任务 KJ（越过 BTBO 的第一步）：你上次交的装配已复核并入库，LOWERᵂ 现在无前提，所以 tr₀ BTBO ≼ read EBOᶜ 是无前提的定理；请在它之上证 J BTBOᴵ ≼ read EBOᶜ，其中 J x 是从 x 起步的链 x, ψ⁰(Ω_x), … 的极限。

简报全文在这个文件里，请先完整读它，再严格照做：

<实验目录>/briefs/KJ.md

要点（以简报为准）：基目录换成 scratchpad/w10（原 W4 的整条链，含你的 KAsBase/KAsV3/KAsTw、KBtbo、无前提的 KLow.lowerW，以及真实运行的追踪 Audit2；都已编译，只读），编译命令里的 -i 目录相应替换；新工作目录 scratchpad/m8，前缀 KJ。分三步：Level 一侧定义从任意带证书的树 x 起步的链与极限 J x（SV-toLevel、St-F、Uniform 等引理是对一般的树陈述的）；把 Run 推广成"状态的第 0 层条目不低于 x 时 J x 不高于输出"；再用塔第 2 项的真实运行里孩子 zero（层号就是 tw 1）的那个运行接到闭项，它的第 0 层条目含塔第 1 项从头折的值作尾巴。定理要无前提；做不完时把没证的部分写成带确切陈述的模块参数并报出。约束不变：只在自己的工作目录里写，同时只跑一个 agda，堆上限 6G，不提交。最终消息就是回报原文，中文，按公共约束里的回报格式。

Address this before completing your current task.

## 回报原文

第 1 份，转录时间戳 2026-11-24 16:58 (UTC)：

#### M5 回报（前缀 KAs，工作目录 <实验目录>/m5）

**对纲领与目标意味着什么。** 这是一条第四层（序数值验收）的条件定理：已发表的 BTBO 闭项不高于 W4 的 EBOᶜ。条件只有一条，即模块参数 `lower : LOWERᵂ`，也就是在跑的"可数层号定理"的出口陈述。树、折叠、合法性一行没改，w5 与仓库里的文件也没有动。只要另一路证出 `LOWERᵂ`，这条下界就不再带条件。这只是下界，不涉及上界与同值。另外，"BTBOᴵ = ψ₀(Ω_Ω)" 在仓库里仍是估计（NoCumsum §4），所以这里只说"不低于已发表的 BTBO 闭项"。

##### 1. 文件（三份都是纯 .agda，第一行逐字照公共约束的选项）

| 文件 | 行数 | 最后一次编译的退出码 |
|---|---|---|
| KAsBase.agda | 132 | 0 |
| KAsV3.agda | 162 | 0 |
| KAsTw.agda | 141 | 0 |

- 最后一次是冷编：先删了 m5 里自己的 .agdai，再编 KAsTw。日志里只有三个 KAs 模块的 Checking 行，共享模块都从接口读入。用时约 9 秒，堆上限 6G。
- 已查：没有 postulate、洞、TERMINATING / NO_POSITIVITY，也没有函数外延。
- 编译脚本 c.sh 也放在 m5 里。

##### 2. 编译定理（陈述逐字抄出）

**第 1 段（KAsBase，无前提）**
- `◃→≺ : {x y : Tr zero} → zero ⊢ x ◃ y → read x LV.≺ read y`：第 0 层的步进序给出 read 的字面前驱。`◃l` 情形对构造子里存着的相邻证据 `a n` 递归，能过停机检查。
- `read-+≅ : (a b : Tr zero) → read (a + b) LV.≅ (read a LV.+ read b)`：read 与加法字面 ≅。
- `HS-read : (η : Tr zero) → LV.HS (read η)`：每棵第 0 层树的读回都带证书 HS。
- `cp≅ : (η : Tr zero) → tr₀ (cp η) LV.≅ read η`，`Mono-cp : (η : Tr zero) → Mono (tr₀ (cp η))`：把第 0 层树抄成 src 的树 `cp`，值不变，且满足 V2′ 目标一侧要的"极限逐项不降"。
- `code-read : (η : Tr zero) (i : IsN (h₁ η)) (o : Ok (h₁ η)) (h : LV.HS (read η)) → code (h₁ η) i o ≅ᴵ LV.toLevel (read η) h`：层号码与读回一致，对一切证明成立。
- `PEmb-≅ : ∀ {a b b′} → PEmb a b → b ≅ᴵ b′ → PEmb a b′`：前驱嵌入的目标可以换成 ≅ᴵ 的层号。
- `Uz≤ : (m : L) → U (z≤ m)`，`Ulift : (x : L) → U (self ∙ lift zero x)`：这里 `U` 指只由 inu 与 self 组成的到零路径。
- `baseLt : (m : L) (o : Ok m) (S : Base m) (j : L) (w : j ≤ m) (β : Tr⁺ j) → j ⊢ proj₁ β ◃ proj₁ (ψ m o S j w β (proj₁ (Ωt m)))`：折一棵 Ωt 严格高于底。
- `one≼` 是由覆盖条件得到"底不低于 1"的一行引理。

**第 2 段（KAsV3，无前提），W4 版第 (3) 段**
```
V3w : (η : Tr zero) (o : Ok (h₁ η)) (S : Base (h₁ η)) → Cov S → (β : Tr⁺ zero) (w : zero ≤ h₁ η) → U w
    → Σ (WT.Eb (ordᴰ (cp η)) (RV η o S β w)) (Abv (read (proj₁ β)))
```
其中 `RV η o S β w = read (proj₁ (ψ (h₁ η) o S zero w β (proj₁ (Ωt (h₁ η)))))`。

白话：对层号 h₁ η 上的一切运行（任意 Ok、覆盖的状态、任意底、只含 inu 的路径），链点的累加规范化层号 `ordᴰ (cp η)` 的前驱保序地映到 W4 折叠值的字面前驱，而且每个像都字面高于 read β。

**第 3、4 段（KAsTw，模块参数只有 `(lower : LOWERᵂ)`）**
- `Run.btboRun : NC.BTBOᴵ ≼ read (proj₁ out)`：对 tw 1 上任意一个运行都成立（运行的参数是 `(S : Base (tw 1)) (cv : Cov S) (β : Tr⁺ zero) (h1 : 𝟏 ≼ read (proj₁ β))`，`out = ψ (tw 1) o₁ S zero (z≤ (tw 1)) β (proj₁ (Ωt (tw 1)))`）。
- `Run.chainV : ∀ n → Σ ℕ (λ m → NC.γ n ≼ read (c m))`：链上的不变量只是值序。
- `Run.embL : ∀ n m → NC.γ n ≼ read (c m) → PEmb (NC.L n) (κ (c (suc m)))`：每一步的前驱嵌入。
- `tw1-low : NC.BTBOᴵ ≼ read (twᶜ 1)`：塔第 1 项本身。
- `EBO-low : NC.BTBOᴵ ≼ read EBOᶜ`
- `src-EBO-low : tr₀ Ord-Ord.BTBO ≼ read EBOᶜ`：目标定理，已发表的 BTBO 经 `BTBO≈` 换过来。

##### 3. 证法与简报纸面判断的对照

- **链。** 照先例写，不变量只带值序。每一步依次是 `PW₃ (V1 (SV-L n))`、`PW₁ (V2′ …)`、`PW₂ (HS-read …) (V3w …)`，再接 `PEmb-≅ (code-read …)` 落到下一个链点的层号码，然后用 `Ψ-emb` 与 `lower`。起点取 m = 1，因为链点 c 0 = zero。
- **后继情形。** 简报的判断成立：覆盖条件给出 Ωt H ◃ c₁，再用 `mono`、归纳假设、`Eb-suc`，整体左移一个加数（第 0 个累加项 A）。这一情形用不到归纳假设的"高于底"，因为像都形如 A + x，而底 ◃ A。
- **极限情形。** 简报的判断成立，而且比先例简单：W4 的第 n+1 个部分结果以第 n 个为底，所以不需要平移，各块直接由 `Blk.Lim` 粘起。孩子运行的状态是"进孩子后"的状态，它仍然覆盖，由 `mono` 加 `zero ◃ cum` 得到。
- **到 EBOᶜ。** 没有经过 twᶜ 1，而是把 tw 1 上的链对一切覆盖的状态、一切底 ≥ 1 写成一次。EBOᶜ 极限的第 1 项定义性地就是这样一个运行：状态 `SΛ`，底 `βΛ`，都在 KAsTw 里逐字写出。所以 `EBO-low` 直接实例化，`tw1-low` 是另一个实例。

##### 4. 没做的与限制

- **路径没有推广到一切到零的路径**，只做了只含 inu 的路径 `U w`。证明里实际用到的路径只有 `z≤ (h₁ z)` 和 `self ∙ kh z`，都满足 U，所以目标定理不受影响。没做的是 sL 层上 `inc n v` 路径的情形：那里折叠走 `cW (way …)` 的分派，其中一支折的是 `emb` 的像而不是 Ωt。我没有尝试，这不是编译出的障碍，只是范围限制（判断）。
- **LOWERᵂ 实际用到的实例比接口窄**（编译事实，见 `lowStep`、`lowG`）：
  - 层号只有 m = h₁ z（z : Tr zero）；
  - 状态是 tw 1 上某个覆盖状态的孩子分量 `λ i u → S i (inc z u)`；
  - 底只有两种：`S zero (ink self)` 或运行的底 β；
  - 路径只有 `self ∙ kh z` 或 `z≤ (h₁ z)`。

  另一路若只证这个窄版本，本结论依然成立，只需把参数类型换成窄版本（判断，没有编译窄版本）。
- `LOWERᵂ` 是否可满足由另一路负责，本路没有给实例。

##### 5. 反例

没有发现要证的命题不成立的地方。简报里的建议写法在只含 inu 的路径范围内全部编译通过。

第 2 份，转录时间戳 2026-11-25 04:45 (UTC)：

#### KJ 回报（前缀 KJ，工作目录 <实验目录>/m8，基目录 w10）

**结论：越过 BTBO 的第一步已经无前提地做成，但起点必须取 suc BTBOᴵ，不能取 BTBOᴵ。** 按简报的写法以 BTBOᴵ 起步，链停在 BTBOᴵ 不动，J BTBOᴵ 不高于 BTBOᴵ，这一点是编译出的否定（见第 3 节）。所以真正越过 BTBO 的是从 suc BTBOᴵ 起步的链，记作 J (suc BTBOᴵ)，它满足 `suc BTBOᴵ ≼ J (suc BTBOᴵ) ≼ read EBOᶜ`。

这是第四层的下界定理。树、折叠、合法性一行没改，w10 和仓库都没碰。三份文件都不带模块参数，可数层号定理用的是 `KLow.lowerW`。

##### 1. 文件

| 文件 | 行数 | 最后一次编译的退出码 |
|---|---|---|
| KJLevel.agda（Level 一侧，与 W4 无关） | 110 | 0 |
| KJRun.agda（推广 Run） | 79 | 0 |
| KJEbo.agda（接到闭项） | 86 | 0 |

- 最后一次是删掉 m8 里的 .agdai 之后冷编 KJEbo，日志里只有三个 KJ 模块的 Checking 行。堆上限 6G，用时不到一分钟。
- 选项行逐字照公共约束。
- 检查过：没有 postulate、洞、停机或正性编译指示，也没用函数外延。

##### 2. 编译定理（陈述逐字抄出）

**KJLevel：Level 一侧**

- `module Chain (y : T₀) (hy : HS y) (sy : St y) (py : Psv (toLevel y hy))`
  - 白话：从带证书的树 y 起步的链。
  - 链：`δ 0 = y`，`δ (n+1) = ψ⁰ (Ω (toLevel (δ n) _))`，证书由 `Uniform` 给出。
  - 极限：`J = LV.lim (λ n → ψ⁰ (Ω (Lδ n)))`。
  - 附带：`SV-δ : ∀ m → SV (Lδ m)`，`St-δ : ∀ m → St (δ m)`，`bk≅δ : ∀ m → tr₀ (bkᴵ (Lδ m)) LV.≅ δ m`，`δ≼J : ∀ n → δ (suc n) ≼ J`。照 `SV-L`、`St-γ`、`bk≅γ` 对一般的树重写。
- `γ≺ : ∀ n → NC.γ n LV.≺ NC.γ (suc n)`：参照链字面严格上升。
- `St-BTBO : St NC.BTBOᴵ`：由此 BTBOᴵ 可以作起点（证书用 `NC.BTBO-HS`）。
- `JB₁≼ : JB.δ 1 ≼ NC.BTBOᴵ`：从 BTBOᴵ 起步的第 1 项不高于 BTBOᴵ（`JB = Chain NC.BTBOᴵ NC.BTBO-HS St-BTBO plv`）。
- `JB-tail : ∀ k → JB.δ (suc k) LV.≅ LV.lim (λ n → NC.γ (sh (suc k) n))`：这条链的每一项都结构互模拟于 γ 某段尾巴的极限。
- `JB≼ : JB.J ≼ NC.BTBOᴵ`
- `no-sJB : ¬ (LV.suc NC.BTBOᴵ ≼ JB.J)`：简报第 1 项的强形式不成立（见第 3 节）。
- `sBTBO≼JS₁ : LV.suc NC.BTBOᴵ ≼ JS.δ 1`：从 suc BTBOᴵ 起步，第 1 项 ψ⁰(Ω_{BTBO+1}) 已经严格越过 BTBOᴵ（`JS = Chain (LV.suc NC.BTBOᴵ) (LV.hs NC.BTBO-HS) (sts St-BTBO) psv`）。
- `sBTBO≼JS : LV.suc NC.BTBOᴵ ≼ JS.J`

**KJRun：W4 一侧**

在 `module RunJ (S : Base (tw 1)) (cv : Cov S) (β : Tr⁺ zero) (h1 : 𝟏 ≼ read (proj₁ β))` 里，先 `open As.Run … public`，然后：

- `embJ : ∀ n m → C.δ n ≼ read (c m) → PEmb (C.Lδ n) (κ (c (suc m)))`
- `chainJ : (m₀ : ℕ) → y ≼ read (c m₀) → ∀ n → Σ ℕ (λ m → C.δ n ≼ read (c m))`
- `Jrun : (m₀ : ℕ) → y ≼ read (c m₀) → C.J ≼ read (proj₁ out)`
  - 白话：tw 1 上任一覆盖的运行，只要起点 y 不高于某个链点，J y 就不高于输出。证法照搬 `embL`/`chainV`，把 γ、L 换成 δ、Lδ。
- `β′≺c₁ : read (proj₁ β′) LV.≺ read (c 1)`：第 1 个链点严格高于状态的第 0 层条目 β′。
- `J-x : … → x ≼ read (proj₁ β′) → Chain.J x hx sx px ≼ read (proj₁ out)`
- `J-sx : … → x ≼ read (proj₁ β′) → Chain.J (LV.suc x) hx sx px ≼ read (proj₁ out)`
  - 白话：β′ 不低于 x 时，从 x 起步和从 suc x 起步的极限都不高于输出。

**KJEbo：接到闭项**

- 那个运行：`S₂ i u = B₂ i (inc zero u)`，它覆盖（`cv₂ : Cov S₂`）；底是 v₁，`h1₂ : 𝟏 ≼ read (proj₁ v₁)`。
- `entry-shape : proj₁ (S₂ zero (ink self)) ≡ proj₁ (β″ ⊞ tw1⁺)`（refl）：第 0 层条目由回退行算出，是 β″ 右边接上塔第 1 项从头折的值（`tw1⁺ = ψ₀ (tw 1) (Ok-tw 1) (proj₁ (Ωt (tw 1)))`）。
- `tail≼ : (a b : Tr⁺ zero) → read (proj₁ b) ≼ read (proj₁ (a ⊞ b))`
- `entry≥ : NC.BTBOᴵ ≼ read (proj₁ (S₂ zero (ink self)))`：由 `KBtbo.tw1-lower` 得到。
- `out≼EBO : read (proj₁ R₂.out) ≼ read EBOᶜ`：这个运行的输出是 real₂ 的第 0 个累加项，而 real₂ 是 EBOᶜ 的第 2 项。
- `JB-EBO : JB.J ≼ read EBOᶜ`：简报字面要的定理，但它的内容不超过 BTBOᴵ。
- `JS-EBO : JS.J ≼ read EBOᶜ`：从 suc BTBOᴵ 起步的链的极限不高于 EBOᶜ。
- `sBTBO-EBO : LV.suc NC.BTBOᴵ ≼ read EBOᶜ`：EBOᶜ 严格高于 BTBOᴵ。

##### 3. 不成立的命题（编译反例）

- 简报第 1 项的 "`suc BTBOᴵ ≼ J BTBOᴵ`" 不成立：`no-sJB`。
- 机制：`toLevel BTBOᴵ BTBO-HS` 定义性地等于 `lim (L ∘ suc)`，所以 `ψ⁰(Ω (toLevel BTBOᴵ …))` 字面上就是 `lim (γ ∘ suc ∘ suc)`。BTBOᴵ 正是 z ↦ ψ⁰(Ω_z) 的不动点。往后每一项都 ≅ γ 的一段尾巴的极限（`JB-tail`）。
- 弱形式 "`BTBOᴵ ≼ J BTBOᴵ` 且第 1 项出现在其中" 是成立的，但没有新内容。
- 出路：W4 一侧的第 1 个链点是 β′ 之上的 next⁺，严格高于 β′（`β′≺c₁`）。所以链可以直接从 suc x 起步（`J-sx`），越过 BTBO 用的是这一条。

##### 4. 没做的

**第 4 项（塔第 n+2 项不低于 J 迭代 n+1 次）没有做。** 下面是判断，没有编译：
- 塔第 n+2 项在孩子 zero 里的运行，层号是 tw (n+1)。
- 当 n ≥ 1 时，它的链点所在层号 `tw n ⊕ ↑ (tw n) c` 含 Ω 形结点，不满足 `IsS`，`LOWERᵂ` 用不上。
- 所以要另一条引理：含 Ω 形结点的层号上的镜像下界，也就是 `LOWERᵂ` 在 tw (n+1) 一类层号上的推广。
- 本文的 `Chain`、`RunJ` 部分对起点是一般的，不需要再改。

##### 5. J (suc BTBOᴵ) 按原记号大概是什么（估计，未核）

- 层号 `toLevel BTBOᴵ` 的基本列逐项是 γ 各项的层号，与 EBO 里 Ω_Ω[n] = Ω_{γ_n} 同形。所以按基本列来读，它扮演 EBO 里下标 Ω (=Ω₁) 的角色。
- 照这个读法，第 1 项 ψ⁰(Ω_{BTBO+1}) 大约对应 ψ₀(Ω_{Ω+1})，J (suc BTBOᴵ) 在它之上，是 z ↦ ψ⁰(Ω_z) 在 BTBO 之后的下一个不动点。
- 精确位置没有算。按集合 C 的标准定义，ψ₀(Ω_{BTBO+1}) 会退化回 BTBO，所以这个读法只在基本列的意义下才有意义。
