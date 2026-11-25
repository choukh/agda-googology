# M5：把可数层号定理接到 BTBO 下界（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-24 16:42 至 16:58 |
| 工具调用 / agda 编译 (粗数) | 52 / 2 |
| token (usage 字段，按消息去重) | 输出 84686；新写入缓存的输入 263745；读缓存的输入 8415825；其余输入 84 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `KAs` (在 `<实验目录>/m5/`) |
| 主审复核后的一句结论 | 完成：src-EBO-low : tr₀ Ord-Ord.BTBO ≼ read EBOᶜ 编译，模块参数只有 lower : LOWERᵂ；W4 版第三段 V3w（对一切覆盖的运行，像字面地高于底）无前提；路径只做了只含 inu 的（目标定理用到的都是）。主审另目录冷编复核，禁用构造 0；再用 KLow.lowerW 填上参数得 KBtbo.btbo-lower : tr₀ Ord-Ord.BTBO ≼ read EBOᶜ，无模块参数；全链 29 个模块在新目录从头编译退出 0（6G 堆上限，常驻峰值 1.80G，46 秒）；各模块与留档附件逐字节相同，W4 与 WV 模块与 11-16 的附件逐字节相同。附件 attachments/M5-KAs*.agda.txt、KBtbo.agda.txt、M5-简报-M5.md |

## 简报原文

你的任务简报全文在这个文件里，请先完整读它，再严格照做（它是自足的，背景、任务、约束、回报格式都在里面，其中第一步是读公共约束文件）：

<实验目录>/briefs/M5.md

要点提示（以简报为准）：这是一个 Agda 形式化任务（--safe --without-K）。以已编译的接口陈述 KLowIface.LOWERᵂ（可数层号上 W4 的折叠不低于参照系统在镜像码上的折叠）为唯一的模块参数，证 tr₀ Ord-Ord.BTBO ≼ read EBOᶜ。做法照搬仓库里旧主线的先例（probes/Survey/RR7-BtboLower.md，probes/OCF/Lean/YiBtboLower.lagda.md 与 YiBtboV2.lagda.md）：链上只带值序，每步造到下一个链点层号码的前驱嵌入；其中与块无关的两段可以直接导入，第三段（链点的规范化层号嵌进 W4 折叠值的字面前驱）要写 W4 版，简报里给了推广到一切运行的建议写法（是纸面判断，不成立就照实报）。共享基目录是 scratchpad/w5（不是 w4）。只在你的工作目录 <实验目录>/m5 里写，模块前缀 KAs；不改仓库、W4 与共享基目录里的任何文件；同时只跑一个 agda，堆上限 6G；不提交。做不完时把没证的部分写成带确切陈述的模块参数，使文件整体编译。你的最终消息就是回报原文，中文，按公共约束里的回报格式。

## 回报原文

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
