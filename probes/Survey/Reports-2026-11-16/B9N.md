# B9N：整棵 Y 1 在一次更新处（Opus 5.5，外部主审第九批）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-18 06:49 至 07:27 |
| 工具调用 / agda 编译 (粗数) | 44 / 10 |
| token (usage 字段，按消息去重) | 输出 228487；新写入缓存的输入 689085；读缓存的输入 9079181；其余输入 82 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `B9Upper` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | First 未判定；编译无前提：W4 一侧对一切阶的上界关系 𝓤 n（B9UpperRel，与 WSW4 同形、方向相反），out1-up : out 1 ≼ Ŝ（Ŝ 只由第 0 层影子算术构成），sandwich（ψ⁰ X₀ ≼ out 1 ≼ Ŝ），正对照 out0-cross 复得 B8N 的初态精确界；条件否定 no-first-if / no-goal-add-if / no-first-from-Gap′，所缺的 Gap′ : suc Ŝ ≼ ψ⁰ (Y 1) 是不含 W4 的 Level–影子不等式，开放；执行方判断 Gap 成立、First 为假（纸面），估反向 Level 理论 600–900 行；协调者私有目录只复制源码 6G 冷编退出 0，三个新模块各有 Checking 行，附件 attachments/B9N-* |

## 简报原文

本批实验目录 B9_RUN = <临时目录> （公共目录已按协调简报准备并冷编：$B9_RUN/common 里 WKAll、WSMain、YiLAB8Split 均退出 0，B8 与 YiLAB9Orbit 模块都已检查；库文件 $B9_RUN/libraries）。在每条 shell 命令前先 export B9_RUN=<临时目录> probes/Survey/Lead/第九批/ 为基准。你的最终消息就是回报原文，会逐字留档。

以下为简报全文（原样）：

### B9N · 整棵 Y 1 在一次更新处是否已经成立

请独立检验 `First = Match (Y 1) (chainW 1)`，与 B9A 保持同一参照。全程中文，模型 Opus 5.5。先读仓库根 `AGENTS.md`、工程手册 §4 及[主审指令 02](../Lead/指令-02.md)。协调者提供公共目录；独立收到本简报时可先运行[公共准备段](../Lead/第九批/00-协调简报.md)。在 `$B9_RUN/B9N` 写纯 Agda，新模块前缀 `B9Upper`。

**首试交付 `no-first : First → ⊥`，也接受带两个消费者闭实例的 `first : First`。** 第八批否定了冻结初态。主审补证的是较小参照 `X₀` 在一次更新处成立而在初态不成立。`B8PairMain.no-merge` 只排除一个描述，尚没有关于整个 `First` 的否定。

1. 以 `YiLAB8Split.out 1` 为右端。先试 `out 1 ≼ LV.ψ⁰ X₀`。现有 `B8PairMain.c-add₀` 给反向；若上界成立，配合 `B8PairMain.X₀≺Y1`，用已编译的 `refute-at {X = Y 1} {n = 1}` 即可否定所有允许的共同描述。B8N 的 `fold-up` 只管初态；请从 `chainW1-shape` 展开本次更新的累加与 `ex`，核对上界是否真的保持。初态的精确上界可作基例。
2. 可以更换上界 H。所需的两条是 `out 1 ≼ H` 与 `LV.suc H ≼ LV.ψ⁰ (Y 1)`，同一 H 且前提可满足。`B8FreezeMain.Y1-big` 可帮助在 Level 一侧挑选阈值。另一种写法可直接反驳同一个闭消费者目标。若编出 `First` 正例，交四个字段和两个出口，记录是哪一步推翻了上界判断。
3. 对一份描述的逐点比较失败，不排除别的描述；指数消费亦不能由被加项消费者的否定自动判断。若两种写法都受阻，列出最后已编译的具体上界、尚缺的上界保持行、它实际经过的 W4 参数以及一个非空实例。先纸面后编译，每路新代码约 1200 行，可换一次写法。对第九批整条路线的裁定交主审。

在仓库根执行，按入口实名替换文件名：

```sh
agda +RTS -M6G -RTS --library-file="$B9_RUN/libraries" -i src -i probes -i "$B9_RUN/common" -i "$B9_RUN/B9N" "$B9_RUN/B9N/B9UpperMain.agda" > "$B9_RUN/B9N/compile.log" 2>&1
code=$?
echo "agda exit $code"
```

沿用公共 OPTIONS，一次一个 Agda；仓库、W4、公共源码只读。第 4 层若有经典条件，必须作参数并标明具体用途。回报列签名、量化域、前提与实例、源码、冷编退出码和仍开放的命题。把结果交给协调者复核，无须等待构造路。

## 回报原文

### B9N 回报：整棵 Y 1 在一次更新处

#### 结论

`First` 没有判定，`no-first` 和 `first` 都没有交出。我把 `First → ⊥` 归约成一个不含 W4 的闭不等式：

- **W4 一侧已编译，无前提。** 我得到 `out 1 ≼ Ŝ`。`Ŝ` 是只用第 0 层影子算术写成的闭项（影子：第 0 层上的函数，用来跟踪 W4 运算的值），不含 W4 的树、折叠和状态。和 B8A 合起来是夹逼 `ψ⁰ X₀ ≼ out 1 ≼ Ŝ`。
- **还缺的一步全在 Level 与影子之间。** 只要证出 `Gap′ : LV.suc Ŝ ≼ LV.ψ⁰ (Y 1)`，`First → ⊥` 与 `Goal-add → ⊥` 就成立。这两个条件定理已编译。
- B8N 当时说卡在 "W4 的 E、It 在第 1 层指数上各阶的一套上界理论，与 B6A 方向相反"。这套理论这次编出来了，约 440 行，和下界版 WSW4 同形。
- **对纲领与目标：** 这是第 4 层（值验收）的结果，不改 W4 定义，不涉及记号，没有用排中律或函数外延。

#### 编译定理（全部 `--safe --without-K`，无前提）

**B9UpperRel：上界逻辑关系 `𝓤 n`**（"这个 op 的值不超过这个影子"），对一切阶 n 成立。

- 量化域：一切语境 `X : Cx lvl1`、一切状态 S、一切点 t、一切输入 v。前提只有两条：`read v ≼ a`，以及状态在链点的读回 `rd S ch ≼ c`。高阶只对 Good 延伸（与 WSW4 相同）。
- 各行：`U-sh`、`U-limC`、`U-enter`、`U-node`、`U-up`。`U-node` 对 nodeC 与 E 的 Ω 行，影子 `nodeU` 的链从 0 起、输出逐项累加；`U-up` 对 upC，影子 `compU` 是两段复合。
- 第 0 层指数：`Lem.L0E`、`Lem.L0I`。
- 指数实现 `RealE` / `RealI`：
  - `Real-zero`
  - `Rsuc : Real x e → Real (suc x) (sC e)`
  - `U1 : Real Ω₁t Ω̂U`
  - `U2 : Real x e → Real (ex Ω₁t Ω₁t nbΩ (suc x) tt) (shU e)`

**B9UpperTop：本次更新的累加与 ex 行**（按 `chainW1-shape` 展开）

- `brA`、`preΩ : … → read (ψ … (a + Ω₁t)) ≼ fΩ A A′`
- `opΩ : 𝓤 0 {nil} (inc tt self) (opB lvl1 o Ω₁t nbΩ) fΩ`
- `topB`（ex 行），`eU`，`RzW : (m : ℕ) → Real (zW m) (eU m)`
- `Bok : (n : ℕ) → read (proj₁ (ψ lvl1 o (B₀ lvl1) zero (inc tt self) (Ωt zero) (cum Fz n))) ≼ Bnd n`
- `out1-up : out 1 ≼ Ŝ`，其中 `Ŝ = LV.lim Bnd`

**B9UpperMain：入口**

- `sandwich : (LV.ψ⁰ X₀ ≼ out 1) × (out 1 ≼ Ŝ)`
- 两个待证闭命题：
  - `Gap = Ŝ ≼ LV.ψ⁰ X₀`
  - `Gap′ = LV.suc Ŝ ≼ LV.ψ⁰ (Y 1)`
  - 二者关系：`Gap→Gap′`（经 `X₀≺Y1`）
- 逐项形式：`Gap-from-terms : (∀ n → Bnd n ≼ LV.ψ⁰ (ψ₁ (γ n))) → Gap`，以及 `terms-Gap`
- 若 Gap 成立则三者同值：`Gap→val : Gap → out 1 ≈ᵛ LV.ψ⁰ X₀`
- 条件否定：
  - `no-first-if : (H : T₀) → Ŝ ≼ H → LV.suc H ≼ LV.ψ⁰ (Y 1) → First → ⊥`（经已编译的 `refute-at {X = Y 1} {n = 1}`）
  - `no-goal-add-if`：同样两个前提，对闭消费者目标 `Goal-add`
  - `no-first-from-Gap`、`no-first-from-Gap′`
- 正对照：`out0-cross : out 0 ≼ Pε`（经 `out0-up : out 0 ≼ fΩ 𝟏 𝟏` 与 `fΩ-1 : fΩ 𝟏 𝟏 ≼ Pε`）。同一套上界理论在初态重新得出 B8N 的精确界 `fold-up`，说明它在第 0 阶不松。

**前提与实例。** `out1-up` 与 `sandwich` 无前提。`no-first-if` 的第一个前提有实例 H = Ŝ（`≼-refl`）；第二个前提就是开放的 Gap′，没有实例。

#### 实际经过的 W4 参数与行

- **第 1 层 ψ**（目标 0，路径 `inc tt self`，β = `Ωt zero`，底族 `B₀ lvl1`）：
  - lim 行：`chainW 1 = lim (cum Fz)`。
  - ex 行：E 用 tdNil、`opB lvl1 o Ω₁t nbΩ`，状态取 `λ i u → ψ … a`。
  - 累加项：第 0 项 a = `Ω₁t`；第 n+1 项 a = `cum Fz n + Ω₁t`，指数 `suc (zW (n+1))`。
  - Ω 行：kp 给 nothing，链点在 `posW lvl1 p₁ = inc tt self`。
  - up 行：inc 与 inu 两种路径都走过。
  - 第 0 层 suc / lim：经 `P-up`。
- **E**：zero、suc（itV 与 itS 两轨同步）、Ω（kpT）、up（chTD、enterO）、ex（It 0 与 Kb）。
- **It n**：zero、suc（limC）、Ω（nodeC）、up（upC，A = `It n zero K G`，R 为孩子语境里的 It 与 `enter (Itᴺ …)`）、ex（`It (suc n)`、Kₑ、Itᴺ）。
- **语境搬运**：enter、chM、liftM、Good。

W4 一侧需要的上界保持行都已编译，没有缺的。

#### 仍开放的命题

开放的是 **Gap′**（足以推出 `First → ⊥`），以及更强的 Gap（它还会推出 `out 1 ≈ᵛ ψ⁰ X₀`）。

**纸面判断（不是定理）。**
- `Bnd n` 对应 ψ₀ 作用在第 n 个累加项上，该项约为 Ω·ω^{z_n+1} = z_{n+1}。
- 由 z_n < γ_n 可得 z_{n+1} < γ_{n+1}。所以 `Bnd n ≲ ψ⁰ (ψ₁ (γ n))`，Ŝ 约为 ψ₀(Ω₂)，与 ψ⁰ X₀ 同一量级。
- 累加、compU、链起点 0 对 1、分支 `lv (suc y)` 对 `lv y`，这几处差异都只差有限步，在对角里被吸收。
- 另一方面 ψ⁰(Y 1) ≥ ψ⁰(ψ₁Ω₂ + ψ₁Ω₂)（`Y1-big`，读作 ψ₀(Ω₂·2)），所以 Gap′ 有较大余量。
- 据此我判断 First 不成立。这仍是判断，不能写成路线已否定。

**为什么没有编出来（第二种写法的位置）。** Gap′ 需要反向的 Level 理论，即 "Level 的 ψ⁰ 不低于影子"，方向与 WSLevel 相反。我核到的必经难点有三处：

1. Level 的 ψ⁰ 对 ≼ 不单调（`Value.ψ⁰-not-cong`）。需要一个结构序 ⊴：limᵢ 的分支族对参数单调，并证 ψ⁰ 沿 ⊴ 单调。
2. ψ₁ 产生右结合的和，影子语义按前缀从右边接上。两者要靠 + 的结合律接起来；不用函数外延时，只能在 ⊴ 或值的层面做。
3. 上界结点的累加和 upC 的复合要被吸收。这需要影子在各阶单调，或者 Level 一侧的倍增性质；对一般的 k，复合没有通用的界。

我估计这部分要 600 到 900 行，超出本路剩余预算，所以没有开写。

**我建议作为下一路首交的最小未证签名**（纸面成立）：`∀ n → Bnd n ≼ LV.ψ⁰ (ψ₁ (γ n))`。它经 `Gap-from-terms` 与 `no-first-from-Gap` 直接给出 `First → ⊥`。

#### 源码与编译

- 文件（共 526 行，前缀 B9Upper）：
  - `<临时目录>`（335 行）
  - `<临时目录>`（108 行）
  - `<临时目录>`（83 行，入口）
- 冷编：先删掉本路的 .agdai，再按简报原命令在仓库根编译入口 B9UpperMain，6G 堆，退出码 0（不经管道），约 8 秒。日志 `<临时目录>` 里三个模块各有自己的 Checking 行。
- OPTIONS 与公共目录一致。扫描结果：没有 postulate、洞、停机或其他编译指示（只有 OPTIONS 一行），没有本机路径，没有经典参数，没有 Funext。
- 依赖只有公共目录（W4Block/Ops/Path/Fold、WVOne、WSShadow、WSW4 的 Good、WSLevel 的 ψ₁ 与 γ、B8FreezeMain、B8PairW4、B8PairLevel、B8PairMain、YiLAB7Orbit、YiLAB7Replay、YiLAB8Split）与仓库的 `OCF.Align.Level` / `OCF.Align.Value`。仓库、W4 与公共源码都没有改动。

#### 交协调者复核

请从源码冷编，重点核三处：
- `out1-up` 的左端就是 `YiLAB8Split.out 1`，按定义一致；
- `no-first-if` 调用的是原 `refute-at`；
- `out0-cross` 与 B8N 的 `fold-up` 是同一个目标。

对第九批整条路线的裁定交主审。

## 派发消息正文（简报全文原样，本机路径换成占位）

本批实验目录 B9_RUN = <B9_RUN> （公共目录已按协调简报准备并冷编：$B9_RUN/common 里 WKAll、WSMain、YiLAB8Split 均退出 0，B8 与 YiLAB9Orbit 模块都已检查；库文件 $B9_RUN/libraries）。在每条 shell 命令前先 export B9_RUN=<B9_RUN>。简报里的相对链接以 probes/Survey/Lead/第九批/ 为基准。你的最终消息就是回报原文，会逐字留档。

以下为简报全文（原样）：

## B9N · 整棵 Y 1 在一次更新处是否已经成立

请独立检验 `First = Match (Y 1) (chainW 1)`，与 B9A 保持同一参照。全程中文，模型 Opus 5.5。先读仓库根 `AGENTS.md`、工程手册 §4 及[主审指令 02](../Lead/指令-02.md)。协调者提供公共目录；独立收到本简报时可先运行[公共准备段](../Lead/第九批/00-协调简报.md)。在 `$B9_RUN/B9N` 写纯 Agda，新模块前缀 `B9Upper`。

**首试交付 `no-first : First → ⊥`，也接受带两个消费者闭实例的 `first : First`。** 第八批否定了冻结初态。主审补证的是较小参照 `X₀` 在一次更新处成立而在初态不成立。`B8PairMain.no-merge` 只排除一个描述，尚没有关于整个 `First` 的否定。

1. 以 `YiLAB8Split.out 1` 为右端。先试 `out 1 ≼ LV.ψ⁰ X₀`。现有 `B8PairMain.c-add₀` 给反向；若上界成立，配合 `B8PairMain.X₀≺Y1`，用已编译的 `refute-at {X = Y 1} {n = 1}` 即可否定所有允许的共同描述。B8N 的 `fold-up` 只管初态；请从 `chainW1-shape` 展开本次更新的累加与 `ex`，核对上界是否真的保持。初态的精确上界可作基例。
2. 可以更换上界 H。所需的两条是 `out 1 ≼ H` 与 `LV.suc H ≼ LV.ψ⁰ (Y 1)`，同一 H 且前提可满足。`B8FreezeMain.Y1-big` 可帮助在 Level 一侧挑选阈值。另一种写法可直接反驳同一个闭消费者目标。若编出 `First` 正例，交四个字段和两个出口，记录是哪一步推翻了上界判断。
3. 对一份描述的逐点比较失败，不排除别的描述；指数消费亦不能由被加项消费者的否定自动判断。若两种写法都受阻，列出最后已编译的具体上界、尚缺的上界保持行、它实际经过的 W4 参数以及一个非空实例。先纸面后编译，每路新代码约 1200 行，可换一次写法。对第九批整条路线的裁定交主审。

在仓库根执行，按入口实名替换文件名：

```sh
agda +RTS -M6G -RTS --library-file="$B9_RUN/libraries" -i src -i probes -i "$B9_RUN/common" -i "$B9_RUN/B9N" "$B9_RUN/B9N/B9UpperMain.agda" > "$B9_RUN/B9N/compile.log" 2>&1
code=$?
echo "agda exit $code"
```

沿用公共 OPTIONS，一次一个 Agda；仓库、W4、公共源码只读。第 4 层若有经典条件，必须作参数并标明具体用途。回报列签名、量化域、前提与实例、源码、冷编退出码和仍开放的命题。把结果交给协调者复核，无须等待构造路。
