# B9A：第二次更新承载整棵 Y 1（Opus 5.5，外部主审第九批）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-18 06:49 至 07:04 |
| 工具调用 / agda 编译 (粗数) | 38 / 8 |
| token (usage 字段，按消息去重) | 输出 80642；新写入缓存的输入 226446；读缓存的输入 4975834；其余输入 62 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `B9Inner` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | second : Second（= Match (Y 1) (chainW 2)）编译，无前提，无排中律、函数外延：second = to-second at1，at1 用第二次更新的累加分支 U 1 与 B8PairLevel 的规范描述 (dY1, eY1)；at-suc 覆盖一切 k ≥ 1；两个消费者闭不等式 add-2、exp-2（及 U 1 上的 add-U1、exp-U1）；外层下界 outer : ψ⁰ (body (Y 1)) ≼ read Ψ₃（经原始内链 z 2 的 match-z2，底族为一次更新后的状态）；新一般行 RealX、Real-pos（执行方判断 RealX 是同一条 ex 行引理第三次以不同名字出现）；协调者私有目录只复制源码 6G 冷编退出 0，五个新模块各有 Checking 行，附件 attachments/B9A-* |

## 简报原文

本批实验目录 B9_RUN = <临时目录> （公共目录已按协调简报准备并冷编：$B9_RUN/common 里 WKAll、WSMain、YiLAB8Split 均退出 0，B8 与 YiLAB9Orbit 模块都已检查；库文件 $B9_RUN/libraries）。在每条 shell 命令前先 export B9_RUN=<临时目录> probes/Survey/Lead/第九批/ 为基准。你的最终消息就是回报原文，会逐字留档。

以下为简报全文（原样）：

### B9A · 第二次更新能否承载整棵 Y 1

请独立完成 W4 的第 4 层值证明，全程中文，模型 Opus 5.5。先读仓库根 `AGENTS.md`、工程手册 §4 及[主审指令 02](../Lead/指令-02.md)。公共目录由协调者给出；独立收到本简报时可先运行[公共准备段](../Lead/第九批/00-协调简报.md)。在 `$B9_RUN/B9A` 写纯 Agda，新模块前缀 `B9Inner`。

**首交目标是 `second : Second`。** `YiLAB8Split.Second = Match (Y 1) (chainW 2)`。这要求整棵非初始 Level 链点与两次更新后的 W4 树共同满足被加项、指数的四个字段。第八批只在较小的 `X₀` 上得到配对。主审已证初态无法承载 `X₀`，本路继续向上取整棵 `Y 1`。

1. 优先试 `at1 : AtPart 1`，用 `to-second at1` 交付。`AtPart k` 使用的是第二次更新的实际**累加分支** `YiLAB9Orbit.U k`。记一次更新的状态为 c；`second-part` 给出 `U 1 ≡ ex (z 1 + c) c nc (suc (z 1)) tt`。`inner-seed` 已把 `X₀` 接到 `U 0`。先明确消费 c 的哪一处、指数的哪一处；若使用原始内链 `z 2`，补证其界到累加分支的传递。
2. `B8PairLevel.Ld-Y1/Lx-Y1` 给已满足 Level 字段的具体描述。`B8PairW4.Real-c1` 给 c 的指数描述 `lC ε = eΩ₂`，`SumR-c1` 与 `B8PairMain.shift-d` 可把 c 的被加项描述收窄到 `dΩ₂`。先试以 W4 侧的 `ex`、前缀或语义膨胀律合成同一对描述；若换描述，说明两个方向的比较。第八批 `no-merge` 否定的是一次更新的一对具体描述，本题的右端不同。
3. 如 `U 1` 太小或难以消费，可由计算选有依据的其他 k，再经 `part k` 提升；也可对整个极限给值界。不要把“在一支找齐四个字段”升格成必要条件。取得 `second` 后，分别编译 `consume second`、`consume-exp second` 对应的闭不等式，写清左右端。若有余量，优先把一个实际非初始分支接到 `LV.ψ⁰ (body (Y 1)) ≼ read WKShape.Ψ₃`，说明底族和路径；这是单独的外层目标。
4. 第二种写法可直接证明整棵 `Y 1` 在两次更新处的一个闭消费者值界。若只完成这一条，按这一条回报。任何否定也须对准签名，并给已满足的前提。新代码约 1200 行、可换一次写法；触顶或两种写法受阻时交最小未证签名与最后一个已编译实例。

在仓库根执行，按入口实名替换文件名：

```sh
agda +RTS -M6G -RTS --library-file="$B9_RUN/libraries" -i src -i probes -i "$B9_RUN/common" -i "$B9_RUN/B9A" "$B9_RUN/B9A/B9InnerMain.agda" > "$B9_RUN/B9A/compile.log" 2>&1
code=$?
echo "agda exit $code"
```

沿用公共 OPTIONS，一次一个 Agda；仓库、W4、公共源码只读。第 4 层若使用排中律或函数外延，标明条件及给出见证的具体步骤。回报按闭项、值界、否定、纸面判断分开写，列出新模块、每个分支编号、出口、退出码与依赖。源码和回报交协调者，无须等待对照路。

## 回报原文

### B9A 回报：第二次更新承载整棵 Y 1

#### 结论

第二次更新能承载整棵 `Y 1`。`second : Second` 已经编译出来，用的是 `AtPart 1` 加 `to-second`，没有前提，也没有用排中律或函数外延。描述对用的就是 B8PairLevel 的规范描述 `(dY1, eY1)`，没有换描述，所以不需要补两个方向的比较。余量部分另外得到一个外层下界 `ψ⁰ (body (Y 1)) ≼ read Ψ₃`。这些都是第 4 层（值验收）的结果，没有新增或改动任何树侧定义；它们说明配对接口可以消费 W4 的实际输出，不涉及“树自足”。

如果 B9N 否定了 `First`，按主审指令 02 的判据，这条轨道上整棵 `Y 1` 首次能以该接口配对的更新次数就是 2。如果 `First` 成立，首次次数是 1。

#### 新模块

都在 `$B9_RUN/B9A`，纯 `.agda`，选项沿用公共 OPTIONS（`--safe --without-K`）。共 359 行。

| 模块 | 行数 | 内容 |
|---|---|---|
| `B9InnerReal` | 63 | 指数实现 `Real` 的两条一般行：`Real-pos`、`RealX`，另有组合子 `exE` 和放宽 `Real-w` |
| `B9InnerSecond` | 101 | `at1`、`second`、`at-suc`，以及两个消费者的四条闭不等式 |
| `B9InnerLevel2` | 55 | `ψ≼ψ⁰`、`L2u`、`L2-sem`、`body-Y1` |
| `B9InnerOuter` | 96 | `match-z2`、`outer` |
| `B9InnerMain` | 44 | 入口，转出 `second`、`at1`、`at-suc`、`add-2`、`exp-2`、`outer` |

- **退出码：** 按简报命令编译 `B9InnerMain`，退出 0，日志在 `$B9_RUN/B9A/compile.log`。另外把公共源码和本路源码复制到私有目录（无 `.agdai`）冷编入口，也是退出 0，且每个新模块和所依赖的公共模块都有自己的 Checking 行。
- **扫描：** 新模块里没有 `postulate`、洞，除 OPTIONS 外没有编译指示，没有本机路径，也没有经典参数。
- **依赖：**
  - 公共目录：W4Block、W4Ops、W4Path、W4Fold、WSShadow、WSW4、WKSum、WSLevel、WVOne、WVTwo、WVThree、WKGen、WKShape、YiLAB7Orbit、YiLAB7Replay、B8PairLevel、B8PairW4、B8PairMain、YiLAB8Split、YiLAB9Orbit。
  - 仓库：OCF.Align.Level、OCF.Align.Value、OCF.BTBO（只用 `Ord-Ord` 和 `injᵃ`、`injᵇ`、`injᶜ`）。
  - 全部属于值验收侧。

#### 1. 闭项

无新闭项，也没有改动 W4、公共源码或仓库文件。

#### 2. 值界（都是编译过的定理，无前提）

##### 2.1 第二次更新的配对

用的分支是 `U 1`，即第二次更新所产极限的第 1 号累加分支（`◃l 1`）。由 `second-part`，`U 1` 定义上等于 `ex (z 1 + c) c nc (suc (z 1)) tt`。

- **`at1 : AtPart 1`**，写作 `together dY1 eY1 SumR-U1 Real-U1 Ld-Y1 Lx-Y1`。四个字段在同一对描述上：
  - `SumR (U 1) dY1`
  - `Real (U 1) eY1`
  - `Ld (Y 1) dY1`
  - `Lx (Y 1) eY1`
- **`second = to-second at1 : Second`**，即 `Match (Y 1) (chainW 2)`。
- **`at-suc : ∀ k → AtPart (suc k)`**：由 `U k ◃ U (k+1)`（W4 的 `+-mono`）和 `Match-up` 得到，覆盖所有 k ≥ 1。

**c 和指数各自在哪里被消费**（简报第 1 项）：

- **指数 `suc (z 1)`：** `z 1 = ex c c nc (suc 0)` 实现 `eΩ₂ ⨾ Ω̂`，即 Ω₂ + Ω₁ 的影子。
  - 前一个 c（ex 的 a 位）当 Ω₂ 用，即 `Real-c1 : Real c (lC ε)`。
  - 后一个 c（b 位）当 Ω₁ 用，由 `Real-up (chain-step 0) W1` 得到。
  - 指数 `suc 0` 只用正性。
- **`U 1` 本身：**
  - 底 c 当 Ω₁ 用。指数侧是 `Ω̂`；被加项侧是 `Nx`，由 `SumR-c1` 按 `Nx ≤ d₁` 放宽而来。
  - 前缀 `z 1 + c` 只用正性：指数侧用 `Real-pos`，被加项侧用 `baseInfl`。
- **定义上的一致：** `RealX` 给出的影子 `exE zC Ω̂ (eΩ₂ ⨾ Ω̂)` 与 `eY1 = sh (eΩ₂ ⨾ Ω̂)` 定义上相同；`SumR-x` 给出的被加项影子就是 `dY1`。
- **没有用到收窄到 `dΩ₂` 的 `shift-d`。**
- **原始内链 `z 2`** 只在外层目标里使用，见 2.2；两种用法分开写在不同定理里。

**两个新一般行：**

- `Real-pos : zero ◃ a → Real a zC`，只用 W4 的 `Emono` 和 `Itmono`。
- `RealX : Real a ea → Real b eb → Real x ex → Real (ex a b nb x tt) (exE ea eb ex)`，其中 `sE (exE ea eb ex) f = sI ex 0 (sE eb) (sE ea f)`。

**消费者的闭不等式**（左端是 Level 参照，右端是 W4 实际计算，逐字照抄）：

```
add-U1 : LV.ψ⁰ (Y 1) ≼ read (proj₁ (ψ lvl1 (proj₂ ok₂ tt) (B₀ lvl1) zero (inc tt self) (Ωt zero) (O.U 1)))
exp-U1 : LV.ψ⁰ (WL.ψ₁ (Y 1)) ≼ read (proj₁ (E o₁ tdNil (O.U 1) Ω₁op (B₀ lvl1) zero (inc tt self) (Ωt zero)))
add-2  : LV.ψ⁰ (Y 1) ≼ read (proj₁ (ψ lvl1 (proj₂ ok₂ tt) (B₀ lvl1) zero (inc tt self) (Ωt zero) (chainW 2)))      -- = consume second
exp-2  : LV.ψ⁰ (WL.ψ₁ (Y 1)) ≼ read (proj₁ (E o₁ tdNil (chainW 2) Ω₁op (B₀ lvl1) zero (inc tt self) (Ωt zero)))   -- = consume-exp second
```

##### 2.2 外层目标（单独的目标）

```
outer : LV.ψ⁰ (body (Y 1)) ≼ read Ψ₃          -- Ψ₃ = WKShape.Ψ₃，body (Y 1) = Ω₂ᴸ LV.+ LV.up LV.zero (Y 1)
```

左端是 Level 的 ψ⁰(Ω₂ + Y 1)，Y 1 = ψ₁(Ω₂ + Ω₁)。这是 Ψ₃ 的下界，没有上界。

**用的实际分支：**

- 先证 `match-z2 : Match (Y 1) (O.z 2)`。`z 2 = ex c c nc (suc (z 1))` 是第二次更新的原始内链第 2 项，与 `U 1` 用同一对描述，前一个 c 只用正性。
- 它不经 `to-second`，所以不需要证明它到累加分支的传递。

**路径**（由外到内，逐层取下界）：

1. Ψ₃ 的 Ω₃ 结点在目标 0 走链，取链第 1 项 `s₃ 0 = ex Ω₂t Ω₂t (suc 0)`（`node-ge … 1`）。
2. 取 `next⁺` 的第 0 项。
3. 取 `E (suc 0)` 的第 0 个近似项，它就是 `run F st1 zero (z≤ lvl2) v₁`，即 `WKGen.Main ok₂ st1 w2 v₁ … .Ψg`。
4. 取第 2 层 Ω₂ 链的第 2 项 `zs 2`，它定义上就是 `O.z 2`（`Ψg-ge 2`）。

**底族与底：**

- 底族：`st1 = itS F 1 (B₀ lvl2)`，即一次更新后的状态，第 1 层分量就是 c；用 `st1 ∘ inc` 把 `z 2` 折到第 0 层。
- 底：`v₁ = ψ lvl2 ok₂ (B₀ lvl2) zero (z≤ lvl2) (Ωt zero) Ω₂t`。
- 第 0 层链底：`cz = st1 zero (inc tt (inc tt self))`。

**值的论证：**

- `SumR-z2` 给出 `dY1 (read v₁) (read cz) ≼ read (fold 2)`。
- 新的 Level 引理 `L2-sem`：`Ld D d`，且 a、c 都 ≥ ψ⁰(Ω₂)，则 `ψ⁰ (body D) ≼ d a c`。它与 `WSLevel.Ld-sem` 同形；Ω₁ 结点的链在 Level 一侧由 `ψ≼ψ⁰` 压到 ψ⁰。
- v₁ 和 cz 都 ≥ ψ⁰(Ω₂)，由初态底族上的 `WKGen.Main … .main` 给出。

#### 3. 否定

无。`B8PairMain.no-merge` 否定的是 `chainW 1` 的一对描述，本题右端是 `U 1` 和 `chainW 2`，两者没有冲突。

#### 4. 纸面判断（都未编译）

- **外层左端的位置：** ψ⁰(Ω₂ + ψ₁(Ω₂+Ω₁)) 严格高于 ψ₀(Ω₂)、低于 ψ₀(Ω₂·2)。严格性没有编译。这只是 Ψ₃ 的一个粗下界，离 ψ₀(Ω₃) 很远。
- **外层只用了 Ψ₃ 里的第一次 F 运行：** 底族是 st1，`E (suc 0)` 只取第 0 个近似项。我判断，沿 `E` 的后续近似项（底族 st2, st3, …）配合 `at-suc` 一类结果可以继续上推到 lim ψ⁰(body (Y n)) = ψ⁰(Ω₂+Ω₂)，但还缺 `Y n`（n ≥ 2）与第 n 次更新的配对，以及 `L2-sem` 对更高前缀的推广。
- **可合并进接口的引理：** `RealX` 推广了 `WSW4.W2`、`B8PairW4.Pre.W2P` 和 `WKGen.W2c`，这是同一条 ex 行引理第三次以不同名字出现，可按 AGENTS 的规定合并进接口。`L2-sem` 是 `Ld-sem` 在前缀 Ω₂ 上的版本，按阶段写成，不是阶段无关的定理。

#### 5. 翻译账

- `RealX`、`Real-pos` 是 W4 自身 ex 行、正性的值律，没有读记号的基本列。
- `L2-sem` 只在 Level 验收侧。
- 没有新增脚手架，也没有用 `Lab`。

## 派发消息正文（简报全文原样，本机路径换成占位）

本批实验目录 B9_RUN = <B9_RUN> （公共目录已按协调简报准备并冷编：$B9_RUN/common 里 WKAll、WSMain、YiLAB8Split 均退出 0，B8 与 YiLAB9Orbit 模块都已检查；库文件 $B9_RUN/libraries）。在每条 shell 命令前先 export B9_RUN=<B9_RUN>。简报里的相对链接以 probes/Survey/Lead/第九批/ 为基准。你的最终消息就是回报原文，会逐字留档。

以下为简报全文（原样）：

## B9A · 第二次更新能否承载整棵 Y 1

请独立完成 W4 的第 4 层值证明，全程中文，模型 Opus 5.5。先读仓库根 `AGENTS.md`、工程手册 §4 及[主审指令 02](../Lead/指令-02.md)。公共目录由协调者给出；独立收到本简报时可先运行[公共准备段](../Lead/第九批/00-协调简报.md)。在 `$B9_RUN/B9A` 写纯 Agda，新模块前缀 `B9Inner`。

**首交目标是 `second : Second`。** `YiLAB8Split.Second = Match (Y 1) (chainW 2)`。这要求整棵非初始 Level 链点与两次更新后的 W4 树共同满足被加项、指数的四个字段。第八批只在较小的 `X₀` 上得到配对。主审已证初态无法承载 `X₀`，本路继续向上取整棵 `Y 1`。

1. 优先试 `at1 : AtPart 1`，用 `to-second at1` 交付。`AtPart k` 使用的是第二次更新的实际**累加分支** `YiLAB9Orbit.U k`。记一次更新的状态为 c；`second-part` 给出 `U 1 ≡ ex (z 1 + c) c nc (suc (z 1)) tt`。`inner-seed` 已把 `X₀` 接到 `U 0`。先明确消费 c 的哪一处、指数的哪一处；若使用原始内链 `z 2`，补证其界到累加分支的传递。
2. `B8PairLevel.Ld-Y1/Lx-Y1` 给已满足 Level 字段的具体描述。`B8PairW4.Real-c1` 给 c 的指数描述 `lC ε = eΩ₂`，`SumR-c1` 与 `B8PairMain.shift-d` 可把 c 的被加项描述收窄到 `dΩ₂`。先试以 W4 侧的 `ex`、前缀或语义膨胀律合成同一对描述；若换描述，说明两个方向的比较。第八批 `no-merge` 否定的是一次更新的一对具体描述，本题的右端不同。
3. 如 `U 1` 太小或难以消费，可由计算选有依据的其他 k，再经 `part k` 提升；也可对整个极限给值界。不要把“在一支找齐四个字段”升格成必要条件。取得 `second` 后，分别编译 `consume second`、`consume-exp second` 对应的闭不等式，写清左右端。若有余量，优先把一个实际非初始分支接到 `LV.ψ⁰ (body (Y 1)) ≼ read WKShape.Ψ₃`，说明底族和路径；这是单独的外层目标。
4. 第二种写法可直接证明整棵 `Y 1` 在两次更新处的一个闭消费者值界。若只完成这一条，按这一条回报。任何否定也须对准签名，并给已满足的前提。新代码约 1200 行、可换一次写法；触顶或两种写法受阻时交最小未证签名与最后一个已编译实例。

在仓库根执行，按入口实名替换文件名：

```sh
agda +RTS -M6G -RTS --library-file="$B9_RUN/libraries" -i src -i probes -i "$B9_RUN/common" -i "$B9_RUN/B9A" "$B9_RUN/B9A/B9InnerMain.agda" > "$B9_RUN/B9A/compile.log" 2>&1
code=$?
echo "agda exit $code"
```

沿用公共 OPTIONS，一次一个 Agda；仓库、W4、公共源码只读。第 4 层若使用排中律或函数外延，标明条件及给出见证的具体步骤。回报按闭项、值界、否定、纸面判断分开写，列出新模块、每个分支编号、出口、退出码与依赖。源码和回报交协调者，无须等待对照路。
