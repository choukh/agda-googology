# B8N：冻结对照（Opus 5.5，外部主审第八批）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-18 05:51 至 06:04 |
| 工具调用 / agda 编译 (粗数) | 29 / 4 |
| token (usage 字段，按消息去重) | 输出 74268；新写入缓存的输入 231362；读缓存的输入 4692989；其余输入 56 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `B8Freeze` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | Frozen 被否定（编译定理，无前提，无排中律、函数外延）：no-frozen m = refute (consume m)，refute 与 consume 在 Y 1、chainW 0 处的目标逐字一致；no-add 对一切 d 否定两个被加项字段；机制是值界矛盾（fold-val：冻结折叠与 ψ⁰(Y 0) 同值；low：suc (ψ⁰ Ω₁) ≼ ψ⁰ (Y 1)；irr）；单看指数一半未判定；First → ⊥ 未形式化，执行方判断 First 也很可能不成立（相同编号配对本身的问题）；协调者在执行目录外私有目录只复制源码，6G 串行冷编退出 0（17 个模块重新检查），附件 attachments/B8N-B8FreezeMain.agda.txt |

## 简报原文

本批实验目录 B8_RUN = <临时目录> （公共目录已准备并冷编：$B8_RUN/B8Common 里 WKAll、YiLAB7Orbit、YiLAB7Replay 均退出 0；库文件 $B8_RUN/libraries）。在每条 shell 命令前先 export B8_RUN=<临时目录> probes/Survey/Lead/第八批/ 为基准。你的最终消息就是回报原文，会逐字留档。

以下为简报全文（原样）：

### B8N · 冻结第 1 层初始状态，对照同一个参照链点

请独立审查第八批的冻结对照。工作目录为 agda-googology 仓库根，全程中文，模型 Opus 5.5。先读根目录 `AGENTS.md` 和 `probes/Survey/EBOHandbook.md` §4。协调者会给出本批实验目录 `B8_RUN`。若单独收到本简报，先运行[协调简报的公共准备段](../Lead/第八批/00-协调简报.md)，再执行本路。只在 `$B8_RUN/B8N` 写源码与日志，新模块前缀 `B8Freeze`。

#### 要判别的命题

构造路比较更新一次的实际 W4 树。本路把**参照固定在同一个 `Y 1`**，把 W4 的第 1 层树固定为初态 `chainW 0`。在公共模块 `YiLAB7Replay` 上尝试其一：

```agda
frozen : Frozen
-- Frozen = Match (Y 1) (chainW 0)
-- 或
no-frozen : Frozen → ⊥
```

`Y n` 来自 Level 的 `ψ⁰ (Ω₂ + Ω₂)` 的实际链，`double-shape` 给出来源。`chainW 0` 是 W4 第 1 层标准 Ω 树。`seed` 已给出 `Match (Y 0) (chainW 0)`。`Match X y` 要**存在**共同的 d、e，满足 W4 的 `SumR y d`、`Real y e` 以及 Level 的 `Ld X d`、`Lx X e`。排除某一对候选描述只否定那个候选。两种消费者 `consume` 与 `consume-exp` 都接受任意完整见证。[公共接口和消费者](../Lead/指令-01.md) · [第七批的反例候选 C1、C4](attachments/B7A-WK-paper.txt)

#### 做法与止损

1. 先试肯定。展开 `Y 1`；在冻结的标准 Ω 树上复用 `seed`、`WSW4.Lem.W1` 的指数证据以及 `WSLevel` 的加法、移位、放宽律。给出允许共享的 d、e，检查比较方向。若有 `frozen`，提交完整见证，以及代入两个消费者得到的闭不等式。这个结果本身即有信息。
2. 再试否定。先写出冻结后某一个消费者的精确左右端，尝试证明该不等式推出空类型，或以已有的不相容定理和反向严格界推出矛盾。示意证明为 `no-frozen m = refute (consume-exp m)`，其中 `refute` 须独立编译，且目标与消费者逐字对上。若用被加项消费者，按其签名做同样检查。也可从接口字段直接得到矛盾，但须覆盖所有允许的 d、e。核对严格关系与值前序的联系；观察到两个头构造、两个影子或两条计算路径不同并不足以否定值界。
3. 若问题在相同编号的配对，且有具体依据，可尝试 `First → ⊥`，或交一个经编译的其他配对下标的见证。保留 `Frozen` 自身的准确状态。两种写法用尽或新代码约到 1200 行即停。若两边都未判定，报最后可编译的实例、卡在哪个不等式及为何现有引理用不上。

#### 编译与回报

按仓库约定使用 `--safe --without-K`，沿用公共源码 OPTIONS。第 4 层允许以排中律或函数外延为模块参数；用到时说明哪一步需要它，结论标“条件”。W4、公共接口、旧的证明和仓库文件只读。每次一个 Agda 进程，6G 堆，日志落在本路目录。以下示例假设入口叫 `B8FreezeMain`，在仓库根执行，按实际模块名替换。

```sh
agda +RTS -M6G -RTS --library-file="$B8_RUN/libraries" -i src -i probes -i "$B8_RUN/B8Common" -i "$B8_RUN/B8N" "$B8_RUN/B8N/B8FreezeMain.agda" > "$B8_RUN/B8N/compile.log" 2>&1
code=$?
echo "agda exit $code"
```

回报先写 `Frozen` 的状态，再列新模块、精确签名、前提及实例、退出码、消费者与否定的量化范围。分别标编译定理、有限测试和判断。某次证明受阻就写“未证”。本路只裁定实际覆盖的比较，整体路线的判断交主审。将源码和原文交协调者复核，无须等待构造路。

## 回报原文

### B8N 回报 · 冻结对照

#### 结论：Frozen 已被否定（编译定理，无前提，未用排中律或函数外延）

`no-frozen : Frozen → ⊥` 已编译通过，其中 `Frozen = Match (Y 1) (chainW 0)`。

- **对纲领与目标的意义**：在同一个参照链点 `Y 1` 上，W4 若把第 1 层冻结在初态 `chainW 0`，任何共同描述都不存在。初态描述不足以控制这个链点。由此可知，这一点的比较确实需要状态更新。但要下"更新足够"的结论，还须 B8A 的 `First` 成立，见文末判断。
- **被否定的对象**：被加项消费者 `consume` 的目标不等式对 `X = Y 1`、`y = chainW 0` 不成立，证明是 `no-frozen m = refute (consume m)`。否定只用到两个被加项字段 `add-w` 和 `add-l`，`e₀`、`exp-w`、`exp-l` 不参与。所以 d 是什么都不重要。更强的形式 `no-add` 对一切 `d` 否定这一对字段。
- **机制**：冻结树在消费者参数下折到零层，读回的值恰好与 `ψ⁰ Ω₁` 值相等（`fold-val`，两个方向都是定理）。Level 一侧有 `suc (ψ⁰ Ω₁) ≼ ψ⁰ (Y 1)`。两式接上，在第 0 层得到 `suc x ≼ x`，再由 `irr` 推出矛盾。所以这是值界上的矛盾，不是"头构造或计算路径不同"那类观察。

#### 新模块与编译

- **文件**：`<临时目录>`，173 行。
  - SHA-256：`36da81797e5203b82261fbfde2b46dffab17913306d4ee2cfb74305e395affc9`
- **选项**：沿用公共源码的 OPTIONS，`--safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns`。无公设、无洞、无编译指示，文件里没有本机路径。
- **命令**：在仓库根执行，删去本模块 `.agdai` 后重编：
  ```
  agda +RTS -M6G -RTS --library-file="$B8_RUN/libraries" -i src -i probes -i "$B8_RUN/B8Common" -i "$B8_RUN/B8N" "$B8_RUN/B8N/B8FreezeMain.agda" > "$B8_RUN/B8N/compile.log" 2>&1
  ```
- **结果**：退出码 0，约 7 秒。日志 `$B8_RUN/B8N/compile.log` 只有一行自己的 Checking：`Checking B8FreezeMain (...)`。本文件 0 条警告；日志里的 53 条 `UnsupportedIndexedMatch` 都来自已有依赖。
- **导入**：W4Block/Ops/Path/Fold，WVOne，WSShadow，WSLevel，WKSum，YiLAB7Orbit，YiLAB7Replay，OCF.Align.Level，OCF.Align.Value，OCF.BTBO。这是纯第 4 层验收文件，不改任何公共或仓库文件。

#### 精确签名（全部是编译定理）

```agda
refute    : LV.ψ⁰ (Y 1) ≼ read (proj₁ (ψ lvl1 (proj₂ ok₂ tt) (B₀ lvl1) zero (inc tt self) (Ωt zero) (chainW 0))) → ⊥
no-frozen : Frozen → ⊥                                   -- = refute (consume m)
no-add    : (d : Sh 0) → SumR (chainW 0) d → L.Ld (Y 1) d → ⊥
fold-up   : read (proj₁ (ψ lvl1 (proj₂ ok₂ tt) (B₀ lvl1) zero (inc tt self) (Ωt zero) (chainW 0))) ≼ LV.ψ⁰ L.Ω₁ᴸ
fold-val  : read (proj₁ (ψ lvl1 (proj₂ ok₂ tt) (B₀ lvl1) zero (inc tt self) (Ωt zero) (chainW 0))) ≈ᵛ LV.ψ⁰ (Y 0)   -- = fold-up , consume seed
low       : LV.suc (LV.ψ⁰ L.Ω₁ᴸ) ≼ LV.ψ⁰ (Y 1)
irr       : (x : T₀) → LV.suc x ≼ x → ⊥
Y1-big    : LV.ψ⁰ (ψ₁Ω₂ LV.+ ψ₁Ω₂) ≼ LV.ψ⁰ (Y 1)       -- 旁证, ψ₁Ω₂ = LV.ψ zero id Ω₂ᴸ
```

- **`refute` 的定义域**：与 `consume` 在 `x = Y 1`、`y = chainW 0` 处的目标逐字相同。`no-frozen` 就是靠这一点编译通过的。

**辅助引理**：
- 第 0 层算术：`x≼W`、`sW`、`ssW`、`W-sum`，以及 `Wψ`、`Wψ⁰`。这里 W 是 `Mv 𝟏`，后两条说 Level 的 ψ 和 ψ⁰ 在第 0 层树上不低于 W。
- W4 读回的上界：`read-+′`、`iterR′`、`P-up`（`WVOne.P-read` 的反方向）。
- 链的界：`zsZ`、`Cb`、`ZE`。
- 证明形状：
  - 冻结折叠的读回是 `lim (cum (Gt ∘ zs))`，`kp` 在 `inc tt self` 处给 `nothing`。每个链点和部分和都被 `W (suc (suc (Z n)))` 控制，而它又低于 Level 链 `Eψ (suc n)` 的 ψ⁰。
  - `low` 是一串 `≼l 0, 1, 0, 0, 2, 0, 2` 的定义性展开，路径为 Y 1 → ψ₁(Ω₂+1) → ψ₁Ω₂ → ψ₁Ω₁ → ψ₁⁰ 1 → Ω₁+Ω₁ → Ω₁+1，最后用 `ψ⁰Ω₁ + 𝟏 ≼ ψ⁰Ω₁ + ψ⁰Ω₁`。

#### 量化范围、前提与正对照

- **前提**：`no-frozen` 和 `no-add` 都没有前提。`no-add` 对一切 `d : Sh 0` 成立。
- **消费者参数**：否定所用参数与 `consume` 相同，即 `B₀ lvl1`、`inc tt self`、`β = Ωt zero`、`a = c = 𝟏`。
- **严格关系**：只用了第 0 层的 `irr`，即 `¬ (suc x ≼ x)`，对树结构归纳得到，没有经过 `≺`。
- **不是空真**：同一棵冻结树在 `Y 0` 上有见证 `seed`，所以 W4 那个字段可以满足，`d = Nx`。`fold-val` 还说明冻结折叠的值恰好是 ψ⁰(Y 0)，失败的是 Level 字段 `Ld (Y 1) d`。
- **描述的字面相等**：`Match` 只要求存在共用的 d、e，不要求描述字面相等。本否定对一切 d 成立，与描述的取法无关。

#### 未判定

- **单看指数一半**：只有 `exp-w`、`exp-l` 时（`consume-exp` 的冻结实例）是否可满足，未证。
  - 卡在哪里：要给 W4 的 `E` 在 Ω₁ 树上迭代 `Ω₁op` 的值一个上界，而且要跟踪迭代中的状态更新。本文件只有零层折叠的上界，现有引理全是下界方向（`Real`、`𝓡`），用不上。
- **`First → ⊥`**：未尝试形式化，原因见下面的判断。

#### 判断（未编译，纸面）

- **结论**：`First` 也很可能不成立，问题可能出在相同编号的配对本身。
- **依据**：
  - `stepG` 给出 `chainW 1 = lim cum (z (suc n))`，其中 `z (n+1) = ex Ω₁ Ω₁ (suc (z n))`，即 Ω₁ + Ω₁·ω^(z_n+1)。按序数值它是 ε_{Ω₁+1}，与 Level 的 ψ₁Ω₂ = lim γ(n+1) 同一量级。
  - `Y 1 = ψ₁(Ω₂+Ω₁)` 在 Level 里不低于 ψ₁Ω₂·2，`Y1-big` 已编译这一方向。
  - 所以 `First` 需要 W4 对 ε_{Ω₁+1} 型树的零层折叠达到 ψ⁰(ψ₁Ω₂·2) 以上，我估计达不到。
- **要编成定理还缺什么**：需要 W4 的 `E` 与 `It` 在第 1 层指数上的一套上界理论，与 B6A 下界理论方向相反，并且是各阶的。按预算估计远超本路剩余的约 1000 行。
- **范围**：这一条只是判断，路线判断交主审。

源码和日志都在 `<临时目录>`。

## 派发消息正文（简报全文原样，本机路径换成占位）

本批实验目录 B8_RUN = <B8_RUN> （公共目录已准备并冷编：$B8_RUN/B8Common 里 WKAll、YiLAB7Orbit、YiLAB7Replay 均退出 0；库文件 $B8_RUN/libraries）。在每条 shell 命令前先 export B8_RUN=<B8_RUN>。简报里的相对链接以 probes/Survey/Lead/第八批/ 为基准。你的最终消息就是回报原文，会逐字留档。

以下为简报全文（原样）：

## B8N · 冻结第 1 层初始状态，对照同一个参照链点

请独立审查第八批的冻结对照。工作目录为 agda-googology 仓库根，全程中文，模型 Opus 5.5。先读根目录 `AGENTS.md` 和 `probes/Survey/EBOHandbook.md` §4。协调者会给出本批实验目录 `B8_RUN`。若单独收到本简报，先运行[协调简报的公共准备段](../Lead/第八批/00-协调简报.md)，再执行本路。只在 `$B8_RUN/B8N` 写源码与日志，新模块前缀 `B8Freeze`。

### 要判别的命题

构造路比较更新一次的实际 W4 树。本路把**参照固定在同一个 `Y 1`**，把 W4 的第 1 层树固定为初态 `chainW 0`。在公共模块 `YiLAB7Replay` 上尝试其一：

```agda
frozen : Frozen
-- Frozen = Match (Y 1) (chainW 0)
-- 或
no-frozen : Frozen → ⊥
```

`Y n` 来自 Level 的 `ψ⁰ (Ω₂ + Ω₂)` 的实际链，`double-shape` 给出来源。`chainW 0` 是 W4 第 1 层标准 Ω 树。`seed` 已给出 `Match (Y 0) (chainW 0)`。`Match X y` 要**存在**共同的 d、e，满足 W4 的 `SumR y d`、`Real y e` 以及 Level 的 `Ld X d`、`Lx X e`。排除某一对候选描述只否定那个候选。两种消费者 `consume` 与 `consume-exp` 都接受任意完整见证。[公共接口和消费者](../Lead/指令-01.md) · [第七批的反例候选 C1、C4](attachments/B7A-WK-paper.txt)

### 做法与止损

1. 先试肯定。展开 `Y 1`；在冻结的标准 Ω 树上复用 `seed`、`WSW4.Lem.W1` 的指数证据以及 `WSLevel` 的加法、移位、放宽律。给出允许共享的 d、e，检查比较方向。若有 `frozen`，提交完整见证，以及代入两个消费者得到的闭不等式。这个结果本身即有信息。
2. 再试否定。先写出冻结后某一个消费者的精确左右端，尝试证明该不等式推出空类型，或以已有的不相容定理和反向严格界推出矛盾。示意证明为 `no-frozen m = refute (consume-exp m)`，其中 `refute` 须独立编译，且目标与消费者逐字对上。若用被加项消费者，按其签名做同样检查。也可从接口字段直接得到矛盾，但须覆盖所有允许的 d、e。核对严格关系与值前序的联系；观察到两个头构造、两个影子或两条计算路径不同并不足以否定值界。
3. 若问题在相同编号的配对，且有具体依据，可尝试 `First → ⊥`，或交一个经编译的其他配对下标的见证。保留 `Frozen` 自身的准确状态。两种写法用尽或新代码约到 1200 行即停。若两边都未判定，报最后可编译的实例、卡在哪个不等式及为何现有引理用不上。

### 编译与回报

按仓库约定使用 `--safe --without-K`，沿用公共源码 OPTIONS。第 4 层允许以排中律或函数外延为模块参数；用到时说明哪一步需要它，结论标“条件”。W4、公共接口、旧的证明和仓库文件只读。每次一个 Agda 进程，6G 堆，日志落在本路目录。以下示例假设入口叫 `B8FreezeMain`，在仓库根执行，按实际模块名替换。

```sh
agda +RTS -M6G -RTS --library-file="$B8_RUN/libraries" -i src -i probes -i "$B8_RUN/B8Common" -i "$B8_RUN/B8N" "$B8_RUN/B8N/B8FreezeMain.agda" > "$B8_RUN/B8N/compile.log" 2>&1
code=$?
echo "agda exit $code"
```

回报先写 `Frozen` 的状态，再列新模块、精确签名、前提及实例、退出码、消费者与否定的量化范围。分别标编译定理、有限测试和判断。某次证明受阻就写“未证”。本路只裁定实际覆盖的比较，整体路线的判断交主审。将源码和原文交协调者复核，无须等待构造路。
