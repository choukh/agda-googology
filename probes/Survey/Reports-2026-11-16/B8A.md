# B8A：用更新一次的 W4 状态承载第一个非初始参照链点（Opus 5.5，外部主审第八批）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-18 05:51 至 06:16 |
| 工具调用 / agda 编译 (粗数) | 33 / 10 |
| token (usage 字段，按消息去重) | 输出 153875；新写入缓存的输入 451536；读缓存的输入 6635476；其余输入 64 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `B8Pair` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | First 未走通（无编译否定）；编译定理无前提：first₀ : Match X₀ (chainW 1)（X₀ = Y 1 的第 0 支 ψ(Ω₂)），两个消费者闭不等式 c-add₀、c-exp₀；Level 一侧对一切 Y n 的两项描述 Lx-Y、Ld-Y；Match 沿 W4 结构步进向上封闭（Match-up），故 frozen→first；描述 d₁ 容纳不了 Y 1（no-merge，只否定这一个描述）；执行方判断 First 在值上为假（配对错位：Y 链落在 W4 第二次更新之内），候选配对 Y n 对 chainW 2 的内链项未编译；协调者私有目录只复制源码 6G 冷编退出 0，附件 attachments/B8A-* |

## 简报原文

本批实验目录 B8_RUN = <临时目录> （公共目录已准备并冷编：$B8_RUN/B8Common 里 WKAll、YiLAB7Orbit、YiLAB7Replay 均退出 0；库文件 $B8_RUN/libraries）。在每条 shell 命令前先 export B8_RUN=<临时目录> probes/Survey/Lead/第八批/ 为基准。你的最终消息就是回报原文，会逐字留档。

以下为简报全文（原样）：

### B8A · 用更新一次的 W4 状态承载第一个非初始参照链点

请按本简报独立完成一个 Agda 证明。工作目录为 agda-googology 仓库根，全程中文，模型 Opus 5.5。先读根目录 `AGENTS.md` 和 `probes/Survey/EBOHandbook.md` §4。协调者会给出本批实验目录 `B8_RUN`。若单独收到本简报，先运行[协调简报的公共准备段](../Lead/第八批/00-协调简报.md)，再执行本路。只在 `$B8_RUN/B8A` 写源码与日志，新模块前缀 `B8Pair`。

#### 要交的定理

在 `YiLAB7Replay` 的公共接口上构造闭项

```agda
first : First
-- First = Match (Y 1) (chainW 1)
```

`Y n` 是 Level 参照树的一条实际链。`body x` 把 x 从第 1 层嵌入第 2 层，再接在该层 Ω 树右侧。`double-shape` 已证 `ψ⁰ (Ω₂ + Ω₂)` 就是 `ψ⁰ (body (Y n))` 的 ℕ 极限。`chainW n` 是 W4 标准底族经第 2 层 Ω 运算更新 n 次后，在第 1 层的实际分量。下标 1 在两边都表示第一次更新。

`Match X y` 要选同一对 d、e，填满四个字段。W4 的 `SumR y d` 与 `Real y e` 描述 y 作被加项和指数时能承载的值；Level 的 `Ld X d` 与 `Lx X e` 说明这些描述足以控制 X。公共模块已有 `seed : Match (Y 0) (chainW 0)`。`at-step 1` 能给 W4 一侧的结构描述，`lower` 能在更新后再次使用被加项下界。Level 的两项义务仍待证明。[公共接口与主审复核](../Lead/指令-01.md) · [第七批证据](B7A.md)

#### 做法与止损

1. 先在纸面逐项展开 `Y 1` 与 `chainW 1`，标出 `ψ` 的保留或走链行，以及从旧底族读取、向新状态写入的具体分量。用一小段可编译陈述核对你要用的展开。查 `WSLevel.Ld/Lx` 的结点、加法、放宽及移位引理，`WSW4.Lem.Real`、`WKSum.Sum`、`WKStep` 的 W4 侧引理。
2. 先在主审已经生成的规范域上做。可以用 `at-step 1` 所给的描述，也可以选能同时满足四项的其他描述。两侧已有的描述若有差别，写清要证的有向关系及所用放宽律。每条条件定理附一个适用实例。
3. 一旦得到 `first`，将 `consume first` 与 `consume-exp first` 分别写成明确左右端的闭不等式并编译。两端分别是参照与 W4 的实际计算。`consume-exp` 使用指数证据；只填被加项字段不能交付 `First`。
4. 若第一种写法受阻，第二种可直接证明 `consume-exp first` 所指的**同一闭不等式**（独立写左右端，证明体不假设 first），或者仅为眼前保留行加入最小的目标 1 语义并在该点消费。这样得到的结果按所证值界单列。首交通过且仍有预算，可选一个延伸：下一链点，或把 `ψ⁰ (body (Y 1))` 的值界接到 `read Ψ₃`。两种写法用尽或新代码约到 1200 行即停，交最后可编译的签名、卡点和已验证的实例。

#### 编译与回报

按仓库约定使用 `--safe --without-K`，沿用公共源码 OPTIONS。第 4 层可将排中律或函数外延作为模块参数；若使用，说明它解决的精确命题并标为条件定理。W4、公共接口、旧的证明和仓库文件只读。每次一个 Agda 进程，6G 堆，日志落在本路目录。以下示例假设入口叫 `B8PairMain`，在仓库根执行，按实际模块名替换。

```sh
agda +RTS -M6G -RTS --library-file="$B8_RUN/libraries" -i src -i probes -i "$B8_RUN/B8Common" -i "$B8_RUN/B8A" "$B8_RUN/B8A/B8PairMain.agda" > "$B8_RUN/B8A/compile.log" 2>&1
code=$?
echo "agda exit $code"
```

回报先写 `First` 的状态，再列新模块、精确签名、前提与实例、编译退出码和两个消费者的结果。分别标编译定理、有限测试和判断。写明尚欠哪一条值界、这批工作对树自足及记号依赖的影响。将源码与回报交协调者复核。本路的结论可独立提交给协调者，无须等待冻结对照路。

## 回报原文

### B8A 回报 · 用更新一次的 W4 状态承载第一个非初始参照链点

#### 结论：`First` 未走通

**`First = Match (Y 1) (chainW 1)` 没有得到。** 我的判断是它在值上不成立。这一条是纸面分析，没有编译否定，所以本路只写"未走通"，不写"已否定"。

对纲领与目标的含义：
- 本路没有新增或改动任何树、折叠、合法性定义。W4 和公共接口只读，新文件全部是第 4 层（值验收）文件。
- 本路得到的有向信息来自树侧自身的形状，不来自记号：
  - W4 的一次更新把旧分量放在前面，是 c ↦ "c + Ω₂ 折到第 1 层"。
  - Level 的链步把 Ω₂ 放在前面，是 x ↦ ψ(Ω₂ + x)。
  - 因此 `chainW 1` 对应的是 Y 1 的第 0 个分支 X₀ = ψ(Ω₂)，而不是 Y 1 本身。
- 编号相同的这一对配错了位：我判断 Level 的整条 Y 链落在 W4 的第二次更新之内。

**已编译的部分（无前提）：**
- 一个非初始配对 `first₀ : Match X₀ (chainW 1)`，带两个消费者的闭不等式。
- Level 一侧对一切 Y n 的两项描述（主审说的两项待证义务）。
- Match 沿 W4 的结构序向上封闭，因此 `Frozen → First`。
- 一条描述路线的编译否定 `no-merge`。

#### 新模块

都在 `$B8_RUN/B8A`，共 408 行。

| 模块 | 行数 | 内容 |
|---|---|---|
| `B8PairLevel` | 127 | 只涉及 Level 一侧的描述 |
| `B8PairW4` | 156 | 只涉及 W4 一侧：语义引理与 `chainW 1` 的描述 |
| `B8PairMain` | 125 | 入口：配对、消费者、封闭性、否定 |

#### 编译

- 命令：从仓库根执行 `agda +RTS -M6G -RTS --library-file="$B8_RUN/libraries" -i src -i probes -i "$B8_RUN/B8Common" -i "$B8_RUN/B8A" "$B8_RUN/B8A/B8PairMain.agda" > "$B8_RUN/B8A/compile.log" 2>&1`。
- 结果：删掉三份自己的 `.agdai` 后冷编，**退出 0**，约 6 秒，峰值很低。
- 日志里有三条自己的 Checking 行：`B8PairMain`、`B8PairLevel`、`B8PairW4`。
- 警告只有 `UnsupportedIndexedMatch`（不支持的索引匹配）。我自己的模块里只有 `s≰` 一处触发，其余来自公共依赖。
- 选项：三份文件头都是 `--safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns`。
- 扫描：没有 postulate、洞、停机或正性编译指示，源码里没有本机路径。
- 没有用排中律，也没有用函数外延。
- 依赖图：`$B8_RUN/B8A/main.dot`（`--dependency-graph` 生成）。

#### 精确签名（全部是编译定理，无前提）

##### Level 一侧 `B8PairLevel`

名字的白话：
- `eΩ₂ = lC ε` 是 Ω₂ 作指数的影子，`dΩ₂ = sE eΩ₂ Nx` 是它作被加项的影子。
- `QB X = LV.ψ LV.zero (λ q → q) (LV.add Ω₂ᴸ (λ q → LV.suc q) X)`，即 ψ(Ω₂ + X)。

展开核对（都是 `refl`）：
```agda
Y-step   : (n : ℕ) → Y (suc n) ≡ QB (Y n)
Y1-shape : Y 1 ≡ LV.limᵢ LV.zero (λ y → P (LV.tr⁻ LV.z≅ y))   -- 穿透行: 第 1 层的 Ω 结点, 第 y 分支 = ψ(Ω₂ + y)
X₀-shape : X₀ ≡ LV.lim (λ n → ψ₁ (γ n))                        -- X₀ = QB zero, 同层走链行
```

主定理：对 X 的指数描述归纳，形状同 `WSLevel.shift0` 与 `shiftH`。
```agda
LdQ : ∀ {X e} → Lx X e → Ld (QB X) (sE (eΩ₂ ⨾ e) Nx)
LxQ : ∀ {X e} → Lx X e → Lx (QB X) (sh (eΩ₂ ⨾ e))
```

参照链的描述：
```agda
eY 0 = Ω̂ ;  eY (suc n) = sh (eΩ₂ ⨾ eY n)
Lx-Y  : (n : ℕ) → Lx (Y n) (eY n)
Ld-Y  : (n : ℕ) → Ld (Y (suc n)) (sE (eΩ₂ ⨾ eY n) Nx)
Ld-Y1 : Ld (Y 1) dY1     -- dY1 = sE (eΩ₂ ⨾ Ω̂) Nx
Lx-Y1 : Lx (Y 1) eY1     -- eY1 = sh (eΩ₂ ⨾ Ω̂)
```

##### W4 一侧 `B8PairW4`

记号：`o = proj₂ ok₂ tt`；`zW = iter (λ x → ex Ω₁t Ω₁t nbΩ (suc x) tt) zero`；`Fz n = zW (suc n)`。

展开核对：
```agda
chainW0-shape : chainW 0 ≡ Ω₁t
chainW1-shape : Σ _ (λ s → chainW 1 ≡ lim (cum Fz) s)          -- 走链行, 输出是累加极限
cum-shape     : (n : ℕ) → cum Fz (suc n) ≡ Pre.xp (cum Fz n) (zW (suc n))
```
读法：`chainW 1` 走的是第 2 层 Ω 树在目标 1 的走链行。每个链项是第 1 层自身行的输出 `ex c₁ c₁ (suc z)`，把旧分量 c₁ = Ω₁ 读两次；新状态写入的是这些输出的累加极限。

语义引理：
```agda
Real-up    : ∀ {x y e} → lvl1 ⊢ x ◃ y → Real x e → Real y e
SumR-up    : ∀ {y y′ d} → lvl1 ⊢ y ◃ y′ → SumR y d → SumR y′ d
Real-lim   : ∀ {f s h} → (∀ j → Real (f j) (h j)) → Real (lim f s) (lC h)
chain-step : (n : ℕ) → lvl1 ⊢ chainW n ◃ chainW (suc n)
Pre.W2P    : (x : Tr lvl1) (e : ES) → Real x e → Real (Pre.xp a₀ x) (sh e)   -- W2 的前缀版
```
前缀版的定义：`xp x = ex (a₀ + Ω₁t) Ω₁t nbΩ (suc x) tt`，对任意前缀 a₀ 成立。

`chainW 1` 的描述：
```agda
Rz      : (m : ℕ) → Real (zW (suc m)) (ε m)   -- 与 Level 的 Lx (γ m) (ε m) 是同一个影子
Real-c1 : Real (chainW 1) (lC ε)
SumR-c1 : SumR (chainW 1) d₁                  -- d₁ a c = lim_n dW n a c
```
其中 `dW 0 = Nx`，`dW (suc m) = sE (ε m) Nx`。

##### 入口 `B8PairMain`

配对与两个消费者（左端是 Level 参照的实际计算，右端是 W4 的实际计算）：
```agda
first₀ : Match X₀ (chainW 1)
c-add₀ : LV.ψ⁰ X₀ ≼ read (proj₁ (ψ lvl1 (proj₂ ok₂ tt) (B₀ lvl1) zero (inc tt self) (Ωt zero) (chainW 1)))
c-exp₀ : LV.ψ⁰ (WL.ψ₁ X₀) ≼ read (proj₁ (E o₁ tdNil (chainW 1) Ω₁op (B₀ lvl1) zero (inc tt self) (Ωt zero)))
```
- 公共描述是 d = d₁，e = lC ε。
- Level 一侧用的唯一放宽是下标平移一格：`shift-d : Le 0 dΩ₂ d₁` 与 `shift-e : LeE (lC (ε ∘ suc)) (lC ε)`。
- 没有用影子的单调性，四个字段属于同一对描述。
- 指数证据确实被使用：`c-exp₀` 走的是 `exp-w` 与 `exp-l`。

封闭性与推论：
```agda
Match-up     : ∀ {x y y′} → lvl1 ⊢ y ◃ y′ → Match x y → Match x y′
frozen→first : Frozen → First
seed-up      : (n : ℕ) → Match (Y 0) (chainW n)
first₀-up    : (n : ℕ) → Match X₀ (chainW (suc n))
```

`First` 的两个出口，左右端逐字写出：
```agda
Goal-add  = LV.ψ⁰ (Y 1) ≼ read (proj₁ (ψ lvl1 (proj₂ ok₂ tt) (B₀ lvl1) zero (inc tt self) (Ωt zero) (chainW 1)))
Goal-exp  = LV.ψ⁰ (WL.ψ₁ (Y 1)) ≼ read (proj₁ (E o₁ tdNil (chainW 1) Ω₁op (B₀ lvl1) zero (inc tt self) (Ωt zero)))
first→add : First → Goal-add
first→exp : First → Goal-exp
```

描述路线及其否定：
```agda
first-if : Le 0 dY1 d₁ → LeE eY1 (lC ε) → First
no-merge : Le 0 dY1 d₁ → ⊥
X₀≺Y1    : LV.suc (LV.ψ⁰ X₀) ≼ LV.ψ⁰ (Y 1)
```
- `first-if` 的第一个前提被 `no-merge` 否定，所以 `first-if` 只说明这条路走不通，不给任何正面结论。
- `no-merge` 的论证在 (1, 1) 处：dY1 ≥ dΩ₂(dΩ₂ 1 1, dΩ₂ 1 1) ≻ dΩ₂ 1 1 ≥ d₁ 1 1。
- `X₀≺Y1` 只展开 Level 的定义：Goal-add 的左端严格高于 c-add₀ 的左端。

#### 前提与实例

- 编译定理全部没有前提。
- `first-if` 的前提不可满足（`no-merge`），已如实标出。
- 实例：`first₀`、`seed-up`、`first₀-up` 都是闭项。

#### 两种写法的结果

1. **公共描述。** 对 X₀ 成功，得到 `first₀`。对 Y 1，用 `chainW 1` 的描述 d₁ 去容纳 Y 1 的规范描述，被 `no-merge` 编译否定。
   - 这只否定"d₁ 这一个描述"。我没有检查 `at-step 1` 给出的结构描述能否容纳 Y 1。它的 d 在 ex 行把恒等换成了 Ω₁ 的影子，比 d₁ 大；要否定它需要影子对参数的单调性，未做。
2. **直接证 `Goal-exp`，或加目标 1 的最小语义。** 没有动手，因为我判断目标不等式本身为假，见下一节。

#### 判断（纸面，未编译）

用 Ω 算术的粗略读法：
- `chainW n` 约为 ε_{Ω+n}，所以 `chainW 1` 约为 ψ₁(Ω₂) = ε_{Ω+1}，与 X₀ 同值。
- Y 1 = sup_y ψ₁(Ω₂+y)，约为 ε_{Ω+1}·Ω。
- 因此 ψ⁰(Y 1) 约为 ψ₀(ε_{Ω+1}·Ω)，远高于 W4 对 `chainW 1` 的折叠（约为 ψ₀(ε_{Ω+1})）。Goal-add 与 Goal-exp 都为假。
- 由 `frozen→first`，`First → ⊥` 一旦成立，就推出 `Frozen → ⊥`。
- sup_n Y n = ε_{Ω+2}，约为 `chainW 2`。有值依据的配对候选是 Y n 对 `chainW 2` 的内链项 z′(n+1)，其中 z′(k+1) = ex c c (suc z′ k)，c = `chainW 1`。
  - 纸面核对：z′(2) ≥ c·Ω ≥ Y 1，z′(3) ≥ c·ω^{c·Ω} ≥ Y 2。
  - 这一对没有编译。
- X₀ 对 `chainW 0` 的配对在值上为假（ε_{Ω+1} 对 Ω₁），所以 `first₀` 这一点确实用到了更新。这是判断，没有冻结否定。

#### 尚欠的值界

1. **`First → ⊥` 的编译否定。** 需要 W4 一侧的上界（W4 折叠不高于某个参照）。现有代码只有下界方向，这是一个新方向，可交给 B8N 或后续一路。
2. **任何把 Y 1 配给 W4 的正面结果。** Y 1 是 Ω 结点（影子是 nodeS），W4 一侧是 ℕ 极限或 ex 行。下一个必经缺口是"各阶单调的影子"比较理论（逻辑关系），现有代码有意避开了影子单调。我没有开工：按简报，延伸只在首交通过后才做。
3. **外层值界。** `ψ⁰ (body (Y 1)) ≼ read Ψ₃` 未动。`first₀` 给出的两个闭不等式只有 ψ₀(Ω₂) 量级（X₀ 是 ψ₁(Ω₂)，ψ⁰ X₀ 是 ψ⁰(Ω₂) 的链去掉首项；两者互相 `≼` 未编译）。它们没有超出既有的 ψ₀(Ω₂) 下界强度，离完整的 ψ₀(Ω₃) 还差整个第 3 层链。

#### 依赖与树自足

- 本路没有新增树侧定义，翻译账为零。
- 新模块的导入闭包（依赖图核对）里，项目模块有 W4Block、W4Ops、W4Path、W4Fold、WS*、WK*、WV*、YiLAB7Orbit/Replay，以及 `OCF.Align.Level` 参照。
- 经公共的 WVOne（导入 `OCF.Align.BTBOValMain`），闭包里还有记号模块：Label、Prefix、Standard 等。这是公共验收文件继承下来的，我的陈述没有引用它们。
- 对 Level 参照的依赖只出现在第 4 层值验收里。

#### 文件

- 源码：`$B8_RUN/B8A/B8PairLevel.agda`、`$B8_RUN/B8A/B8PairW4.agda`、`$B8_RUN/B8A/B8PairMain.agda`
- 日志：`$B8_RUN/B8A/compile.log`（冷编，退出 0）；另有中间日志 `level.log`、`w4.log`
- 依赖图：`$B8_RUN/B8A/main.dot`

`B8_RUN` 是 `<临时目录>`。

## 派发消息正文（简报全文原样，本机路径换成占位）

本批实验目录 B8_RUN = <B8_RUN> （公共目录已准备并冷编：$B8_RUN/B8Common 里 WKAll、YiLAB7Orbit、YiLAB7Replay 均退出 0；库文件 $B8_RUN/libraries）。在每条 shell 命令前先 export B8_RUN=<B8_RUN>。简报里的相对链接以 probes/Survey/Lead/第八批/ 为基准。你的最终消息就是回报原文，会逐字留档。

以下为简报全文（原样）：

## B8A · 用更新一次的 W4 状态承载第一个非初始参照链点

请按本简报独立完成一个 Agda 证明。工作目录为 agda-googology 仓库根，全程中文，模型 Opus 5.5。先读根目录 `AGENTS.md` 和 `probes/Survey/EBOHandbook.md` §4。协调者会给出本批实验目录 `B8_RUN`。若单独收到本简报，先运行[协调简报的公共准备段](../Lead/第八批/00-协调简报.md)，再执行本路。只在 `$B8_RUN/B8A` 写源码与日志，新模块前缀 `B8Pair`。

### 要交的定理

在 `YiLAB7Replay` 的公共接口上构造闭项

```agda
first : First
-- First = Match (Y 1) (chainW 1)
```

`Y n` 是 Level 参照树的一条实际链。`body x` 把 x 从第 1 层嵌入第 2 层，再接在该层 Ω 树右侧。`double-shape` 已证 `ψ⁰ (Ω₂ + Ω₂)` 就是 `ψ⁰ (body (Y n))` 的 ℕ 极限。`chainW n` 是 W4 标准底族经第 2 层 Ω 运算更新 n 次后，在第 1 层的实际分量。下标 1 在两边都表示第一次更新。

`Match X y` 要选同一对 d、e，填满四个字段。W4 的 `SumR y d` 与 `Real y e` 描述 y 作被加项和指数时能承载的值；Level 的 `Ld X d` 与 `Lx X e` 说明这些描述足以控制 X。公共模块已有 `seed : Match (Y 0) (chainW 0)`。`at-step 1` 能给 W4 一侧的结构描述，`lower` 能在更新后再次使用被加项下界。Level 的两项义务仍待证明。[公共接口与主审复核](../Lead/指令-01.md) · [第七批证据](B7A.md)

### 做法与止损

1. 先在纸面逐项展开 `Y 1` 与 `chainW 1`，标出 `ψ` 的保留或走链行，以及从旧底族读取、向新状态写入的具体分量。用一小段可编译陈述核对你要用的展开。查 `WSLevel.Ld/Lx` 的结点、加法、放宽及移位引理，`WSW4.Lem.Real`、`WKSum.Sum`、`WKStep` 的 W4 侧引理。
2. 先在主审已经生成的规范域上做。可以用 `at-step 1` 所给的描述，也可以选能同时满足四项的其他描述。两侧已有的描述若有差别，写清要证的有向关系及所用放宽律。每条条件定理附一个适用实例。
3. 一旦得到 `first`，将 `consume first` 与 `consume-exp first` 分别写成明确左右端的闭不等式并编译。两端分别是参照与 W4 的实际计算。`consume-exp` 使用指数证据；只填被加项字段不能交付 `First`。
4. 若第一种写法受阻，第二种可直接证明 `consume-exp first` 所指的**同一闭不等式**（独立写左右端，证明体不假设 first），或者仅为眼前保留行加入最小的目标 1 语义并在该点消费。这样得到的结果按所证值界单列。首交通过且仍有预算，可选一个延伸：下一链点，或把 `ψ⁰ (body (Y 1))` 的值界接到 `read Ψ₃`。两种写法用尽或新代码约到 1200 行即停，交最后可编译的签名、卡点和已验证的实例。

### 编译与回报

按仓库约定使用 `--safe --without-K`，沿用公共源码 OPTIONS。第 4 层可将排中律或函数外延作为模块参数；若使用，说明它解决的精确命题并标为条件定理。W4、公共接口、旧的证明和仓库文件只读。每次一个 Agda 进程，6G 堆，日志落在本路目录。以下示例假设入口叫 `B8PairMain`，在仓库根执行，按实际模块名替换。

```sh
agda +RTS -M6G -RTS --library-file="$B8_RUN/libraries" -i src -i probes -i "$B8_RUN/B8Common" -i "$B8_RUN/B8A" "$B8_RUN/B8A/B8PairMain.agda" > "$B8_RUN/B8A/compile.log" 2>&1
code=$?
echo "agda exit $code"
```

回报先写 `First` 的状态，再列新模块、精确签名、前提与实例、编译退出码和两个消费者的结果。分别标编译定理、有限测试和判断。写明尚欠哪一条值界、这批工作对树自足及记号依赖的影响。将源码与回报交协调者复核。本路的结论可独立提交给协调者，无须等待冻结对照路。
