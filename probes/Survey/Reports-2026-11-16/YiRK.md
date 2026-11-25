# 真实链孩子上的最小实例（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 01:56 至 02:27 |
| 工具调用 / agda 编译 (粗数) | 67 / 12 |
| token (usage 字段，按消息去重) | 输出 188694；新写入缓存的输入 322041；读缓存的输入 10563542；其余输入 112 |
| 写过的仓库文件 | `YiRKCell.lagda.md`, `YiRKChain.lagda.md` |
| 文件前缀 | `YiRK` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 2 件全部退出 0，禁用构造 0，导入闭包干净；三种写法的行都不看分支是否字面延伸目标孩子（w1、w2、w3）；现行行与上折回退都不在原材料上保留低于目标的槽位（ι-free、w2-never、w2A-*）；换基在重建的替身树上保留目标层副本的槽位（keep-lift），换基层号没有 Ω 形状子层号（noΩ-reb）；V50 按孩子对的提法在这一格为否（no-ωᵉ），换基把被问的对换成带 lift 证据的对；YiRKChain 的 a₁/feed/chain 是照 YiSYReduce 重写的副本，相等未编译 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b75/YiRK.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiRK 回报：真实链孩子上的最小实例（Opus 5.5）

#### 1. 判决

**对纲领与目标意味着什么。** 本路只给形状档的事实，没有值的定理。所有定义都没有派发判定，不触壁垒。

这一格上，三种写法的行都不看分支 c 是否字面延伸目标孩子 d（编译）。前两种写法（现行比较表行、上折回退）都没有在原材料上实现 "低于目标保留"：
- 现行行把孩子树折到第 0 层再加上去；
- 上折回退（K = `kp`）对材料里任何深度的槽位都走链。

换基（`YiBSFold`）不用原材料，对一切 c 换成层号 `h₁ d ⊕ ↑c` 上重建的 Ω 树，沿 `lift` 朝原目标折。在那棵树里，保留判定在目标层副本的槽位上保留（编译）；那一层号里没有 Ω 形状的子层号（编译）。

这给出一条树侧的判据（判断）：要不判定地实现 "低于目标保留"，字面关系得由折叠自己造出来（换基的 `lift`），不能去问表或保留判定 "两个任意孩子之间有没有路径"。这与交替路线里 "被比较的两个下标有字面公共上界" 一致，支持 V290 重看 "选表不选换基"。它是诊断，不是新定义，也不算 "树自足" 的定义进展。

**各步到哪里。**
- 第 0 步：完成。临时文件 `YiRK0.agda` 编译退出 0，现行行在 d = ω、c = ω+1 处逐字是退路行。
- 第 1 步：完成。三种写法（上折回退分 `kp`、`kpᴬ` 两个 K）× 两类分支，都是编译事实，表见下。
- 第 2 步：完成。`chain 1` 封进 `opaque`，对一切层号证据与底成立，同一张表逐格实例化。
- 第 3 步：只有判断，见问题表与下面的解释。

**表（d = ω 即 `ωᶜ`；目标 `h₁ d` 经 `inc d self`；顶结点在四个折叠里都保留在 q₀ = `inj₂ (0 , inj₁ tt)`：`top-ω`、`top₁`、`top₂`、`top₂ᴬ`、`top₃`）**

| 写法 | 分支 c | 进孩子层朝原目标折？ | 层号是 d 的字面前驱的槽位保留吗 | 输出形状 | 定理 |
|---|---|---|---|---|---|
| 1 现行（`YiTBRow.ψ`＋`rbᶻ`） | 延伸 ω+1、ω+ω | 否：孩子树折到第 0 层 | 否：尾项在 `ι` 的像里，没有 Ω 结点 | `折 x ⊞ ψ₀ᶻ (h₁ c) y` | `t1-s`、`t1-ω`；`ι-free`、`⊞-form` |
| | 不延伸 1、ωᵉ | 同上 | 同上 | 同上 | `t1-1`、`t1-e` |
| 2 上折回退，K = `kp` | 四个 c 都一样 | 不进孩子层；沿 `down stop c` 上折进 tw 1，朝原目标折 | 否：任何深度一律走链 | `ψˡ (tw 1) … (h₁ d) (inc d self) (折 x) (h₁ c) (down stop c) y` | `t2-*`；`w2-never`、`w2-drop` |
| 2′ 上折回退，K = `kpᴬ` | 同上 | 同上 | 层号字面是第 0 层的槽位保留在 q₀（`w2A-floor`）；`h₁ 1` 层的走链（`w2A-one`）；与目标同层的走链，即对角（`w2A-same`） | 同上 | `t2-*` |
| 3 换基（`YiBSFold`＋`rb-tw 1`） | 一切 c | 否：原孩子树只进 ψ₀ 尾项；在 `h₁ d ⊕ ↑c` 上重建 Ω 树，沿 `lift` 朝原目标折 | 原孩子树的：否。换基树里目标层副本的：在原槽位保留（`keep-lift`、`keep-ω`） | `seen S₁ (h₁ d) … c ⊞ ψ₀ y`；后继孩子处换基树的顶结点走链，槽位层号不低于目标（`seen-s`） | `t3-*`；`w3′`（同步对象给的路径） |

d = `chain 1` 上逐格同形：`u1-*`、`u2-*`、`u3-*`、`u3′`、`top-c₁`、`top-c₃`、`keep-c₁`、`noΩ-c₁`。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 三种写法的行是否区分 "c 字面延伸 d" | 不区分：`w1`、`w2` 只要 `NZ c`，`w3` 对一切 c | 编译定理 |
| 现行行在延伸族上如实？ | 否（形状：`w1`、`ι-free`） | 编译定理；值偏低是判断 |
| 上折回退在延伸族上如实？ | 否：低于目标的材料槽位走链（`w2-never`；`kpᴬ` 只救第 0 层，`w2A-*`） | 形状编译；值偏低是判断 |
| 换基在延伸族上如实？ | 对原材料不如实。对替身 Ω_{d⊕c} 按 FGH 形状走：低于目标保留（`keep-lift`），同层或更高走链（`seen-s`），碰不到 Ω 形状的回退行与 drop 行（`noΩ-reb`） | 保留判定是编译定理；"折叠只访问子层号" 与 "seen(c) 读作 ψ_d(Ω_{d+c})" 是判断 |
| 延伸族的上确界够不够承载参照（d = ω 时 sup_c ψ_d(Ω_c)） | 换基：够；写法 1、2：不够 | 判断 |
| V50 在这一格的答案（按 "(d, c) 对" 的提法） | 否。顶结点对一切 c 都问到；反例 (ω, ωᵉ) 两个方向都没有字面路径（`no-ωᵉ`）。延伸族有证据（`ext-path`），但表不能对任意 c 找到它 | 反例与证据是编译定理；"表找不到" 是判断，最近的编译件是 `YiTBObs.exact→wdec` |
| V50 在换基下 | 被问到的对换成 (h₁ d, h₁ d ⊕ ↑c)，证据 `lift` 对一切 c 字面成立（`w3` 里 route 给 `inj₂ (lift zero (↑ zero d))`） | 编译定理 |
| `chain 1` 的形状 | 对一切 `o`、`B`，顶是 ℕ 极限（`L₁`）；链孩子 `a₁ (chain 1)` 的层号是 ℕ 极限形状（`child-L`）。把 D 路的纸面判断升为定理 | 编译定理 |
| 同步对象在链孩子处实际问到的目标层号 | 由 chain 1 的基本列下降给出，不是 `h₁ (chain 1)` 本身；标准底下第 0 段是 lim(n ↦ n+1)，即数字目标 | 纸面推演，未编译 |
| `chain 1` 与某个非延伸孩子之间没有字面路径 | 未编译 | 判断（同 ω 的情形） |

上确界一行的判断依据：
- 换基："够" 的理由是 d⊕c 不低于 c、折叠对层号单调、延伸族共尾。三条都没有编译。
- 写法 1、2："不够" 的理由是输出只有底 β 加上可数次迭代。

#### 2. 文件表

| 文件 | 代码行（非空） | 冷编退出码 | 峰值内存 |
|---|---|---|---|
| `<仓库>/probes/OCF/Lean/YiRKCell.lagda.md` | 205（全文 303） | 0 | 373 MiB |
| `<仓库>/probes/OCF/Lean/YiRKChain.lagda.md` | 84（全文 123） | 0 | 267 MiB |
| 临时：`<实验目录>/work/YiRK/YiRK0.agda`（第 0 步）、`YiRK1.agda`、`YiRK2.agda`（草稿） | — | 0 | ≤ 316 MiB |

自查结果：
- 冷编日志里只有自己模块的 `Checking` 行。
- 检索 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、`--irrelevant-projections`、`--cubical`、`funext` 与本机路径：0 处。
- `importclosure.py`：两个模块都退出 0，禁用表命中 0。

#### 3. 定理表（陈述逐字）

先给几个缩写的原文：
- `Ext d c = zero ⊢ d ◃ c`
- `Kept {j} t = Σ (Pos j) λ q → IsΩ q t`
- `IsL t`：顶是 `lim`
- `IsΩ q t`：顶是 `Ω q _`
- `S₁ = schema zero (↑ zero) tt self (OkO↑ zero zero tt self) (λ c → refl)`，逐字是 `rb-tw 1` 的第一分量

`Cell` 的原文（`module _ (d c : Tr zero)`）：
```
Cell₁ = (o : Ok (tw 1)) (B : Base (tw 1)) (β : Tr⁺ (h₁ d)) (x : Tr (tw 1)) (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y)
    → ψ₁ (tw 1) o (rbᶻ (tw 1)) B (h₁ d) (inc d self) β (up x c y e)
    ≡ ψ₁ (tw 1) o (rbᶻ (tw 1)) B (h₁ d) (inc d self) β x ⊞ ψ₀ᶻ (h₁ c) (proj₂ o c) y
Cell₂ K = (o …) (B …) (β …) (x …) (y …) (e …)
    → Fold.ψ K true (tw 1) o (rbᶻ (tw 1)) B (h₁ d) (inc d self) β (up x c y e)
    ≡ Fold.ψˡ K true (tw 1) o (λ i u → Fold.ψ K true (tw 1) o (rbᶻ (tw 1)) B i u (B i u) x) (h₁ d) (inc d self)
        (Fold.ψ K true (tw 1) o (rbᶻ (tw 1)) B (h₁ d) (inc d self) β x) (h₁ c) (down stop c) y
Cell₃ = (o …) (B …) (β …) (x …) (y …) (e …)
    → BS.ψ (tw 1) o (rb-tw 1) B (h₁ d) (inc d self) β (up x c y e)
    ≡ seen S₁ (h₁ d) (proj₂ o d) (lift zero (↑ zero d)) (BS.ψ (tw 1) o (rb-tw 1) B (h₁ d) (inc d self) β x) c
      ⊞ BS.ψ (h₁ c) (proj₂ o c) (proj₂ (rb-tw 1) c) (B₀ (h₁ c)) zero (z≤ (h₁ c)) (Ωt zero) y
Cell₃′ = 同 Cell₃，路径换成 inc (suc d) (inc tt self)，证据换成 proj₂ (proj₂ o (suc d)) tt
```

下表 "文件" 一栏，C 指 `YiRKCell`，H 指 `YiRKChain`；档都是编译定理。

| 名字 | 陈述 | 白话 | 文件 |
|---|---|---|---|
| `ext-path` | `∀ {d c} → Ext d c → h₁ d ≤ h₁ c` | 字面延伸给出层号路径（同 `YiPTAll.Rg`） | C |
| `no-ωᵉ` | `(h₁ ωᵉ ≤ h₁ ωᶜ) ⊎ (h₁ ωᶜ ≤ h₁ ωᵉ) → ⊥` | ω 与偶数列 ω 之间两个方向都没有字面路径（由 `YiTBObs` 组合） | C |
| `top-ω` | `(B : Base (tw 1)) (β : Tr⁺ (h₁ ωᶜ)) → IsΩ q₀ (proj₁ (ψ₁ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) B (h₁ ωᶜ) (inc ωᶜ self) β (proj₁ (Ωt (tw 1)))))` | d = ω 时顶结点保留在 q₀ | C |
| `top₁`、`top₂`、`top₂ᴬ`、`top₃` | `∀ {d} → NZ d → (B : Base (tw 1)) (β : Tr⁺ (h₁ d)) → Kept (proj₁ (… (h₁ d) (inc d self) β (proj₁ (Ωt (tw 1)))))`；四个折叠分别是 `ψ₁ … (rbᶻ (tw 1))`、`Fold.ψ kp true …`、`Fold.ψ kpᴬ true …`、`BS.ψ … (rb-tw 1)` | 顶结点在四个折叠里都保留，所以一切 c 都被问到 | C |
| `w1` | `∀ {d c} → NZ d → NZ c → Cell₁ d c` | 现行行退到第 0 层 | C |
| `w2` | `∀ (K : KeepFn) {d c} → NZ d → NZ c → Cell₂ d c K` | 上折回退进 `ψˡ` | C |
| `w3`、`w3′` | `∀ {d} → NZ d → ∀ c → Cell₃ d c`（`Cell₃′`） | 换基对一切 c | C |
| `t1-s` … `t3-e`（12 条） | 例如 `t1-s : Cell₁ ωᶜ (suc ωᶜ)`、`t2-ω : ∀ K → Cell₂ ωᶜ ωω K`、`t3-e : Cell₃ ωᶜ ωᵉ` | d = ω 时的表，c 取 ω+1、ω+ω、1、ωᵉ | C |
| `ι-free` | `∀ j (t : Tr zero) → Ωfree (ι j t)` | 回退尾项没有 Ω 结点 | C |
| `⊞-form` | `∀ {j} (b : Tr⁺ j) (t : Tr⁺ zero) → proj₁ (b ⊞ t) ≡ proj₁ b + ι j (proj₁ t)` | ⊞ 加上去的是 ι 的像 | C |
| `w2-never` | `∀ (o : Ok (tw 1)) {s h} (d : Dn (tw 1) (nd s h)) (c : Ch s) (p : Pos (h c)) c′ {j} (v : j ≤ h₁ c′) → IsNothing (kp (tw 1) o (mv (down d c) p) (inc c′ v))` | 上折后任何深度的材料槽位，`kp` 都不保留 | C |
| `w2-drop` | `∀ (o : Ok (tw 1)) (X : Base (tw 1)) j c′ (v : j ≤ h₁ c′) (β : Tr⁺ j) c (p : Pos (h₁ c)) g → IsL (proj₁ (Fold.ψˡ kp true (tw 1) o X j (inc c′ v) β (h₁ c) (down stop c) (Ω p g)))` | 材料里的 Ω 结点变成链 | C |
| `w2A-floor` | `∀ (o : Ok (tw 1)) (X : Base (tw 1)) c′ (v : h₁ ωᶜ ≤ h₁ c′) (β : Tr⁺ (h₁ ωᶜ)) g → IsΩ q₀ (proj₁ (Fold.ψˡ kpᴬ true (tw 1) o X (h₁ ωᶜ) (inc c′ v) β (h₁ (suc ωᶜ)) (down stop (suc ωᶜ)) (Ω p⁰ g)))` | `kpᴬ` 保留第 0 层的槽位 | C |
| `w2A-one`、`w2A-same` | 同上，槽位换成 p¹、p⁼，结论换成 `IsL (…)` | `h₁ 1` 层与目标同层的槽位走链 | C |
| `keep-lift` | `(j b : L) (o : Ok (j ⊕ b)) (q : Pos j) → KeptAt q (kp⁼ (j ⊕ b) o (psh (lift j b) (inj₂ q)) (lift j b))` | 换基层里目标层副本的槽位保留在原槽位 | C |
| `keep-ω` | `∀ c (o : Ok (h₁ ωᶜ ⊕ ↑ zero c)) → KeptAt q₁ (kp⁼ (h₁ ωᶜ ⊕ ↑ zero c) o (psh (lift (h₁ ωᶜ) (↑ zero c)) (inj₂ q₁)) (lift (h₁ ωᶜ) (↑ zero c)))` | 实例：层号 `h₁ 1` 的槽位 q₁ | C |
| `seen-s` | `∀ d j (oj : Ok j) (u : zero ≤ j) (β : Tr⁺ j) → IsL (proj₁ (seen S₁ j oj u β (suc d)))` | 后继孩子处换基树的顶走链 | C |
| `noΩ-reb` | `(d c : Tr zero) → NoΩ (h₁ d ⊕ ↑ zero c)` | 换基层号里没有 Ω 形状的子层号 | C |
| `l-node` | `∀ {X x₀} (m : Keep zero X x₀) (G : X → Tr⁺ zero) (s : X → X) → IsL (proj₁ (node⁺ m G s))` | 第 0 层的结点必是链 | H |
| `Real.L₁` | `IsL chain₁`（`chain₁ = chain 1`，opaque；`module Real (o : Ok (nd (sΩ zero) a₁)) (B : Base (nd (sΩ zero) a₁))`） | chain 1 的顶是 ℕ 极限，对一切 o、B | H |
| `Real.child-L` | `Σ (ℕ → L) λ g → a₁ chain₁ ≡ nd sL g` | 真实链孩子的层号是 ℕ 极限形状 | H |
| `Real.u1-*`、`u2-*`、`u3-*`、`u3′`、`top-c₁`、`top-c₃`、`keep-c₁`、`noΩ-c₁` | 把 `ωᶜ` 换成 `chain₁` 的同形陈述；c 取 `suc chain₁`、`chain₁ + ωᶜ`、`nat 1`、`ωᵉ` | d = chain 1 时的表 | H |

#### 4. 第一个障碍

形状档没有障碍，各步一次编译通过。

值的第一个未证步：在 d = ω 上，没有关于 `YiBSBase.seen` 的值定理，即 "延伸的 c 处 `seen S₁ (h₁ ωᶜ) … c` 不低于 ψ_ω(Ω_c) 的读法"。
- 现有的 `YiBSCrit` 只到数字孩子。
- 本路按简报只做形状档，没有尝试，所以不能说它是数学上挡住还是工程上挡住。
- 判断：需要两件事，一是 "换基层上的折叠对层号单调"，二是 "seen 的读法"；两者都是值理论。

`chain 1` 与非延伸孩子之间没有字面路径的否定没有编译。这属于工程问题：chain 1 的结构依赖 o 和 B。

#### 5. 偏离、事故与未读

**偏离**
- 目标层取 `h₁ d` 经 `inc d self`。写法 3 另加了同步对象的路径 `inc (suc d) (inc tt self)`（`w3′`）。写法 1、2 的 Cell 只陈述了 `inc d self` 一种路径；`YiVALeaf.fall` 本身对任意路径成立。
- "真实链孩子对应的层号" 只编译了 `child-L`，这些层号来自基本列下降那一层是纸面推演。
- `YiRKChain` 里的 `a₁`、`feed`、`chain` 是照抄 `YiSYReduce`、`YiSYDesc.Node` 重写的，为的是导入闭包干净。两边相等没有编译，是读代码得出的判断。

**事故**
- 第一次编译试图套 `/usr/bin/time`，被沙箱拦下（sysctl），agda 照常跑完。之后改用 `+RTS -s`。

**没有读、只凭转述的东西**
- YiVA 留档：没有读。
- AuditD 留档：只读了第 150–269 行，其余靠检索。
- 台账：只检索了 V50、V146–149、V153、V154、V158、V287–290。
- `YiKTSlot`、`YiRQDom`：只读了文首与几段。
- `YiBSCrit`、`YiBSClean`、`YiBTZero`、`YiBTOne`、`YiBSAccept`：只读了文首。
- `EBOHandbook` §4.2/4.6 与 Bedrock 性能手册：没有读，因为没有出现性能问题（峰值 373 MiB）。
- "现行折叠上 `Cand` 关闭" 等结论引自简报，本路不依赖它们。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：真实链孩子上的最小实例（三种写法各算一格）（前缀 YiRK，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。同批另两路与你互不导入。

#### 作者的决定与背景（2026-11-17）
- Fable 5.2 的路线审核 D 路（先读定义、封存后再读结论；留档 `probes/Survey/Reports-2026-11-16/AuditD.md`，判定件附件 `attachments/AuditD-*.txt`）与此前的独立审核 YiVA（`Reports-2026-11-16/YiVA.md`）两份封存件独立判断：现行折叠在 "Ω 形状结点下、材料在一个孩子里、目标在另一个孩子下面" 时没有实现 "低于目标保留"（`YiRWFold.kp` 的 `(inj₂ _) (inc _ _) = nothing` 一行与 `YiTBRow.ψ` 的退路行），同步对象上的那一步链步（`YiKTSlot.Cand`）不成立。**作者据此定（选项原文）："按两份审核关闭 (Recommended)"**：现行折叠上 `Cand` 这一格及其值否定线关闭，不再派它的任何变体（它在第七十一到七十四批以 `TightStep 1`、`TightDom`、`Top₁`、`Refute`、`single`、`Branch`、`cand₁` 七个名字出现过；台账 V287）。
- 第七十五批作者选三路（选项原文）："真实链孩子上的最小实例 (Recommended)"、"对折叠参数化的整体接口 (Recommended)"、"候选的两个有限测试"。前缀 `YiRK`（Opus 5.5）、`YiFI`（Fable 5.2）、`YiCT`（Opus 5.5），互不导入。**主线定义不动**；改树、折叠、合法性只在新文件里做候选。
- D 路审核要点（判断，未编译）：决定成败的是台账 V50（读回域上被问到的 "目标孩子 c′、材料孩子 c" 的对，是否都带字面证据）。真实同步对象的链在第 0 层（`YiSYReduce`：层号 `nd (sΩ zero) a`，`chain` 是 `feed` 的迭代），真实链孩子是 `a (chain m)`，`chain m` 是回灌输出，不是数字；第七十二到七十四批的测试都在数字孩子 `a₁ (suc d)` 上。数字孩子是可判定的特例：比较表在 "任一端是数字" 的整列可字面填满（`AuditDFin.colFin`、`col-total`），换表后那一格如实进孩子层朝原目标折（`AuditDRow.honest`；现行表下是 `fallᶻ`）。对一般孩子，任何表都不能让每一支如实，只能指望与目标孩子字面共尾的那一族如实；这是换基（台账 V149、V158）要做的，11-14 选比较表而不选换基的决定要重看（V290）。
- 已编译的机制（主审复核过）：`YiVALeaf.fall-diag`、`leaf-branch`（不读记号）；`YiRQDom.drop`、`fall`、`start-form`、`kp*ᵍ`、`kp₀ᵍ`；`YiUSBound.base-form`、`leaf-node₂`；候选原型 `YiDXFold`（`Fold (K : KeepFn) (lifted : Bool)`，(A) `kpᴬ`，(B) 上折回退 `ψˡ`）、`YiKFKeep`/`YiKFFold`（(C) 来源表 `Pv`、`Org`、`kpʳ`、`kpᶜ`），`YiKFValue`（值定理用标准底 `B₀`，不是 `Cand` 的继承底）；`AuditDCand.cand`（候选在塔第 1 项、目标层 ≥ 2 时对层号非零的槽位仍走链）。换基原型：`YiBSFold`、`YiBSBase`（`split`、`seen`）、`YiBSReadNeg`、`YiBSClean`、`YiBSCrit`（只到数字孩子）、`YiBTZero`、`YiBTOne`。
- 主线现状：第一档成品已完成；终点无条件值 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω)（`YiFYRef.target-low`）；里程碑 ψ₀(Ω_{Ω₂}) 未达到。

#### 本路的问题
在一个真实形状的对象上判定 V50 那一格。目标孩子 d 取非数字的树：先 `ω`（第 0 层的 ℕ 极限树），再试真实链点 `chain 1`（闭项可能大，按 C-9 在变量上陈述，具体闭项放 `opaque`）。朝目标层 `h₁ d`（或真实链孩子对应的层号）折塔第 1 项 `tw 1` 的 Ω 树时，看 Ω 结点的各分支 c：
- c **字面延伸** d（d 是 c 的字面前驱，例如 c = d+1、d+ω 一类；"字面延伸" 的证据类型由你定，只用构造子与第一位置序，不比较值）；
- c 不延伸 d（例如 c 是数字）。
对三种写法各算这一格（形状档的编译事实，`refl` 或对变量的等式，仿 `YiVALeaf.leaf-branch`、`AuditDRow.honest`）：
1. 现行行：`YiTBRow.ψ` 配 `YiMTTab.rbᶻ`；
2. 上折回退：`YiDXFold.Fold` 取 `lifted = true`（`ψˡ`）；
3. 换基：`YiBSFold` 那一行（或按 V149 的描述写的最小一行；若要新写，只在新文件，并按 AGENTS "开新行前的先验检查" 对照 `YiAbsObs` 的 `obs→dec` 一族）。
每格要回答：分支是否进孩子层朝原目标折；分支里层号是 d 的字面前驱的槽位是否保留；输出的形状。

#### 要做的（按序）
0. 写出 "字面延伸" 的证据类型与目标孩子 `ω`；在临时文件里先对现行行编译一格。不成立就停下回报。
1. 三种写法 × 两类分支，各一格编译事实；交一张表。
2. 再对 `chain 1`（或它的变量形式）做同样的表。
3. 判断（标档）：哪种写法在字面延伸的那一族上如实；这一族的上确界够不够承载链步需要的参照（例如 d = ω 时 sup_c ψ_d(Ω_c) 一类）；V50 在这一格上的答案。

#### 规则（主审写给内部子智能体，必须照做）
- **先读** `AGENTS.md` 全文；性能问题先查 `probes/Survey/EBOHandbook.md` 4.2、4.6 节与 Bedrock 性能手册 `<Bedrock>/dev/cubical-agda-performance.md` 的 C-9（在变量上陈述、定义等式作假设、在唯一调用点实例化）、C-10（具体的站作 opaque 原子或模块参数）、S-1/S-3（重的构造在出生处封进 opaque，并在同一块里导出规格等式）、C-24、Q-1（`--profile=definitions`）、Q-23（量底价、二分）、H-6（251 之后不原样重跑）。
- **只新建文件**，放 `probes/OCF/Lean/`，用你的前缀（见上）。不改任何已有文件，不碰 `src/`、`archive/`，不碰别的前缀。中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行（判决与档位、做了什么、不否定什么、入口）；代码之间只写范围与不显然的理由。一次性的试验放你的临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要把前三个也写上，否则报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（写 `<实验目录>`、`<仓库>`）。
- **编译**（仓库根目录）：`agda +RTS -M6G -RTS --library-file=<库文件> -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`；临时目录的纯 `.agda` 另加 `-i <你的临时目录>`。退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 Agda 内部错误。报退出码不经过管道。同时只跑一个 agda，堆上限 6G（同批另有四路，外部广撒网也可能在编，机器共 64G；峰值超过 4G 先改形状）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下，写字面路径）。大的 `refl` 前加 `timeout 600`。
- **停下的条件**：退出 251 时不原样重跑，先按 C-9、C-10、S-1 改形状并定位（附 profile 或二分数据）；改过形状后同一上限仍撞墙才停。同一处两次重新设计仍过不了检查器也停。若某一步要改树、折叠或合法性的定义，停下回报。没有编译的否定时只写 "未走通"。
- **过程**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。动手证一般形式之前先用临时文件检查前提可满足；已有引理先检索（`grep`）再写，不重证，搬来的证明在文首写明来源。查签名用检索，不整篇读大文件。
- 不在你的临时目录与你前缀的新文件之外写、删、移任何东西；不 `pkill`，不写 `/tmp`，不装包，不提交，不改 `probes/README.md`、`probes/LOG.md`、台账与留档。
- **两条已更正的事实**（不要再照旧说法写）：`YiMXNote.¬Mono` 否定的是记号一侧非标准形项的项序单调，**不是**树侧折叠的跨层单调（树侧跨层单调目前没有编译的否定）；`YiKWObjects.kept` 是新封装的对象，与 `YiC1Slot` 不透明块里的 `kept` 不是同一个。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0；文首标 "不读记号" 的文件用 `python3 probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包。

#### 回报（最后一条消息就是回报，主审会原样留档）
1. 判决：先说对纲领与目标意味着什么；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理；是数学上挡住还是工程上挡住。
5. 偏离与事故；没有读、只凭转述引用的东西。
不用 "只差"、"自然" 一类形容；判断与定理分开写。

