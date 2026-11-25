# 同步对象上的 Tail（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-16 13:31 至 14:24 |
| 工具调用 / agda 编译 (粗数) | 81 / 29 |
| token (usage 字段，按消息去重) | 输出 259725；新写入缓存的输入 1049161；读缓存的输入 21604098；其余输入 154 |
| 写过的仓库文件 | `YiTLReduce.lagda.md` |
| 文件前缀 | `YiTL` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 1 件退出 0，禁用构造 0；Leaf 在同步对象的孩子层号上无前提（leaf-a₁）；Tail、FirstMissing、Kᴱ′ 2 由对孩子一致的两条保持得到（不对 m 归纳）；第一个挡住的引理 TightStep d，现有三种证据域在那里都为空（no-index-top、block-frame、no-lbl-hh），引理本身未判定 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b71/YiTL.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiTL 回报：同步对象上的 Tail（执行方 Opus 5.5）

#### 1. 判决

**对纲领与目标的意义.** 新增一个验收文件（第 4 层，读记号），树、折叠、合法性与比较表一行没有改，也没有新增序数值下界。`FirstMissing` 与 `Tail` 都未证；否定只有对现有证据域的否定，没有任何路线被否定。
- 本路得到的结构是：`Tail` 不需要对 m 归纳。只要在每个孩子层号 `a₁ c` 上有对 c 一致的保持（`KeepOut`、`KeepFeed`），就直接得到 `Tail`、`FirstMissing`、`Kᴱ′ 2`。
- 第一个挡住的地方已经定位到一条可以写出的引理：紧的链的一步 `TightStep d`。在现有的三种证据域里，这一处都为空，三条都是编译定理（只否定证据域）。这一点同"量化域先取带证据的读回域"那条最佳实践一致。

**各步到哪里.**
- 第 0 步：完成。最小检查通过：
  - `out`、`feed` 展开成孩子层号 `a₁ c` 上的折叠，两者只差路径与起点（`refl`）。
  - `S ν` 逐字就是 ψ₀(Ω_{Ω_ν})（`refl`）。
  - Leaf 部分（↑ 读回不低于 γ）无前提成立：读回域里前缀 `tw 1` 取空读法，`GR.R zero ν c` 给出 Ω_{Ω_ν} 不高于 `Ωt (a₁ c)`。
  - LowKeep 部分是 `PresAt (a₁ (chain 2))` 在目标第 0 层、下标与前缀都为空时的实例，类型已确认。
- 第 1 步：未走通。`FirstMissing` 没有证出。它与 `KeepOut` 在 `chain 2` 处等价（Leaf 已补上），也是 `pres` 与 `Kit (a₁ (chain 2))` 的实例。
- 第 2 步：给出第一个挡住的引理（见第 4 节）。它不是 `LowKeepˣ` 的实例，因为 `LowKeepˣ` 在每个 `a₁ c` 上为空。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| ψ₀(Ω_{Ω_ν}) 的 Leaf 在每个 `a₁ c` 上成立 | `leaf-a₁` | 编译定理，无前提 |
| `Tail` 由对 c 一致的 `KeepOut`、`KeepFeed` 得到，不对 m 归纳 | `tail-fromᴱ` | 编译条件定理 |
| `FirstMissing`、`Kᴱ′ 2` 由同一对前提得到 | `first-from-keep`、`k2′-from-keep` | 编译条件定理 |
| `FirstMissing` 单点形式：由 `KeepOut (chain 2)` 得到 | `first-fromᴱ`、`same-first` | 编译条件定理 |
| `FirstMissing` 是 `PresAt (a₁ (chain 2))` 的实例，经 `pres` 归到 `Kit` | `from-presᴱ`、`from-kitᴱ` | 编译条件定理（余下 `OK`、`PrefixU`、`Exᴴ`） |
| 是否为 `LowKeepˣ` 的实例 | `no-lbl-a₁` | 否；编译定理（`Lbl (a₁ c) ν → ⊥`） |
| 最小表下，`IndexOK` 从任何 `tw 1 ⊕ Y` 到任何不含 Ω 的非零层号 | `no-index-⊕`、`no-index-a₁`、`no-index-top` | 编译否定（只否定证据域） |
| 下界读法的框架在后继形状层号上，经任何非 `self` 路径 | `succ-frame`、`block-frame` | 编译定理：只在 ν ≡ [] 时有居民 |
| 精确标签在阻挡结点的孩子 `hh d z` 上 | `no-lbl-hh` | 编译定理：不存在 |
| 下标在项序上低于槽位底的读法时，链不需要 `StepU′` | `chain-below` | 编译定理 |
| `TightStep d` 是否成立 | `TightStep`、`tight-from` | 未判定（陈述已编译） |
| `chain 2` 的顶构造子是 `lim`，所以 `a₁ (chain 2)` 是 ℕ 极限形状 | — | 判断，未编译 |
| `FirstMissing` 的推导必经 d ≥ 1 的紧链结点（因为 S(γ1) 高于 ψ₀(Ω_{Ω_2})） | — | 判断 |
| 前缀读作空时，`tw 1` 叶子上表缺项的回退行只承载平凡参照，值不受损；`IndexOK` 为空是框架的限制 | — | 判断 |
| `a₁ (d+1)` 顶结点的链是紧的（κ 是 d 的读法，第 `h₁ d` 层的树低于 Ω_{d+1}） | — | 判断 |

#### 2. 文件表

| 文件 | 物理行 | 非空非注释代码行 | 冷编 |
|---|---|---|---|
| `probes/OCF/Lean/YiTLReduce.lagda.md` | 368 | 249 | 删自身接口后 8G 冷编，退出 0；日志只有本模块一行 `Checking`；最大驻留约 1.61G，约 20 秒 |

- 检索结果：禁用构造 0，本机路径 0，`Funext` 0。
- 文首标为"读记号"，所以不需要做导入闭包检查。
- 临时目录（`<实验目录>/work/YiTL`）里有 `TL0` 到 `TL8` 的纯 `.agda` 试验与日志，不在仓库里。

#### 3. 定理表（文件均为 `YiTLReduce`；"Gv 内"指在变量 a、o、B、β、lf 上陈述，`Gvᴱ = Gv a₁ oᴱ Bᴱ (betaᴱ 2) leaf-a₁`）

| 名字 | 逐字的陈述 | 白话 | 档 |
|---|---|---|---|
| `Gv.out-form` | `∀ c → proj₁ (out c) ≡ Fz c (z≤ (a c)) β (proj₁ (Ωt (a c)))` | 输出就是孩子层号上 Ω 树的折叠 | 编译（`refl`） |
| `Gv.feed-form` | `∀ c → feed c ≡ Fz c (self ∙ proj₂ (proj₁ o) c) (B zero (ink self)) (proj₁ (Ωt (a c)))` | 回灌同上，只换路径与起点 | 编译（`refl`） |
| `S-form` | `∀ ν → S ν ≡ E.ψ [] (E.Ωt (E.Ωt ν)) ∷ []` | 同步映射逐字是 ψ₀(Ω_{Ω_ν}) | 编译（`refl`） |
| `leaf-a₁` | `LeafAt a₁`，其中 `LeafAt a = ∀ {ν c} → GR.R zero ν c → Top (a c) (E.Ωt ν)` | 链点不低于 ν 时，孩子层号的 Ω 树不低于 Ω_{Ω_ν} | 编译，无前提 |
| `tail-fromᴱ` | `(∀ c → Gvᴱ.KeepOut c) → (∀ c → Gvᴱ.KeepFeed c) → SM.Gᴱ.Tail` | `Tail` 来自对孩子一致的保持 | 编译条件定理 |
| `first-from-keep` | `(∀ c → Gvᴱ.KeepOut c) → (∀ c → Gvᴱ.KeepFeed c) → SM.Gᴱ.FirstMissing` | 同上，结论取 `FirstMissing` | 编译条件定理 |
| `k2′-from-keep` | `(∀ c → Gvᴱ.KeepOut c) → (∀ c → Gvᴱ.KeepFeed c) → Kᴱ′ 2` | 第 2 站的对位下界 | 编译条件定理 |
| `first-fromᴱ` | `Gvᴱ.FirstFrom`，即 `Gvᴱ.KeepOut (Gvᴱ.chain 2) → Gvᴱ.FirstMissing` | 单点形式 | 编译条件定理 |
| `same-first` | `Gvᴱ.FirstMissing → SM.Gᴱ.FirstMissing` | 同一模块对同一参数的两份拷贝 | 编译 |
| `from-presᴱ` | `Gvᴱ.FromPres two′ mb₂`；`FromPres two mb = (P : PresAt (a (chain 2))) (gb : OK (D.dn B (chain 2))) (pf : PrefixU (D.dn B (chain 2)) []) → H.Exᴴ (deriv-at (chain 2) P gb pf mb (lf (of⁰ two))) → FirstMissing` | `FirstMissing` 是 `PresAt` 实例加出口条件 | 编译条件定理 |
| `from-kitᴱ` | `Gvᴱ.FromKit two′ mb₂`（同上，`P` 换成 `pres (a (chain 2)) kit`，`kit : Kit (a (chain 2))`） | 归到整体保持的工具箱 `Kit` | 编译条件定理 |
| `no-lbl-tw1` | `∀ X {ν} → Lbl (tw 1 ⊕ X) ν → ⊥` | 以 `tw 1` 为前缀的层号没有精确标签 | 编译 |
| `no-lbl-a₁` | `∀ c {ν} → Lbl (a₁ c) ν → ⊥` | `LowKeepˣ` 在每个孩子层号上为空 | 编译 |
| `succ-shape` | `∀ d → a₁ (suc d) ≡ nd (sΩ (h₁ d)) (hh d)` | 后继孩子的顶结点是 `h₁ d` 上的 Ω 结点 | 编译（`refl`） |
| `keep-zero` | `∀ {X x₀} (k : F.Keep zero X x₀) → k ≡ nothing` | 目标为第 0 层时什么都不保留 | 编译 |
| `no-lbl-hh` | `∀ d z {ν} → Lbl (hh d z) ν → ⊥` | 阻挡结点的孩子没有精确标签 | 编译 |
| `succ-frame` | `(h : ⊤ → L) (o : Ok (nd sS h)) {j : L} (w : j ≤ nd sS h) (ν : E.T) → NotSelf w → NodeFrame (nd sS h) o j w ν → ν ≡ []` | 推广 `no-frame-S`：后继形状的框架只容空下标 | 编译 |
| `block-frame` | `∀ d z (o : Ok (hh d z)) (w : h₁ d ≤ hh d z) (ν : E.T) → NodeFrame (hh d z) o (h₁ d) w ν → ν ≡ []` | 阻挡处对任何路径都只容空下标 | 编译 |
| `no-index-⊕` | `∀ Y {K} → NoΩ K → (K ≡ zero → ⊥) → (o : Ok (tw 1 ⊕ Y)) (w : K ≤ tw 1 ⊕ Y) (ν : E.T) → IndexOK (tw 1 ⊕ Y) o (rbᶻ (tw 1 ⊕ Y)) K w ν → ⊥` | 最小表下，从 `tw 1` 前缀层号到不含 Ω 的非零目标，路线证据为空 | 编译否定 |
| `no-index-top` | `∀ d → (h₁ d ≡ zero → ⊥) → (o : Ok (a₁ (suc d))) (ν : E.T) → IndexOK (a₁ (suc d)) o (rbᶻ (a₁ (suc d))) (h₁ d) (ink self) ν → ⊥` | `pres` 给不出顶槽位上链的一步 | 编译否定 |
| `chain-below` | `∀ ℓ (o : Ok ℓ) r (B : Base ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) (t a κ ρ : E.T) → κ E.<ᵀ ρ → GR.R (at ℓ p) (E.Ωt ρ) (proj₁ (B (at ℓ p) (posW ℓ p))) → ChainAt ℓ o r B t a p κ g` | 下标低于槽位底的读法时，链不需要 `StepU′`（推广 `YiS2Chain.gamma-bound`） | 编译 |
| `tight-from` | `∀ d → StepU′ (a₁ (suc d)) → TightStep d` | `TightStep` 是 `StepU′` 的实例 | 编译 |

#### 4. 第一个障碍

**引理**：`TightStep d`，即顶槽位上紧的链的一步。陈述逐字如下：
```
TightStep d = OK (D.dn Bᴱ (suc d)) → (t : E.T) → PrefixU (D.dn Bᴱ (suc d)) t
  → (a κ : E.T) → GR.Nu (a₁ (suc d)) (inj₁ (inj₁ tt)) κ → E.cof a ≡ E.cΩ κ
  → (g : Tr (h₁ d) → Tr (a₁ (suc d))) (n : ℕ) (z : Tr (h₁ d))
  → GR.R (h₁ d) (E.γT (t ++ a) κ n) z → GR.R (a₁ (suc d)) (E.fsT a (E.γT (t ++ a) κ n)) (g z)
  → GR.R (h₁ d) (E.γT (t ++ a) κ (suc n))
      (feedᴸ (a₁ (suc d)) (proj₂ oᴱ (suc d)) (rbᶻ (a₁ (suc d))) (D.dn Bᴱ (suc d)) (inj₁ (inj₁ tt)) g z)
```
- 它是 `YiSUIface.StepU′ (a₁ (suc d))` 的实例，实例化参数为：`o = proj₂ oᴱ (suc d)`，`r = rbᶻ (a₁ (suc d))`，`B = D.dn Bᴱ (suc d)`，`p = inj₁ (inj₁ tt)`。它是 `Kit (a₁ (suc d))` 的分量。
- 它不是 `LowKeepˣ` 的实例：源层号 `a₁ (suc d)` 与分支层号 `hh d z` 都没有 `Lbl`（编译）。
- `Tail` 直接需要它，因为孩子要取遍一切 c。
- `FirstMissing` 需要的是 `a₁ (chain 2)` 子层号上同形的结点（`tw 1 ⊕ (P ⊕ ↑ (h₁ (d+1)) …)`，d ≥ 1）。这一条是判断。`no-index-⊕` 对这些子层号一律成立（编译）。

**是数学挡住.** 最终文件无堆墙（约 1.6G）。这条引理既没有证明，也没有否定。挡住的是现有三种证据域在这一处都为空：
- `IndexOK`：最小表下为空（`no-index-top`）。到达 `h₁ d` 必须经 `tw 1` 叶子的非零指定孩子，而最小表在那里缺项。
- 下界读法的框架：只容空下标（`block-frame`），而实际下标是 d 的读法，d ≥ 1 时不为空。
- 精确标签：不存在（`no-lbl-hh`）。

纸面方向（判断，未编译）：把框架换成只在实际推导的 κ 处检查，并把量化域限在读回域的推导上（前缀读空，回退行只承载平凡参照）。阻挡结点上实际 κ 的比较看来可以满足。另一种可能是继承底带足够大的 ψ_κ 参照、从而给出这条链，但那要实际站折到 `h₁ d` 的保持，仍是整体引理的实例。

#### 5. 偏离与事故

- **堆耗尽 4 次（退出 251，8G）**，都在实例声明上：
  - 第一版整文件撞墙一次；按声明二分，定位到 `first-fromᴱ`（TL2 撞墙一次）。
  - 第一次改写：只用 `Gᴱ` 名字（TL3），仍撞墙。
  - 第二次改写：用自己的模块拷贝，但声明类型里自写 `Gvᴱ.chain 2`（TL4），仍撞墙。
  - **按简报，两次改形状仍撞墙应停下；我做了第三次改写**：把 `FirstFrom`、`FromPres`、`FromKit` 都定义在变量模块里，并重建 `two′`，结果通过。这是对停止规则的偏离。
  - 机制（判断，依据声明二分，没有跑 `--profile`）：同一个 `chain 2` 有两种拼法相比较时，检查器把 `chain 2` 化到弱头范式，等于整次折叠。
- **30 分钟时限**：第 0 步临时文件约在开始后 35 分钟编译通过。这是估计，没有计时，可能超时。
- **没有读、只凭转述引用的**：
  - 没有读 Bedrock 性能手册原文，C-1、C-9 等规则只按 `EBOHandbook` 4.2、4.6 节的摘要用。
  - 没有读 `Reports-2026-11-16/YiGL.md`，没有读 `raiseR` 的内部。
  - 第七十批的结论按简报转述使用；`YiSY*`、`YiGL*`、`YiGT*`、`YiGIRel`、`YiTBRow`、`YiRW*` 的相关定义都读过。
- 同批其他三路的产出没有读，也没有导入；没有改动任何已有文件。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：同步对象上的 Tail（前缀 YiTL，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。作者 2026-11-16 定第七十一批，本路选项原文 "同步对象上的 Tail"，执行方 Opus 5.5。主审的推荐里本路排在最后（理由：它是整体引理的实例，按作者 11-11 的规则 "几路都要同一条未证引理时先闭合引理再派"）；作者仍选了它。所以本路是**直接攻一个具体实例**，看能不能不等整体引理就拿下，或者在拿的过程中给整体引理提供一个完整的实例。同批另三路（工程 YiXP、数学 YiEL、摆脱侧 YiWB）与你互不导入。

#### 第七十批的结果（主审 8G 冷编复核过，读陈述）
- **整体引理 YiGL**（`probes/OCF/Lean/YiGL*`）：读回域 `YiGLDom.Dom`（`dz`、`dC`、`dN`、`dc`）上 Leaf 对一切层号形状成立（`dom-top`），接口 `YiAbsGIface` 的 Leaf、Lift 无前提成立（`leafᴰ`、`liftᴰ`），全域 Leaf 的反例在域外（`not-in`）。LowKeep 未证：现有条件保持引理 `YiGTFold.pres : ∀ ℓ → Kit ℓ → PresAt ℓ` 要的框架 `NodeFrame`，在槽位标签取下界读法 `Rd` 时，对一切后继形状层号无居民（`YiGLFrame.no-frame-S`、`no-tree-child`）；换成精确标签 `YiGLFrame.Lbl`（`Lbl zero ν = ν ≡ []`；后继逐字；ℕ 极限要 `cof ν ≡ cω`、`NF ν`、`LimAt ν`、各孩子标签与基本列的比较；Ω 形状取 `⊥`）后有居民（`frameˣ-S`、`YiGLNode.frameᴸ-S`）；`uniq`、`below`、`lbl-rd`；精确标签的关系族 `YiGLExact.Rˣ`（第 0 层与 `GR.R` 相同），`topˣ`（含 ℕ 极限层号；`topˣ-ω` 在 `no-omega-seed` 的对象上成立），`LowKeepAtˣ`、`LowKeepˣ`（陈述，无居民），`prefixˣ-B₀`、`betaˣ`；`YiGLNode.node-rowˣ`（结点一行的条件定理）。回报 `probes/Survey/Reports-2026-11-16/YiGL.md`。
- **对位调整 YiSY**：`ebo-from-stations′ : (∀ n → Kᴱ′ (suc n)) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`；第 3 站下界归约为 `YiSYSmall.k2′-from-tail : Gᴱ.Tail → Kᴱ′ 2`，`Tail` 未证；`two-shape`、`kl-index`。
- **摆脱侧 YiLX**：`YiLXClimb.climb`（字面路径上源 Ω 树折叠按 `YiVRRel.Le` 不高于目标的，一般形式，不读记号），前缀 0、1；前缀 2 起底前提被否定（`YiLXOne.no-base-two-at0` 等：源底里分支取值在第 0 层的 Ω 结点，`Le` 放不进极限链之下）。
- **配对否定 YiVN**：`YiVNIdx.Gen.no-value-index-mono≈`：以下标的树侧值序作前提的下标单调不成立（谓词太宽）。所以前提只能是字面路径、关系或读回域。
- **作者定**：主线停逐项，改攻整体引理；参照只用记号关系 M（`OCF.Align.Level` 的下标类型只有 `zero`、`suc`、`lim`，接不到终点）。

#### 本路的对象（YiSY 已编译）
- `YiSYSmall` 的 `module Gen (a : Tr zero → L) (o : Ok (nd (sΩ zero) a)) (B : Base (nd (sΩ zero) a)) (β : Tr⁺ zero)`，同步对象 `kl 1 = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))`（`kl-shape : kl 1 ≡ nd (sΩ zero) a₁`），实例 `Gᴱ`（继承底 `Bᴱ`，沿 `p*` 降下来）；`Low-at γ X = ∀ e → K.M⁰ γ e → (h : E.HC (S γ)) → Rt h ≼ K.readRW (X e)`，`S γ = E.ψ [] (E.fsT (E.ΩTower 3) γ) ∷ []`，`γ = E.γT (E.ΩTower 3) []`。
- 已成立：`sf₁ᴱ`、`so₁ᴱ`（γ 第 0 项的两半）、`chain-two : K.M⁰ (γ 1) (chain 2)`、`start-sync`。
- 条件：`k2′-from-tail : Gᴱ.Tail → Kᴱ′ 2`，`Tail = ∀ m → Low-at (γ (suc m)) feed × Low-at (γ (suc m)) (λ e → proj₁ (out e))`；第一个实例 `Gᴱ.FirstMissing = (h : E.HC (S (γ 1))) → Rt h ≼ K.readRW (proj₁ (out (chain 2)))`，即 ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}}) 不高于第 2 个链点的输出。
- `two-shape`（编译）：e ≥ 2 时输出层号 `a₁ e` 的 Ω 下标层是 `one` 或更高，其中的回灌链在不可数层上。

#### 要做的（按序）
0. **最小检查**：展开 `out (chain 2)` 到层号 `a₁ (chain 2)` 上的折叠，写出要证的关系链（哪一处要 Leaf：`↑` 读回不低于 γ；哪一处要 LowKeep：前缀 `tw 1 ⊕` 下、目标为第 1 层一类的下标保持），确认类型。可以用已编译的 `YiGLDom`（读回域上的 Leaf）、`YiGLExact.topˣ` 等。不成立就停下回报。
1. **攻 `FirstMissing`**（只对这一个实例），再试 `Low-at (γ 1) feed`，从而 `Tail 0`。
2. 能走下去就对 m 归纳得 `Tail`；挡住就交第一个挡住的引理，精确到这个对象上的陈述，并说明它是不是整体引理 `LowKeepˣ` 的实例（是的话写出实例化的参数）。

#### 规则（主审写给内部子智能体，必须照做）
- **先读** `AGENTS.md` 全文；性能问题先查 `probes/Survey/EBOHandbook.md` 4.2、4.6 节与 Bedrock 性能手册 `<Bedrock>/dev/cubical-agda-performance.md` 的 C-9（在变量上陈述、定义等式作假设、在唯一调用点实例化）、C-10（具体的站作 opaque 原子或模块参数）、S-1/S-3（重的构造在出生处封进 opaque，并在同一块里导出规格等式）、C-24、Q-1（`--profile=definitions`）、Q-23（量底价、二分）、H-6（251 之后不原样重跑）。
- **只新建文件**，放 `probes/OCF/Lean/`，用你的前缀（见上）。不改任何已有文件，不碰 `src/`、`archive/`，不碰别的前缀。中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行（判决与档位、做了什么、不否定什么、入口）；代码之间只写范围与不显然的理由。一次性的试验放你的临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要把前三个也写上，否则报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（写 `<实验目录>`、`<仓库>`）。
- **编译**（仓库根目录）：`agda +RTS -M8G -RTS --library-file=<库文件> -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`；临时目录的纯 `.agda` 另加 `-i <你的临时目录>`。退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 Agda 内部错误。报退出码不经过管道。同时只跑一个 agda，堆上限 8G（同批另有三路，主审也在编译）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下，写字面路径）。大的 `refl` 前加 `timeout 600`。
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

