# 配对否定：找塔第 1 项上的反例（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-16 15:24 至 16:40 |
| 工具调用 / agda 编译 (粗数) | 94 / 19 |
| token (usage 字段，按消息去重) | 输出 448855；新写入缓存的输入 926094；读缓存的输入 33579937；其余输入 164 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `YiTF` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 3 件全部退出 0，禁用构造 0；关系档：塔第 1 项上链步接口 StepU′、WholeU 不成立（前提全部实填），TightStep 1 等价于实际底的前缀前提不可满足；值档未做成（缺 twᶻ 1 的上界），不触发改定义 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b72/YiTF.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiTF 回报：配对否定，在塔第 1 项上找反例（执行方 Opus 5.5）

#### 1. 判决

**对纲领与目标意味着什么。** 新增 3 个验收文件（第 4 层，读记号）。树、折叠、合法性、比较表一行都没有改。值档（b）没有做成，所以不触发"停下交作者改折叠"。关系档有两条编译过的结论，都针对 GR.R 量化分支的接口：
- 在塔第 1 项本身，LowKeep 的链步接口 `StepU′ (tw 1)` 不成立，`WholeU (tw 1)` 也不成立。所有前提都已实填：最小表 `rbᶻ`、标准底、`PrefixU` 由 `leafC` 给出。
- 同步对象孩子 2 上的共用陈述 `TightStep 1`（即 `TightStep (suc zero)`，层号 `a₁ 2`）等价于"它自己的前缀前提 `PrefixU (D.dn Bᴱ 2) t` 对一切 t 都不可满足"，两个方向都已编译。所以 `TightStep 1` 要么为假，要么只是空真。无论哪种情形，它都不能用来推出 `Kit`、`pres` 或 `FirstMissing`。

机制是同一个。一个分支把树放进 tw 1 叶子的孩子 2，形式是直接嵌入 `up zero 2 (c+1)`。GR.R 允许这棵树读作 Ω₁ 级的项。但折叠到第 1 层时，路径在叶子上只能经指定孩子；最小表在 (2, 2) 处没有条目，于是走退路，得到"底 ⊞ 可数尾巴"。这棵树的 R 读法都低于 Ω₁+Ω₁（编译），而记号要 ψ₁(Ω₁) 一类。这否定的是关系 GR.R（下界读法）在宽量化下的陈述，不是实际对象的值。给构造一路的含义是 YiTL 的纸面方向——"前缀读空，退路行只承载平凡参照"——是必需的，不是可选项（这一句是判断）。

**各步进度**
- 第 0 步：完成。
  - 编译的局部事实：tw 1 叶子上，槽位在孩子里时，对任何证据、任何非零且不含 Ω 的目标路径，折叠都走链（`kp-leaf`）。同步对象参照的第 1 项 ψ₁(Ω_Ω) 在第 1 层保留（`ref₁-cof`、`ref₁-keep`）。
  - 两边的值：在我选的结点上，树一侧是 Ω₁ 树加可数尾巴（`out-form`，`refl`）；记号一侧是 ψ₁(Ω₁)。值的比较是判断。
- 第 1(a) 步：交了 `¬StepU′ (tw 1)`、`¬WholeU (tw 1)`，以及 `TightStep 1` 的等价刻画。没有得到无条件的 `¬TightStep d`，原因见第 4 节。没有做 `¬KeepOut c`，因为它要值的上界。
- 第 1(b) 步：未走通，见第 4 节。
- 第 2 步：没有编译出实际输出的上界。纸面分析见第 4 节。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| tw 1 叶子上，槽位在孩子里、目标非零且不含 Ω 时走链 | `YiTFTw1.kp-leaf` | 编译定理 |
| 同步对象参照第 1 项在第 1 层保留（共尾 Ω₁） | `ref₁-cof`、`ref₁-keep` | 编译（`refl`） |
| 第 0 层关系只读出低于 Ω₁ 的项 | `YiTFBound.bZ` | 编译定理 |
| 第 1 层：无 Ω 结点的树读法低于 Ω₁；Ω₁ 树加可数尾巴的树读法低于 Ω₁+Ω₁ | `bD`、`bS` | 编译定理 |
| `StepU′ (tw 1)`、`WholeU (tw 1)` 不成立，前提全部实填 | `no-stepU′-tw1`、`no-wholeU-tw1` | 编译否定 |
| `TightStep 1` ⇔ 对一切 t 实际底的 `PrefixU` 都不可满足；`OK` 已实填 | `no-tight′`、`vacuous`、`okᴱ` | 编译定理 |
| 实际继承底在第 1 层等于 Ω₁ ⊞ Y₁ ⊞ Y₂，且 Y₂ 就是 `twᶻ 1` | `β-form`、`Y₂-tw` | 编译（`refl`） |
| 该结点上树值约为 Ω₁+可数，记号值约为 Ω₁² | — | 判断 |
| 实际底的 `PrefixU` 在某个怪异 z 给出的槽位层号上不成立（`YiLLLeafNeg` 的机制加 tw 1 前缀），若是，`TightStep 1` 空真 | — | 判断，未编译 |
| 实际对象 out 2 是否低于 ψ₀(Ω_{Ω₂}) | — | 未判定 |
| 换成表无关的 `kp` 行（槽位在孩子里，经 `inc` 恒走链）可得同类反例，界要取 Ω₁·ω | — | 判断，未编译 |

#### 2. 文件表

| 文件 | 物理行 | 非空非注释代码行 | 冷编 |
|---|---|---|---|
| `probes/OCF/Lean/YiTFBound.lagda.md` | 275 | 216 | 删自身接口后 6G 冷编，退出 0；日志只有本模块的 Checking 行；最大驻留约 1.41G，约 16 秒 |
| `probes/OCF/Lean/YiTFTw1.lagda.md` | 156 | 103 | 同上，退出 0；约 1.63G，约 18 秒 |
| `probes/OCF/Lean/YiTFTight.lagda.md` | 171 | 120 | 同上，退出 0；约 1.77G，约 20 秒 |

- 检索结果：禁用构造 0，本机路径 0，`Funext` 0。三件都标为读记号，所以不需要导入闭包检查。
- 一次性试验 `YiTF0` 到 `YiTF6`（纯 `.agda`）与日志都在 `<实验目录>/work/YiTF`，不在仓库里。

#### 3. 定理表

记号：`Ω₁ = ψ (𝟏 ∷ []) [] ∷ []`，`ΩΩ` 是两个 Ω₁ 主项的列表，`a₂ = E.Ωt (E.natT 2)`，`cΩ₁ = proj₁ (Ωt one)`。档：除 `ref₁-keep`（`refl`）外均为编译定理。

| 名字 | 逐字的陈述 | 白话 | 文件 |
|---|---|---|---|
| `bZ` | `∀ {s y} → H.M⁰ s y → s <ᵀ Ω₁` | 第 0 层只读出可数项 | YiTFBound |
| `bD` | `∀ {t x} → GR.R one t x → D0 x → t <ᵀ Ω₁` | 第 1 层无 Ω 结点的树只读出低于 Ω₁ 的项 | YiTFBound |
| `bS` | `∀ {t x} → GR.R one t x → S x → t <ᵀ ΩΩ` | Ω₁ 树加可数尾巴只读出低于 Ω₁+Ω₁ 的项 | YiTFBound |
| `L2Ω` / `L2ΩΩ` | `∀ {s} (v : Vω s) → Ω₁ ≤ᵀ s → Ω₁ ≤ᵀ fω v 2`（ΩΩ 版同形） | ω 共尾项的第 2 项不低于阈值 | YiTFBound |
| `LΩ` | `∀ {s μ} (v : VΩ s μ) → μ ≡ [] → fΩ v (E.natT 2) <ᵀ Ω₁ → s ≤ᵀ Ω₁` | 下标为空的 Ω 共尾项，第 2 项可数则本身不超过 Ω₁ | YiTFBound |
| `rd-zero` | `∀ {κ} → GR.Rd zero κ → κ ≡ []` | 第 0 层只读作空 | YiTFBound |
| `kp-leaf` | `∀ {K} → NoΩᵀ K → (K ≡ zero → ⊥) → (o : Ok (tw 1)) (c : Tr zero) (t : Pos⁼ (zero ⊕ ↑ zero c)) (w : K ≤ tw 1) → kp (tw 1) o (inj₂ (c , t)) w ≡ nothing` | 叶子上树走链 | YiTFTw1 |
| `ref₁-keep` | `∀ η → E.fsT ref₁ η ≡ E.ψ (E.natT 1) (E.Ωt η) ∷ []` | 记号保留（`refl`） | YiTFTw1 |
| `pf` | `PrefixU (B₀ (tw 1)) []` | 标准底在 tw 1 上满足前缀前提 | YiTFTw1 |
| `no-stepU′-tw1` | `StepU′ (tw 1) → ⊥` | 塔第 1 项上链步接口不成立 | YiTFTw1 |
| `no-wholeU-tw1` | `WholeU (tw 1) → ⊥` | 一切分支版本也不成立 | YiTFTw1 |
| `LD` | `∀ (o : Ok (hh (suc zero) cΩ₁)) (B : Base (hh (suc zero) cΩ₁)) (v : one ≤ hh (suc zero) cΩ₁) (β : Tr⁺ one) → S (proj₁ β) → S (proj₁ (TB.ψ (hh (suc zero) cΩ₁) o (rbᶻ (hh (suc zero) cΩ₁)) B one v β W₁))` | 对一切证据与路径，输出都是"底加可数" | YiTFTight |
| `β-form` / `Y₂-tw` | `proj₁ (D.dn Bᴱ (suc (suc zero)) one (ink self)) ≡ proj₁ ((Ωt one ⊞ Y₁) ⊞ Y₂)`；`proj₁ Y₂ ≡ twᶻ 1` | 实际继承底的形状 | YiTFTight |
| `okᴱ` | `OK (D.dn Bᴱ (suc (suc zero)))` | `TightStep` 的 `OK` 前提成立 | YiTFTight |
| `no-tight′` | `(t : E.T) → PrefixU (D.dn Bᴱ (suc (suc zero))) t → TightStep (suc zero) → ⊥` | 前缀前提可满足就推出 `TightStep 1` 为假 | YiTFTight |
| `vacuous` | `((t : E.T) → PrefixU (D.dn Bᴱ (suc (suc zero))) t → ⊥) → TightStep (suc zero)` | 前缀前提不可满足就推出 `TightStep 1` 空真 | YiTFTight |

前提可满足：
- `no-stepU′-tw1`、`no-wholeU-tw1` 的每个前提都给了实例。
- `no-tight′` 的前提 `PrefixU (D.dn Bᴱ 2) t` 可满足与否未判定。这条定理是等价刻画的一半，不是无条件否定。

#### 4. 第一个障碍

**(a) 无条件 `¬TightStep 1`：数学上挡住。** 需要证 `PrefixU (D.dn Bᴱ 2) t`，也就是 a₁ 2 一切槽位层号上、对 `Rd` 读法的 Leaf，其中包括 `tw 1 ⊕ …` 一类层号。现有结果只到条件版（`YiCNAccept.Leafᶜ`）。
- 判断（未编译）：取 z 为第 1 层里分支只在 c=1 非零的 Ω 结点，可以造出槽位层号 `tw 1 ⊕ ↑ one z`。它可读作 Ω+1，但其 Ω 树的读法不超过 Ω_Ω 一类。机制同 `YiLLLeafNeg`，加上 tw 1 前缀。
- 若此判断成立，`PrefixU` 不成立，`TightStep 1` 空真。

**(b) 值档：工程上挡住（工具缺失），数学上未判定。**
- 任何实际输出的值上界，都必须先界住 `twᶻ 1`：
  - 第 1 层继承底含 `ι (twᶻ 1)`（`β-form`、`Y₂-tw`，编译）；
  - 第 0 层继承底不低于 `twᶻ 1`（`YiSYSmall.fb`，已有）。
- 现在没有 `twᶻ 1` 的上界：`YiXVStart.Goalᶻ` 只是类型。标准底版本的同步对象也含真实的 Ω_Ω 前缀，同样需要这一级的上界。

**纸面判断：值可能在哪一步保住。**
- 对实际的 out 2 和参照 ψ₀(Ω_{Ω₂})，有两个方向相反的效应，我判断不了净结果：
  - 损失：↑z 中非前缀的 Ω 形状结点下标低于目标时，下标槽位被 `kh` 推进 tw 1 叶子的孩子，`kp` 走链。记号在那里保留，树只取可数长的链。
  - 补偿：c=0 分支的链在 tw 1 层，用的底含 `Ωt (tw 1)`。自折叠把孩子嵌入提升成孩子槽位上的 Ω 结点。叶子自己的下标槽位（`inj₁`，被推进目标所在的孩子）是唯一被保留的，它的分支约为 ψ_d(Ω_c)，对一切可数 c 取上确界后可达 ψ_d(Ω_Ω) 量级。
- 所以值若保住，判断是经叶子下标槽位加自折叠，不是经非前缀结点。第 2 项以后（γ₂ = ψ₁(Ω_{γ₁}) 仍是 Ω₁ 共尾、记号保留）是否对得上，是我最大的不确定处。
- 对我构造的非规范分支：树值是 Ω₁ 加可数，参照是 ψ₁(Ω₁)，差的是整段 Ω₁·ω 的幂。这是判断；编译的只是读法上界 `bS`。

#### 5. 偏离与事故

- **30 分钟时限可能超时**：第一个临时文件 `YiTF0` 写出前读了大量文件，估计开始后约 50 分钟才编译，没有计时。
- 没有堆耗尽（全程最大约 1.9G），没有 251 或 124。退出 42 共 6 次，都是普通类型错误，修改后通过；同一处没有两次重新设计。
- 临时文件编译时，在命令行加了 `-W noUnsupportedIndexedMatch`。
- (a) 交付的是 `¬StepU′ (tw 1)`、`¬WholeU (tw 1)` 加 `TightStep 1` 的等价刻画，不是简报所写的无条件 `¬TightStep d` 或 `¬KeepOut c`。
- 反例依赖最小表 `rbᶻ` 在 (2, 2) 处缺条目。换成对角有条目的表（如 `YiTBRow.rb1`），这个实例会走第一臂；表无关的版本只有判断。
- **没有读、只凭转述或签名引用的**：
  - `EBOHandbook` 4.2、4.6 节与 Bedrock 性能手册没有读，因为没遇到堆问题。
  - `YiEL*`、`YiWB*`、`YiXPExact/Frame/Rows`、`YiVNIdx`、`YiORBound` 没有读，第七十一批结论按简报转述使用。
  - `YiGLDom`、`YiCNAccept`、`YiXVStart` 只读了文首。
  - `YiLLCheck.leafC`、`YiVRRel.NoΩ≤`、`YiTBFam.ψ-⊵`、`YiKSDesc._⊑¹_` 只按签名使用。
  - 读过的：`YiTLReduce` 全文，以及 `YiRW*`、`YiTBRow`、`YiMTTab`、`YiSYReduce`、`YiSYSmall`、`YiSYDesc`、`YiGIRel`、`YiHCRel`、`YiLLLeafNeg`、`YiXPNeg`、`YiFOValue`、`YiXUFirst`、`YiGIInst`、`YiLKIface`、`YiSUIface`、`EboLeanView` 的相关部分，以及 YiTL 回报留档。
- 同批其他路的文件（`YiKT*`、`YiMG*`、`YiTA*`、`YiRR*`）没有读，也没有导入；没有改动任何已有文件。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：配对否定，找塔第 1 项上的反例（前缀 YiTF，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。本路选项原文 "配对否定：找塔第 1 项上的反例 (Recommended)"。构造一路 `YiKT` 在证同一件事；你们共用的陈述是 `YiTLReduce.TightStep`、`Gvᴱ.KeepOut`/`KeepFeed`；不导入彼此的文件。AGENTS："构造与否定配对"、"前提要可满足"、"归到已知的墙要逐条核机制"。

#### 作者的决定与背景（2026-11-16）
- 作者定：主线停逐项，改攻整体引理（读回域上的 Leaf 加 LowKeep）；参照只用记号关系 M。第七十二批选项原文："构造：塔第 1 项上的 LowKeep (Recommended), 配对否定：找塔第 1 项上的反例 (Recommended), 合流两个关系族 (Recommended), 记号侧：截断加法与部分和链点"；摆脱侧 "右边放宽的底关系 (Recommended)"。同批五路：构造 `YiKT`（Fable 5.2）、配对否定 `YiTF`、合流 `YiMG`、截断加法 `YiTA`、摆脱侧 `YiRR`（Opus 5.5），互不导入。
- **第七十一批的结果**（主审 8G 冷编复核过，读陈述；回报在 `probes/Survey/Reports-2026-11-16/`）：
  - `YiXPExact.lowKeepAt-noΩ : ∀ ℓ → NoΩ ℓ → LowKeepAtˣ ℓ`、`lowKeepˣ`：精确标签 `YiGLFrame.Lbl` 下 LowKeep 对一切不含 Ω 形状的层号无条件成立；保持引理族的一般各行不用槽位标签的性质（`YiXPRel`、`YiXPRows`、`YiXPFold` 对抽象 `Lab` 参数化），框架只靠 `uniq`、`below`、`YiXPFrame.lbl-path`。`YiXPNeg.no-index-tree-tw1ˣ`：折叠 `YiRWFold.kp` 对 "Ω 形状、槽位在孩子里、路径经 `inc`" 恒为 `nothing`（走链），记号一侧在孩子里更深的槽位处保留，于是逐槽位证据域 `IndexTree` 在塔第 1 项上为空（只否定证据域）。
  - `YiELLim.limAt : ∀ u → cof u ≡ cω → LimAt u`；`YiELZero.no-all`（带下界证据 `M⁰` 的第 0 层树不都有精确标签）→ 第 0 层分支前提要换精确读回 `Ex⁰ η d = Lbl (↑ zero d) η`（`ex→M⁰`、`ex-lower`、`child-lbl`）；`YiELOmega.Lblᵒ`（下标层为第 0 层的 Ω 形状层号有精确标签，带 `CofΩ` 字段）、`uniqᵒ`、`belowᵒ`（要 `PosOk`）、关系族 `Rᵉ`（第 0 层分支前提用 `Ex⁰`）、`topᵉ`、`lbl-layer`；`YiELChain.ex-next`、`ex-add`（要 `HdLe p s`）。`Rˣ` 与 `Rᵉ` 之间没有映射。
  - `YiWBNeg.Neg.no-next`、`no-base`：只放宽左边的底关系（含最宽的 `Ω≼`）给不出两条实际链前缀 2 的底前提；`val-left-right`：值序上成立，用的是右边一个第 1 层槽位结点的**非首分支**（该槽位层号自己的 Ω 树）。
  - `YiTLReduce`：同步对象（`kl 1 = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))`）各孩子层号 `a₁ c` 上 Leaf 无前提（`leaf-a₁`）；`tail-fromᴱ`、`k2′-from-keep : (∀ c → Gvᴱ.KeepOut c) → (∀ c → Gvᴱ.KeepFeed c) → Kᴱ′ 2`（`KeepOut c = ∀ {s} → GR.R (a c) s (proj₁ (Ωt (a c))) → (h : E.HC (E.ψ [] s ∷ [])) → Rt h ≼ K.readRW (proj₁ (out c))`）；`no-lbl-a₁`（这些层号没有 `Lbl`）；第一个挡住的引理 `TightStep d`（顶槽位上紧的链的一步，`StepU′ (a₁ (suc d))` 的实例，陈述已编译），三种现有证据在那里都为空（`no-index-top`、`block-frame`、`no-lbl-hh`）。纸面方向（YiTL 判断）：把框架换成只在实际推导的 κ 处检查，量化域限在读回域的推导上（前缀读空，退路行只承载平凡参照）。
- **决定性问题**（主审判断）：塔第 1 项（及以它为前缀的层号）上的 LowKeep 成不成立。成立要一种新证据；不成立就要改折叠的那一行（第 4 层逼出的定义改动，交作者）。
- 其他已编译的事实：`YiVNIdx.Gen.no-value-index-mono≈`（下标的树侧值序不能作下标单调的前提）；`YiFOValue.fallback-prefix`（退路保留此前折叠的值）；`YiXUFirst.first-ceiling`（干净对象第一支 ≤ ψ₀(Ω₄)）；`YiORBound.original-neg`（封闭关系下原行仍不过判据）。

#### 要做的（按序）
0. **定位候选反例**：在读回域内（同步对象 `kl 1` 的实际孩子 `a₁ c`，或塔第 1 项为前缀的实际层号），找一处 "记号一侧保留、树一侧走链" 的结点，写出两边的值：树一侧的折叠输出与记号一侧的参照。纸面算清，标判断。
1. **两档否定，分开交**：
   - (a) 关系档：编译 `¬ TightStep d`（某个具体 d）或 `¬ KeepOut c`（某个具体 c），说明它否定的是关系 `GR.R`（下界读法）下的陈述，而不是值。
   - (b) **值档**（决定性）：编译一个值的上界，证明某个读回域内实际的折叠输出（如同步对象 `out (chain 2)`、或 `a₁ (suc d)` 上 Ω 树折到第 0 层）**严格低于**它的记号参照（如 ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}}) 一类）。若做成，这是 "要改折叠定义" 的依据：**停下，交作者**，不要提改法以外的结论。
2. 若 (b) 做不成：交出你算到的最好上界与它和参照的差距，说明纸面上值在哪一步保住了（这是给构造一路的信息）。

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

