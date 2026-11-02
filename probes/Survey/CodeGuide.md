# 外部序数代码: 查阅手册

> 证据记录在 [code/](code/) 的四份报告 (下文写作 TT = [TypeTheoryTrees](code/TypeTheoryTrees.md), LP = [LeanPsiNotations](code/LeanPsiNotations.md), ML = [MahloLevelRules](code/MahloLevelRules.md), WO = [WellOrderProofs](code/WellOrderProofs.md)). 记号本身的结论在 [OrdinalNotationsGuide.md](OrdinalNotationsGuide.md) (下文 "手册"). 本文只放结论, 用来查. 状态日 2026-11-02.

**四份分析全是静态的.** 没有构建、运行或类型检查任何外部代码, 唯一例外是 `ExBuchholz` (手册 §5.2, 只有它是 **机检·已构建**). sorry/axiom 数都是文本检索, 不是 `#print axioms`.

**来源层级** (与手册同):

| 标记 | 含义 |
|---|---|
| **机检·已构建** | 他人代码, 我们构建过, 公理来自 `#print axioms`. 只有 `ExBuchholz` |
| **机检·只读** | 他人 Lean/Isabelle/Agda/Coq 代码, 读过源码或 README, **从未构建** |
| **同行评审** | 正式发表的论文 |
| **人工证明(社区)** | 社区写出了证明, 未经第二人核查 |
| **测试** | 有限样本, 不是证明 |
| **社区无证明** | 社区定义或声称, 没有证明 (含 JS 实现) |
| **推断** | 我方的推理, 仓库里没有这条陈述, 也没有机检 |

指向本项目代码时用手册的 **机检·我方**; 本次没有重新编译.

**路径简写** (提交钉在行内, 行号指该提交):

| 简写 | 仓库 @ 提交 | 前缀 |
|---|---|---|
| `gl` | koteitan/googology-lean @ `6da2de5` | `E/` = `Googology/Notation/ExBuchholz/`, `P/` = `Googology/Notation/InaccPsi/` |
| `pss` | koteitan/pss-proof @ `d1be91f` | `W3` = `lean/Buchholz-1987/Buchholz-1987-2.3-W.lean`, `W4` = 同目录 `-2.4-2.8.{lean,md}`, `SY` = `lean/OTB-well-founded-syntactic/OTB-well-founded-syntactic-`, `S8` = `isabelle/8/Support_8_C.thy` |
| `bt` | zball-bz/btbms-formalization @ `4f31c78` | `P/` = `lean/BTBMS/Plan/` |
| `hz` | hzyhhzy/column-ordinal-notations-hzy @ `2da3765` | `O/` = `lean/Omega-LRD3/src/` |
| `ph` | Phyrion1343/1Y-Well-Ordering-Lean @ `03d794f` | `RI/` = `formalization/OneY/RootIndexed/` |
| `cq` | coquand/agda-ordinal-analysis-id1 @ `1f977e0` | 全在 `IDHAT/` 下 (报告省略了这一层) |
| `kv` | AndrasKovacs/universes @ `08e56f2` | `agda/` |
| `cz` | takahashi-yt/czf-in-mahlo @ `b8aa846` | |
| `xu` | cj-xu/OrdinalNotations @ `4690b68` | `src/*.lagda` |
| `hy` | coq-community/hydra-battles @ `ed8e604` | `theories/ordinals/` |
| `sw` | SteveWmoc/lean-ordinal-analysis @ `0aa3551` | `OrdinalAnalysis/` |
| `nr` | Naruyoko/googology @ `958ac91` | `impl` = `padicBotRathjen/implementation.js` |
| `ex` | DavidExmachina/garden-of-ordinals @ `618e814` | `ord` = `ASSETS/ordinal.js` |
| `br` | koteitan/bms-rathjen @ `7bde9d7` | `lean/TM/` |

"省什么" 相对于从头写. **没有一行是现成可搬的**: 目标全是 Agda 重写, 能否抄见 §5.

## 1. 按用途查

### (a) 标签路线: 关闭一般下标的标准形

| 代码 | 位置 | 层级 | 省什么 | 不给什么 |
|---|---|---|---|---|
| 相对不变量 `Trian` | `gl` `E/Closure.lean:193`; `Trian.psi_sub` 550, `G_lt_of_Trian` 359, `SubBound` 651, `Trian_case4` 968, `Trian_fs` 1127 | 机检·已构建 | 全 EBO 的不变量, **界相对于 $c$**. 可望一次替换 `StandardOmega` 的 `regSb`/`swapΩ`/`SELFΩ` 前提 `NoSb ⊎ HdIs` [推断] | `Trian` 读 `G` 列表, 要与 `Vis₁` 接桥; Lean 走 `tower`, 我方 `fsn` 结构递归 |
| 规则 6 起点的 `G` 界 | `gl` `E/Closure.lean:1192-1820`: `size_fs_W0` 1205, `no_small_between` 1323, `bach_pre` 1796, `bachmann` 1820 | 机检·已构建 | 只要大小论证, **不依赖 `OTFS`**, 可先做. 前缀 $p$ 不可省 | 这里的 `bachmann` 只是 `G` 界, 不是经典 Bachmann |
| 证明顺序 | `gl` `E/Closure.lean:1554-1830`: `towerOT_of_Bachmann`, `OTFS_aux` 1635, `OTFS_thm` 1827 | 机检·已构建 | 对 `size` 归纳并同时带 3.6 的组织方式; `Classical.choice` 已机检可去 (手册 §5.2) | Agda 重写本身. `omega`、`simp` 要换成显式推理 |
| 共尾 | `gl` `E/Cofinal.lean:294` `exists_lt_fs_numeral`, 135 `lt_fs_psi_of_G`, 257 `exists_lt_fs_tower` | 机检·已构建 | `cofin₁` 推广到全 EBO 的蓝本, 句法, 不依赖上面三行. 我方 `Cof6` 已同形 | 单调的陈述 (见 (c)) |
| `G` 小工具 | `gl` `E/Cofinal.lean:40-58`, `E/Sum.lean:256,274,292` | 机检·已构建 | 对应 `Vis₁`, 含 `vs` | |
| ℕ-下标对照 | `pss` `lean/Buchholz-1986/Buchholz-1986-3.3.lean:1354` `buchholz_fseq_closed_general`, 254 `G_control_bc` | 机检·只读 | 同一定理的另一种同时归纳; `Trian` 选不动时看 | **只读, 不抄** (无许可); 下标只到 ω, 绝对界在项下标上为假 |

### (b) `EBOI` 标尺与扩到 χ/M

| 代码 | 位置 | 层级 | 省什么 | 不给什么 |
|---|---|---|---|---|
| 第三意见的序与标准形 | `gl` `P/Term.lean:112` `cmp`, 194 `KLt`, 205 `NF` | 机检·只读 | 全句法, 可转写成脚本, 在里程碑序列上比 `EBOI` 的序 | 不能逐项翻译: 多 `phi`, `om`, `inacc`, `inaccW` [推断]; **无基本列**, 无 `dom`/`fs`/`cof` |
| "NF 恰好枚举值" | `gl` `P/Onto.lean:562`, `P/Correct.lean:1105,1166`; 假设 `P/Hyp.lean:169` `InaccSeq` | 机检·只读 | "这张表没漏项" 的外部引用 | 证明全靠 `val` 与基数算术, 不可移植; 不验证 `EBOI` 新规则 |
| 值域事实 | `gl` `P/Facts.lean:12-13, 224, 238` (F9, F10) | 机检·只读 | 核 $\psi_I$ 与 $\psi_{\Omega_{s+1}}$ 的值域约定 | 只说 $\psi_{I_n}(a)$ 是 Ω-不动点; $=\Lambda$ 是推断 (§6) |
| χ/M 的蓝本 | Maksudov/KawamoYurase 规则, 转写 `probes/Survey/scripts/mnot.py` | 社区无证明 + 测试 | 唯一 φ-free, `EBOI` 规则是其特例; 序层两项大小和下降 [推断, 手算] | KawamoYurase 全情形版无人实现; P2a 未修 |
| 分层架构 | `mnot.py:112-113`; `ex` `ord:944`; `br` `Order.lean` 不导入 `FS` | 社区无证明 + 推断 | 序与标准形不依赖一般基本列, `EBOI` 分层原样可用, 只是层 1 变厚 | 层 1 含 $\star,K,\ominus$ 后 `fsn-dec` 要全情形分析; 不是结构递归 |
| 规则 13–15 的第二意见 | `ex` `ord:1344` 起 (`ALPHA COF IS MAHLO`); `nr` `impl:1440-1450` (5.5.3) | 社区无证明 | 三个二元系统递归结构相同: 上一项喂给 $b[\cdot]$ | 外层形状不同, 互为共尾未证. **`br` 的 `fsN` 无此规则** |
| 不动点的短写法 | `ex` `ord:961-985` `isnormal`, `:1048`; `least` `:923` | 社区无证明 | χ 只查 $b<\chi_a(b)$, 不动点推给序; `least` 单值代替 $K$ 列表 | φ-free 下是否等价未知; 大小度量不再直接成立 [推断]; **无许可, 只看思路** |
| 序的对照表 | `nr` `impl:1517` 158 项升序; `kanrokotiInaccessiblePsi/implementation.js:947` 76 项 | 社区无证明 | 只作外部比对 | **无期望展开**; φ 原语要过 τ; BY-SA, 不可收进本仓库 (§5) |

可写成 `EBOI`/χ 回归测试的只有族内几条: ML §5.2 的 A; D 的递归形状; B、C、E、I 对 Maksudov 的前 4 项; G 的前 3 项. 其余只能是序嵌入断言 [推断, 手算].

**先做什么** [推断]: 无 M 的 χ 片段 (`χ b c`, $b$ 只取 $M$ 以下的项). 它已含层 1 全部难点, 不必碰 13–15 与 $\omega^\delta$. 改动清单见 ML §7.

### (c) 项侧的模与 `InaccStrike` 的 `GV`

对应 `InaccModulus*` 的前提 `Prem` (`InaccModulusRank.lagda.md:27`; 系列未提交, 总结文件 `InaccModulus.lagda.md` 尚不存在) 与 `InaccStrikeCommute` 的 `P-fs`, `P-pr`.

| 我方要的 | 代码 | 位置 | 层级 | 省什么 | 不给什么 |
|---|---|---|---|---|---|
| `cofi`: $s<t\Rightarrow\exists n.\ s\le t[n]$ | `exists_lt_fs_numeral` | `gl` `E/Cofinal.lean:294`; 一步版 401 | 机检·已构建 | 全 EBO, 纯句法, 不依赖 `OTFS_thm`, 无 `Classical.choice` | 见证是 ∃. 线性界 $n\le\mathrm{size}\,Y+1$ **只是推断** (§4 第 1 项) |
| 大小的语法 | `size` | `gl` `E/Sum.lean:203`; 我方 `InaccModulusSize` | 机检·已构建 / 机检·我方 | | **树上没有 `size`**: 同值的树范数不唯一 (`ω` 与 `ω⁺`) |
| 单调 $n\mapsto X[n]$, `dom=ω` | 无 Lean 陈述 | `gl` 只有项下标 `E/FS.lean:745`, 规则 6 部分 `:847`; `pss` `SY` `cofinality.lean:1022` `y4_N_mono` (Buchholz 系统); 我方 `fs-mono₁` 只到 `NF₁` | 机检·只读 | 证明形状 | 全 EBO 的版本要自己写, 其余分支是结构的 [推断] |
| `bach`: $t[n]$ 在 $t[n{+}1]$ 的 1-走步上 | **没有对应定理** | 最近的是 `Trian_fs_thm` `gl` `E/Closure.lean:1830`, `no_small_between` 1323 | 机检·已构建 (近邻) | `G` 形式与范数缝形式的 Bachmann | 字面单步形式为假 (§3); 走步形式要自己证 [推断] |
| `P-fs`, `P-pr` | `OTFS_thm`, `OT_psi_fs` | `gl` `E/Closure.lean:1827`, 617 | 机检·已构建 | 对 `isOTᵉ` 的封闭性证据 | |
| Ω-分支的显式见证 | `lt_fs_psi_of_G` | `gl` `E/Cofinal.lean:135` | 机检·已构建 | 见证 $\psi_{Z_0}(\beta)$, $\beta$ 只需压住 $G_{Z_0}(d)$; 对应 `Ωcof`/`ΩC`, 但对全 EBO | 这是否就是 `pen` 分支搬运的 `b` 是猜测 [推断] |
| 好输入类的模型 | `W_u` | `pss` `W3:62,115,121`; `SY` `main.lean:235` | 机检·只读 | 分层即 `Gs`, 只是层号换成基数层 | 只有 ℕ-下标, 见 (g) |
| `OrderEmb` 路径 | 固定范数走路 | LP §2 | 推断 | 分支搜索变成一条确定的路 | 需要单调与良基; 路径长度无界, 不是判决算法 |

**一概不给的.** `GV` 的 `pen`/`rise` 由树判决, 上面全在项上. `InaccStrike` 第一个障碍 (奇异 Ω 下标, 在 `limᴼ k g` 目标上判 `j ≺ g x`) 没有任何对应物: Lean 比较项不比较树.

### (d) 记号无关闭包定理, 深度 $\ge1$

对照对象: `Good` (`UniformPendingGoodClass.lagda.md:174`), `Step` (`UniformPendingGoodTower.lagda.md:132`), 阻塞记在 `Tower:361`. 下面的对应全是推断, 没有哪个仓库这样说. 这些**都不直接解决** `Obs` 缺 `fo1`.

| 想法 | 位置 | 层级 | 省什么 | 不给什么 |
|---|---|---|---|---|
| $W^*=\{x\mid\forall u.\ D_ux\in W_u\}$, $A_\omega(W^*)\subseteq W^*$; 任意 A-封闭 $X$ 上 $X^{(a)}$ 仍封闭; 对**项长度**归纳吸收阶段 | `pss` `W4` Lemma 2.4–2.8, `W3:62,115,121,163`; `S8:7593-7649` | 机检·只读 (陈述); 数学是 Buchholz 1987, 同行评审 | 现在 `Tower` 对 $k$ 递归、闭包对具体 `Good` 做; 它对任意封闭类证, 且闭包**不用标准形** | 只到 $D_\omega$-free, 即 $\psi_0(\Omega_\omega)$, `Tower` 已超过; 超限版无先例; Lean 证明体的经典性未查 |
| 全称进类, 只要求原始目标标准: `S<n ⟹ W<n ⟹ D<n ⟹ Sn` | `bt` `P/Spine.lean:2011` `SStrict`, 2017, 2032, 2099; `paper/paper.txt:1171-1216` | 机检·只读 | 可能收窄 `¬BranchΩ` 否定的那个过强陈述; 归纳量是目标高度的有限大小 | 其语法类 $L$ 可判定, 我们的不可判定; "原始出现" 若只能用记号说就破约束 |
| 按项固定的行域 | `hz` `O/OrdinalFormal/Omega3RowPool.lean:43` `Pool`, 51 `fs_mem`; `O/OmegaLRD3Final.lean:49,79,102`; `proofs/paper/well-ordering.zh-CN.md:460-498` | 机检·只读 | 不找全局类, 只对 FS 封闭不对 + 封闭; 正是 "折叠输出回灌下标" 的同形物 | $\rho_G$ 把行码压进序数, 不能照搬; 只帮 `Label` 路线的 `G` |
| 深度归纳带秩见证 | 同上 §8.3 | 人工证明(社区) (纸面) + 机检·只读 | 归纳命题是 "存在 $\mu_G$", 不是 "无无穷链"; 与 `forceᴺ`/`lvG` 读输出同需求 | |
| 储备重新获得, 不写逐阶段 | `ph` `RI/Representation.lean:401` `blockScheme_bounded_representations`, 372 `BlockScheme`, 301 `FiniteReflection`; `RI/ExpansionWellFounded.lean:133` | 机检·只读 | 独立旁证 "阶段步不从上一阶段的对角取数据"; 组合层 **6 个假设不含全序** | 反射本身对树不成立, 不要试 |
| 中间态可暂破不变量 | `bt` 论文 Capping lemma, Barrier lemma (`paper.txt` §2–§3) | 人工证明(社区) + 机检·只读 | 闭包中间步不必保持完整类 | 规模: `P/U2.lean` 37080 行, 闭包在 22733, 共尾在 37068 |

**避开逐阶段论证只有四招** (WO §3.2): 全称进类 (已用); 一个归纳加抽象接口; 粗到吞掉结构的均匀对象 (要 ω₁ 正则, 树侧无); **对项长度归纳 (我们还没做)**.

### (e) 层号与宇宙设计; 比较层号

**先看结论: 被查的代码里没有一处有 "目标低于节点层、按层号分派的总折叠", 也没有 `<ᴵ-dec` 式有界三歧的对应物** [推断, 依据是读到的代码, 不是穷举].

| 做法 | 位置 | 层级 | 省什么 | 不给什么 |
|---|---|---|---|---|
| 证据写进码, 从不比较 | `kv` `IRUniverse.agda:18-26` `LvlStruct`, 42-47 `Uⁱʳ`, 101-113 `Lift` | 机检·只读 | 术语与最小接口 (15 行). `Lift` 对应 `ψ↓`, 经验已用尽 | `wf`/`<-prop` 外给, `Lv` 不满足 (`¬WF-L₁`). 代价 funext + UIP (`Lib.agda:31-32, 48-49`), 无 `--safe`. 不能实例化到 `Lv` |
| 全局三歧作假设 | `kv` `IRUniverse.agda:244` `cmp` (记录 `Ordinal`) | 机检·只读 | 对照 | 是假设, 且只用于可选的 `Π''` |
| 非递归提升 | `kv` `Super.agda:132, 148-149` `OU` | 机检·只读 | `up` 构造子路线的最近先例; 术语 "recursive sub-universe" (`paper.tex:643-647`) | 下标是裸 `O`, 无 `limᴼ` |
| 沿全部路径一次取齐 | `cz` `TypeHierarchy.agda:19-42` `ϕ`; `𝕍⊆Acc` 31-36 | 机检·只读 | 对应 `Pre`/`at`/`Low` | 没有比现状更短的写法; 他要 `Acc`, 我们结构递归, 更省 |
| 递归定义的值序 | `coquand/agda-mahlo-universe` @ `199a725` `MAHLO/FixCounter.agda:82-122` | 机检·只读 | `VLab` 要跨 `Ordᴸ k` 比较时的短写法; 不用分支互搬 | 是值序, 值路线已判不省代价; 不解决判决 |
| 比较在语法上 | `cq` `BH.agda:199` 起 `lt`, 234 字典序析取; `BHOrd.agda:517,568,795` | 机检·只读 | 独立旁证 "裸项 + 事后标准形" | 我方 `cmpᵀ` 已如此, 动因大半不存在 |
| 记号作层号 | `Lvl = NF` | 推断 | `GV` 按定义成立 | **违反树独立于记号的约束**, 见 §4 第 8 项 |

### (f) 无 `Funext` 的树相等

| 做法 | 位置 | 层级 | 省什么 | 不给什么 |
|---|---|---|---|---|
| 极限处不用 `≡`, 用归纳的逐点关系 | `cq` `Inf/Ord.agda:12-14` (原则), 28-33 `leq` | 机检·只读 | `Commute` 的 `≈S` 方案的依据 (§4 第 6 项); `fe` 只出现在 `InaccStrikeBase:113` 起的 `Ext` 块与 `InaccStrikeCommute:151,154,227,247` | 只是干净化, 不解决判决; `InaccModulusRank:36` 也带 `fe` |
| 递归定义的外延相等 | `cz` `CZFBasics.agda:51-53` `≐`, 86-97 | 机检·只读 | 反演是 `refl` | 跨层时 `Ordᴸ k` 不在同一个 W 里; 不比 `o≅` 省 |
| cubical 路径 | `BedrockInstitute/QIITOrd` @ `7def431` | 机检·只读 | 只知道 `funExt` 能计算 | **不走**: 全部模块要改 `--cubical`; QIIT 见 §3 |
| 走外部消去子跳出 SCC | `QIITOrd` `docs/termination.md` §3.1–3.2 | 文档, 代码本体未读 | 可能帮 `with` 爆炸 [推断, 猜想] | 帮不了 `ψ` 的类型 |

### (g) 记号无关的良基路线 (与 τ 并列)

| 路线 | 位置 | 层级 | 依赖 | 给什么 | 不给什么 |
|---|---|---|---|---|---|
| τ 到 OT_I | 手册 §6.1; `archive/src/Mahlo/Inacc/Theorem.lagda.md` | 机检·我方 + 测试 | 构造性 | 覆盖 EBO | 义务 2–5 未做 |
| **$W_u$ distinguished sets** | `pss` `SY` `main.lean:235` `OT_B_wellFounded`, `cofinality.lean:1438` `y4_bachmann`; `W3`, `W4` | 机检·只读 | 只用 Lean `Acc` 与句法; 不用序数值 | 良基本身约 2000 行 + 1361 行 (文本计数); 分支是基本列, 形状同树 | **ℕ 下标, 只到 $\psi_0(\Omega_\omega)$**. EBO 下标是项, 对 `Acc u` 递归的版本无人写过; 39 处 `by_contra`/`by_cases`/`Classical` 未核 |
| 五项分解 | `bt` `P/Spine.lean:2099` `FinalHyps`, 2117 `abstract_wellOrder` | 机检·只读 | `closure`、`cofinal` 句法; `seed`、`descent` 用序数 + ZFC + ∀n 弱 n-Mahlo | 接口形状; "共尾是连接件" | 强度全在 `seed`/`descent`, 构造性无替代 |
| 秩/组合层 | `ph`, `koteitan/1y-wo-por` @ `d555ade` `Por/Reflection.lean:88`, `hz` | 机检·只读 | 全部经典序数 + 反射或 ω₁ | 接口纪律 | **不要试**: 真实序数、反射、Σ₁ 初等性 |
| ε₀ 片段的 `Acc` | `xu` `TransfiniteInduction.lagda:113-150` `fstAcc`/`sndAcc` | 机检·只读 | `--cubical --safe` | 约 30 行, `FGH-c1` 类小片段可照写 | 延伸不到 ψ: $E(a)<\psi(b)$ 的下降不是子项 [推断] |
| 路径刻画 $<$ | `hy` `Epsilon0/Paths.v:884` `LT_acc_from`, 919; `Canon.v:823` | 机检·只读 | Coq | 双向形式, `desc-lab`/`occ<` 的通用形状 | 只到 ε₀ |

**接口结论.** $B<A\Rightarrow\exists k.\ B\le A[k]$ 是全部良序证明的连接件: `bt` `P/U2.lean:37068`, `pss` `S8:10501`, `SY` `y4_bachmann` 都是它 [推断, 比较是我方做的]. 无序数的归纳只有两处: BTBMS 的 `closure`/`cofinal` 与 $W_u$.

### (h) API 与基本列设计

| 模式 | 位置 | 层级 | 抄什么 | 备注 |
|---|---|---|---|---|
| 基本列返回分类, 规格单独写 | Mathlib `SetTheory/Ordinal/Notation.lean:925`, 967, 989 (主分支, **未钉**) | 机检·只读 | 全部原始项上定义; NF 保持是**条件式** | 可把 `cof`/`fsn` 规格收成 `FSProp` |
| 信息性共尾 | `hy` `Epsilon0/Canon.v:823` `canon_limit_strong` | 机检·只读 | Σ 算出下标 | 对 `--safe` 直接适用, 优于 Prop 版 |
| 通用记录 + 认证分类器 | `sw` `Generic/OrdinalNotationSystem.lean:29`, `Generic/Classifier.lean:20` | 机检·只读 | `limit` 支三件事 | 用 `eval` 进 `Ordinal`, 要换成树 |
| 免带分支等式 | `sw` `Generic/LimitSequence.lean:24` `LimitSequenceData` | 机检·只读 | 已知极限后直接拿列 | 治 `with` 爆炸 [推断] |
| 映射与基本列交换 | `gl` `Googology/Core/Morphism.lean:27,65,106`; `Trans/BMS/ExBuchholz/Commute.lean:514` | 机检·只读 | `StepHom` 的 reindex 形状, `Lab` 的同形物 | 只有 `dom` 三种, 规则 6 永不触发 |
| 句法保序翻译 | `gl` `Trans/BMS/ExBuchholz/PSS/Terms.lean` `toTerm`, `lessBT_iff_lt` | 机检·只读 | τ 义务 2 的模板 | 证明体未读 |
| 验收陈述 | `gl` `Googology/Cofinal.lean` `Eval.Cofinal.rank_eq` | 机检·只读 | "秩 = 值" 的干净写法 | 语义, 不能搬 |
| 比较器与求值分开 | `sw` `docs/gamma0-design.md` | 文档 | raw/canonical/semantic 三层 | 已是我们的做法 |
| 记下下标约定 | `hy` `canonS`; 手册 §3 速记 | | | PSS 的基本列比较有偏移且分情形 |

## 2. 项目卡片

"可抄" 的详细边界在 §5. 计数口径写在卡内; 除 `ExBuchholz` 外都没跑过 `#print axioms`.

**koteitan/googology-lean** `6da2de5` (2026-11-02). Lean 4.30.0 + mathlib.
- 证明: `E/` EBO 的封闭、递减、共尾、良基、同构 (手册 §5.2, 语义部分经典); `P/` ω 个弱不可达的 ψ, φ 原语, NF 良序且完备, 假设结构 `InaccSeq`; `Trans/` 翻译.
- 状态: `E/`、`P/`、`Trans/{ExBuchholz,BMS/ExBuchholz,DBMS/ExBuchholz}` 0 axiom. 全库 axiom 全在 PoR 一侧 (`Trans/BMS/PoR/PSS`, `Trans/PoR/InaccPsi/R2`) 与一处注释: 去注释 27 文件 156 个, 不去注释行首 31 文件 160 行. `E/` 公理已机检, 其余文本计数.
- 许可 MIT (`Copyright (c) 2026 koteitan`); `NOTICE` 列的目录 Apache-2.0. 可抄, 须保留声明.
- **判断: EBO 段的主要蓝本. I 层没有基本列.**

**koteitan/pss-proof** `d1be91f` (2026-09-06). Isabelle/HOL + Lean 4.
- 证明: PSS 停机 `y5_PSS_wf` (`S8:13087`), Lean `p_8_7_termination`; Buchholz 1986 Lemma 2.1–3.3 自证; **无语义的 `OT_B_wellFounded`** (`SY` `main.lean:235`); `bijectivity/` 序同构, 满射引 [Buc2] Thm 1.4(a) (README 称).
- 状态: 见 §3 "131/5". Isabelle 独占一行的 `sorry` 8 处, 3 处在 `pss_paper.thy`; 审计按名字, 不是按证明项 (`S8:12651`). `lean/` 所列目录 axiom 0.
- 无 LICENSE. 不可抄, 只取数学 (Buchholz 1986/1987 本身是论文).
- **判断: $W_u$ 与 Bachmann 共尾最值得读. 交换律 20 万行 (Isabelle) 不要搬.**

**koteitan/bms-rathjen** `7bde9d7` (2026-08-22). Lean 4, 无依赖.
- 证明: 只有 Rathjen 1991 $\mathfrak T(M)$ 的项、序、标准形定义; `fsT`/`fsN` 是作者设计. M 处递减、封闭未证.
- 状态: 1 sorry (`scripts/axioms_of.lean` 自测), 0 axiom (文本). 只有 12 行 `#guard` 对博客表, Γ₀ 量级.
- CC BY-SA 3.0. 不可并入本仓库.
- **判断: 工程先例. 一元 χ 写不出 $\Omega_2$, 不能作 EBO 的超集; $\psi_{ZM}(0)[n]$ 是常量.**

**Naruyoko/googology** `958ac91` (2026-10-01). JavaScript.
- 证明: 无. `impl` 1944 行, *Rathjen-type* 的实现; `kanrokotiInaccessiblePsi` 是 EBO 上加 I.
- 许可: 根无 LICENSE; `implementation.html:47`、`kanrokoti…/implementation.html:36` 声明 CC BY-SA 3.0. 不可并入.
- **判断: 只作序的外部对照. 序依赖 `inOT`、造大项, 最不适合 Agda. Kanrokoti 无 $\psi_I$, 标准形靠搜索, 不是 `EBOI` 的前身.**

**DavidExmachina/garden-of-ordinals** `618e814` (2026-10-23). JavaScript, 公开.
- 证明: 无. `ord:858-1388` `RathjenM` 是最短的二元 χ 实现; 还有 `RathjenK`, `Stegert1/2`; `ASSETS/DATA/SHEET` 表 5000 行, 无展开.
- 无 LICENSE, 无版权声明. 不可抄, 数据也不可用, 要先问作者.
- **判断: 规则形状的第二意见; `isnormal` 把不动点推给序值得借鉴.**

**EgoFakeFantasy/BMS-Well-Ordering-Lean** `3a4a945` (2026-10-28). Lean + mathlib.
- 证明: `bm4_strictWellOrder_l` (`ConstructibleBridge/BMSConstructibleBridge/FinalAssembly.lean:63`), ZFC 级, 载体是种子生成的 BM4 数组; `derives_m H` 是 Z₂ 内逐外部高度 H 的推导, 不含可比性, 不是 Z₂ 内对 H 全称.
- 状态: sorry 4 处 (全在注释), axiom 0 (文本); 公理足迹 README 称三公理.
- Apache-2.0 (`NOTICE` 须保留). 可抄, 但无用.
- **判断: 标签是稳定序数, 用不上. 只记 "粗到吞掉结构的均匀对象" 这一招.**

**Phyrion1343/1Y-Well-Ordering-Lean** `03d794f` (2026-09). Lean + mathlib.
- 证明: 1-Y 上 `expansion_wellFounded` 等 4 条, 不限生成集 (`formalization/Concrete/OneYTruth/ActualWellOrdering.lean:15-31`); 0-Y 与可逆 BMS 序同构 (README 称). 假设无参数, 经典, 纸面 ZFC.
- 状态: sorry 0, axiom 0 (文本, 排除 `vendor/`, 444 文件).
- Apache-2.0; `vendor/` 另算 (§5).
- **判断: 组合层/语义层切分最干净, `RI/Representation.lean` 只依赖 `Std`. 形状可看, 反射不可用.**

**koteitan/1y-wo-por** `d555ade` (2026-09). Lean + mathlib.
- 证明: 同上四条, 只换语义层为 PoR 式 Σ₁ 初等; 强度全在 `initial_all` 的 ω₁ 正则与选择.
- 状态: 180 文件, sorry 0, axiom 0 (文本). Apache-2.0 + `NOTICE`.
- **判断: 两层接口的外部验证, 仅此而已.**

**zball-bz/btbms-formalization** `4f31c78` (2026-10-28). Lean + mathlib.
- 证明: `MainTheorem := (∀ n, ∃ κ, IsWeaklyMahlo n κ) → IsWellOrder Std Std.lt`. `closure`、`cofinal` 句法, `seed`、`descent` 语义. 形式化替换了论文 §5 的 J-层级, 所以没验证那一节.
- 状态: sorry 9 处全在蓝图注释, axiom 0 (文本); 73050 行.
- 无 LICENSE. 不可抄, 只取想法.
- **判断: 调查中与我们最接近; 闭包的规模警告 (约 2.3 万行, 按文件位置粗估).**

**hzyhhzy/column-ordinal-notations-hzy** `2da3765` (2026-10-22). Lean + 纸面.
- 证明: 七个列式记号良序, 如 `standard_with_top_strictWellOrder` (`lean/RPD/src/FiniteDemandRPDFinal.lean:44`), `standard_accessible` (`O/OmegaLRD3Final.lean:102`). 普通经典 Lean; KPω 强度下调只是纸面.
- 状态: 337 文件, sorry 0, axiom 0 (文本).
- 根无 LICENSE (`lean/licenses/1Y-Apache-2.0.txt` 只针对上游 1Y). 不可抄, 只取想法.
- **判断: `Pool` 与带数据的深度归纳值得试; 其它不用.**

**AndrasKovacs/universes** `08e56f2` (2026-09-05). Agda 2.6.1. CSL 2022 补充.
- 证明: 给定 `LvlStruct` 的 IR 宇宙层次; `Super` 的超宇宙. 无 `--safe`, postulate `ext`, 用 UIP.
- 无 LICENSE. 只借思路.
- **判断: 方向相反 (层号先有). 只留术语与最小接口.**

**coquand/agda-ordinal-analysis-id1** `1f977e0` (2026-11-02, 还在推). Agda 2.8.0.
- 证明: θ(ε_{Ω+1}) 记号与全部序律 (裸项), 树上二元 Veblen, ID₁ 分析. **WF 作前提** (`Inf/BHSound.agda:64-69`); **无基本列**; Γ₀ 在所读模块未定义 (只看了签名).
- 状态: README 称 83 模块 `--safe --without-K`, 无 postulate; grep 相符.
- 无 LICENSE. 只借思路.
- **判断: `VebT.agda:6-9` 是壁垒定理的独立旁证, `Inf/Sum.agda:3-21` 是 cumsum 的历史出处. 代码省不了什么.**

**takahashi-yt/czf-in-mahlo** `b8aa846` (2025-08-19). Agda.
- 证明: CZF + 超限不可达集解释进 MLTT + Mahlo 宇宙 + Acc; `𝕍⊆Acc` 是定理. 选项 `--cubical-compatible`, 部分 `--safe`; 3 文件有 postulate (`Extensional:18`, `Inaccessibles/Basics:218,232`, `RegularExtensionAxiom:259`).
- MIT. 可抄, 须保留声明.
- **判断: 可抄但没有更短的写法.**

**cj-xu/OrdinalNotations** `4690b68` (2021-02-21). Cubical Agda.
- 证明: ε₀ 三种表示, 泛等互转, 超限归纳; `--cubical --safe`, grep 无 postulate.
- GPL-3.0. 不可并入, 只借思路.
- **判断: 两招: ε₀ 片段 `Acc`; 函数的图代替递归函数 (`MutualOrdWithoutNestednessAndRecursion.lagda:6-14`).**

**coq-community/hydra-battles** `ed8e604` (2025-01-22). Coq.
- 证明: ε₀ 完整, 带基本列. `Gamma0/` 经 RPO 良基, 无基本列, grep `Admitted` 0; README.md:145 标 **draft**.
- MIT. **判断: Σ 共尾、路径刻画值得照写.**

**SteveWmoc/lean-ordinal-analysis** `0aa3551` (2026-10-31). Lean 4.
- 证明: ε₀ 与 Γ₀ 段, 通用 API, 基本列共尾. 全部 `.lean` 6483 行, sorry 0, axiom 0 (文本). MIT. Veblen 基本列细节未读.
- **判断: API 形状可看.**

**Mathlib** `SetTheory/Ordinal/Notation.lean` (主分支, 未钉; 文件头 Apache-2.0). ε₀ `ONote`. **判断: 规格写法可看.**

**没用, 不用重读:**

| 仓库 | 提交 | 许可 | 内容 | 判断 |
|---|---|---|---|---|
| AndrasKovacs/ir-metatheory | `7cb256b` | 无 | Mahlo 算子作模块参数; IIR 规范性 | 没用 |
| coquand/agda-mahlo-universe | `199a725` | 无 | Mahlo 语法元理论, 不动点作假设 | 只有 `FixCounter:82-122` 一段, 见 (e) |
| BedrockInstitute/QIITOrd | `7def431` | AGPL-3.0-only | Brouwer 树 QIIT | 只有 `docs/termination.md` 的方法, 见 (f) |
| hyperpolymath/echo-types | `b0982c4` | MPL-2.0 / 文档 CC-BY-SA-4.0 | 24 行 Buchholz 语法骨架 | 没用 |
| hyperpolymath/ordinal-notation | `deb0131` | MPL-2.0 | `<ᵇ` 的 WF 对**粗关系**成立, 不是序数序; 序型 postulate (`Fidelity.agda:183,211`) | 不解决层 3; `*Refuted` 模块可作反例目录 (未读) |
| AzertyWasTaken/Ordinals | `a921bf9` | MIT | JS 展开脚本 | 没用 |
| hypcos/notation-explorer | `30c43bd` | 无 | Taranovsky、BMS 类; 无 M 规则 | 没用 |
| vihdzp/ordinal-notation | `46a81b1` | 无 | Lean 到 Buchholz, 已归档 | 没用 |
| koteitan/bms-paper-formalization | `4a83c05` | MIT | Isabelle BMS, 无 ψ 规则 | 没用 |

## 3. 已否定或不要再查

| 问题 | 结论 | 依据 | 层级 |
|---|---|---|---|
| 字面的 $s<t[n{+}1]\Rightarrow s\le t[n]$? | **假.** $t=\psi_0(\omega)$, $t[n]=\omega^n$, $s=\omega^n+1$. 只有带范数或带 `G` 的形式成立 | LP §2, 手算 | 推断 (反例可手验) |
| (B2) 字面 $\alpha[n]<\beta<\alpha\Rightarrow\alpha[n]\le\beta[0]$ 在 EBO 编号下? | **假**: $\alpha=\psi_0(\omega)$, $\beta=\psi_0(n{+}1)$, $\beta[0]=0$. 改 $\beta[1]$ 能否救未判定, `InaccModulus*` 把它当前提 `bach` | LP §5, 手算; BCW 原文未对 | 推断 |
| QIIT 能作树或层号? | **不能.** `l≡l` 使 FGH 无从定义; 层号的类型族进 `hSet` 过不了 `isSetOrd`; `≤` 仍不可判定; 工具链要全改 `--cubical`. 只有 `docs/termination.md` 的方法可用 | TT §E | 推断 |
| Kovács 有比较或折叠? | **没有.** 全程消费证据, 只上行 `Lift`; 无 "把高层压到低层". `cmp` 是假设 | `kv` `IRUniverse.agda:101-113, 244` | 机检·只读 |
| 宇宙文献能给判决 `D`? | 读到的范围内没有, 也没人碰到同样问题 | TT 总结 | 推断, 非穷举 |
| 这些仓库有 I 层基本列? | **带证明或 Lean 形式的: 没有.** `InaccPsi` 无 `dom`/`fs`/`cof`; `Trans/PoR/InaccPsi` 只消费值. I 层展开只在 JS 实现 (Kanrokoti、Naruyoko、Exmachina), 无证明; 人工证明仍只有 みずどら (手册 §6.2) | LP §3.2, §6; ML §1–§4 | 机检·只读 / 社区无证明 |
| 有实现折叠树的仓库? ψ 记号的基本列? | 树折叠: 所读的仓库都没有. ψ 记号基本列: 只有 `ExBuchholz`、`br` 的 `fsN`、JS 实现 | TT 总结 | 推断, 非穷举 |
| BMS 类的良序证明无序数? | **只有定义无序数.** 除 PSS 外都给列贴真实序数标签, 加反射或大基数. 无序数的归纳只有 BTBMS 的 `closure`/`cofinal` 与 $W_u$ | WO §2 | 机检·只读 + 推断 |
| 对这些系统到 ψ 的序数值有定理? | 只到 PSS (两行). BMS、Y、BTBMS 都没有; `omegaIndexMatrix` 是校准表, 不是定理 | WO §4 | 机检·只读 |
| pss-proof 的 131 与 5? | **两个都对, 说的不是一回事.** 131 是 `isabelle/8/audit.thy:41-42` 的历史清单 (已核: 131 项), 那些陈述已搬进 `5/ 6/ 7/ 8/` 单命题文件; README:30 是迁移前的过时说法. 5 = `pss_paper.thy` 里 3 条真 `sorry` (233, 239, 250, 全是 [Buc1] 引用) + 2 处注释 (14, 222). 全 `isabelle/` 独占一行的 `sorry` 8 处. 正则不抓 `by sorry`; 审计按名字 | WO §1.5 | 机检·只读, 文本计数 |
| 有 M 层的 "期望展开" 语料? | **没有.** 只有序的表 (`nr` 158 项, `ex` SHEET), 展开只到 Ω 量级 (`br` 12 行). 要用就自产 | ML §8 | 机检·只读 |
| M 层有证明? | 无封闭、无递减、无良基、无值语义 | ML §7 | 推断, 基于所读 |
| "$\psi$ 参数都 $<M$"? | 只对 Maksudov 与 $\mathfrak T(M)$. Exmachina (`ord:980-985`, `:1290`) 与 Naruyoko (`impl:1455-1458`) 允许 $\mathrm{cof}=M$ 落在 ψ 参数上. 我们建议切掉; 切掉是否丢强度未知 | ML §3, §5.1 | 社区无证明 + 推断 |
| 序、标准形要与基本列同时算? | **不要.** 单向: $r^\ominus$ 只对后继取 $b[0]$, 即 `pred`. 注意 Naruyoko 的序与 `inOT` 互相依赖, 但两者都不碰一般基本列 | ML §6 | 社区无证明 + 手算 |
| PSS 的基本列与 ψ 逐项对应? | **不.** 下标有偏移且分情形; 一步可对应无界多步 (`gl` `Trans/BMS/ExBuchholz/PSS/StepBound.lean:492`, 陈述已读). 只有可达性保持且反映. 所以别拿它当 `Lab` 的先例 | LP §4.2, WO §4 | 机检·只读 |
| `Trans/PoR/InaccPsi/R2` (1975 文件) 有用? | 无用: Wilken 的 $R_2^+$ 主张, 两半都开放, 带前提 FRAG, 28+ 条 axiom | LP §4.1 | 文档 |
| hydra `Gamma0` 的 "draft"? | **有, 不在 `.v` 里.** `README.md:145` 与 `meta.yml` 标 draft; `Gamma0/*.v` 无此字样, 无基本列, `Admitted` 0 | 本次抽查 | 机检·只读 |
| Exmachina 的源码? | **公开**, 见 §2. 无许可 | ML §3 | |
| Dybjer–Setzer 仓库? | 匿名取不到 (GitLab 要凭证, API 404). 是否问作者由人定; 预计与层号比较无关 [推断] | TT §I | 未读 |

**不要试** (WO §7, TT §E): 列贴稳定序数; 反射/Σ₁ 初等性; Z₂ 逐实例内部化; 把 PSS 交换律搬到高阶段; 把 QIIT 作树; 把 `Lv` 实例化成 `LvlStruct`.

## 4. 待试清单

排序是我方判断 [推断], 综合 "一次能否判定" 与 "判定后改变什么". "约束" 指树独立于记号: 树的定义不读记号, 记号只在验收节.

| # | 想法 | 来源 | 最便宜的检验 | 试过? | 约束 |
|---|---|---|---|---|---|
| 1 | **线性模** $n\le\mathrm{size}\,Y+1$, 与 $t$ 无关. **推断, 未测试前不算事实** | LP §1.1 逐支读 `gl` `E/Cofinal.lean:294-395`; 紧性手算 | `probes/Survey/scripts/ebo_vs_exbuchholz.py` 的转写上枚举 $(X,Y)$ 对; 或给 `Cof6` 的 `Σ ℕ` 加上界 | **未测**. 我方树侧 `InaccModulusBase` `mod` 有同形陈述 (模读 `wk j`), 但那是另一件事 | 合规: 只在验收节 |
| 2 | **`PL`/`PR` 是不是 "原始出现"?** 收窄 `BranchΩ` 的量词 | `bt` `P/Spine.lean:2011`, `paper.txt:1178`; 我方 `Relative.lagda.md:74-76` | 纸面判定, 不写 Agda: `PL`/`PR` 是否会被 `Pk`/闭包实际产生 | 未试 | **待判**: "原始" 若只能用记号表述就违反 |
| 3 | **$W^*$ 闭包, 参数化到任意 A-封闭类**, 对前缀语法长度归纳 (Buchholz 1987) | `pss` `W4`, `W3:62,115,121,163` | `--safe --without-K` 玩具: ℕ-下标 Buchholz 项, 内层 `data A u X` + 对 `u` 递归, 证 2.4–2.7, 判据是能否不用 funext 与 LEM (200–1400 行, WO 估计). 然后看 `Step.V` 用了 `Good` 的哪些具体性 | 未试 | 合规 (对类量词). 玩具本身带记号, 只作形状验证 |
| 4 | **按项 `Pool` 代替全局 `G`**, 针对 `T₂-cert→⊥` | `hz` `O/OrdinalFormal/Omega3RowPool.lean:43` | 在 `InaccStrikeOracle` 上定义 `Pool t`, 看 `Pool(ψ₀(Ω_Ω·2))` 是否含 `ω⁺T`; 不含则否定不适用. 再对 `ver-dev` 的项检验 | 未试 | 合规, 若只作 `GV` 的前提类; 不解决证书路线 |
| 5 | **EBO 上的 $W_u$**: 对 `Acc u` 递归定义, 同时归纳证下标 Acc | LP §5.1 | 先做 3; 再纸面查循环 | 未试, 无人写过 | 记号侧, 不涉树 |
| 6 | **归纳逐点关系 `≈S` 去 `Funext`** | `cq` `Inf/Ord.agda:12-14`; `InaccStrikeCommute:151,154,227,247,268` | `data _≈S_` 四构造子, `limᵢ` 保留 `subst Ordᴸ e`, 改写 `Commute` 一次编译. 收益 `nat-label` 无条件; 规模约等于 `Ext` 块 | 未试 (`≈S` 在 probes 无命中) | 合规. 只是干净化 |
| 7 | **函数的图代替 `Run`**, 救 `Gen`/`Run` 不严格正 | `xu` `MutualOrdWithoutNestednessAndRecursion.lagda:6-14` | 一次编译. 只有 `Run` 在 `Gen` 构造子里严格正时才行, 那份试验未保留 (`InaccStrike` 事实 6). 现行 `Gs` 已绕开, 价值只是去掉对 $n$ 分层 | 未试 | 合规 |
| 8 | **Lean `exfalso` 结果 ⟹ `OTFS_thm` 可移植** | 手册 §5.2 | **已做**: `Closure:1027,1645` 改成 `exfalso; omega` 后 `OTFS_thm`、`Trian_fs_thm` 只剩 `propext, Quot.sound` (机检·已构建). 它说明无经典障碍, **不说明 Agda 写得出** | 已试 Lean 半边; Agda 未试. `propext`、`Quot.sound` 可去仍是推断 | 记号侧, 合规 |
| 9 | 无 M 的 χ 片段 (φ-free) | ML §7 | 先在 `mnot.py` 换 KawamoYurase 序, 跑现有测试 | 未做 | 记号侧, 合规 |
| 10 | 把闭包写成对 `lt`、`D`、`R` 多态的记录 | `ph` `RI/Representation.lean:301,372,401` | 写接口, 看 `Step` 能否脱离 `Good` | 未试 | 合规; 不解决数学 |
| 11 | 共尾改 Σ; `FSProp` 收规格 | `hy` `Epsilon0/Canon.v:823`; Mathlib `Notation.lean:967` | 局部改写一处 | 部分已是 Σ (`Prem.cofi`) | 合规 |
| ✗ | **Kovács `LvlStruct`, `Lvl = NF`, `i<j = cmpᵀ i j ≡ lt`** | `kv` `IRUniverse.agda:18-26` | 不试, 除非改约束 | 未试 | **违反**: `limᴼ` 的分支只能走项, 树成了记号的展开. 另 `wf` 就是记号侧层 3. 这是设计分岔, 要作者判断 |

**只在 "只证强度下界" 时才有意义**: 用 `y3_cofimg` 式的可达性 + 共尾代替 `Lab` 的逐项一致 (WO §4). 不给 FGH 精确性.

## 5. 许可证与复制边界

**这不是法律意见. 是否复制、如何署名, 由用户决定.** 下面的判断只是读许可证文本得到的 [推断].

**本仓库.** 根 `LICENSE` 第 1 行与 `README.md:28-30` 都是 **CC BY-NC-SA 4.0**. ML §8 说的对. 全仓库一个许可, 不分代码与文档, 没有例外条款.

**分类.** *只读*: 无授权, 可看, 可用其中的数学, 不抄文本、数据, 也不做贴合的逐行翻译. *只取思路*: 有许可但与本仓库不相容 (SA 或 GPL 系不容许加 NC). *可抄带署名*: 宽松许可, 保留声明后可用.

| 仓库 | 许可 (依据) | 边界 | 备注 |
|---|---|---|---|
| googology-lean `E/`, `P/`, `Trans/` 的 ExBuchholz 部分 | MIT (`LICENSE`) | 可抄带署名 | `Copyright (c) 2026 koteitan` |
| googology-lean `Y/WellOrder/{ZeroY,OneY,Por}`, `OmegaY/WellOrder` 等 | Apache-2.0 (`NOTICE`) | 可抄带署名 | 用不上 |
| pss-proof | 无 LICENSE | 只读 | 数学属 Buchholz 论文 |
| bms-rathjen | CC BY-SA 3.0 (`LICENSE`) | 只取思路 | |
| Naruyoko/googology | 根无; 页面声明 CC BY-SA 3.0 (`padicBotRathjen/implementation.html:47`, `kanrokotiInaccessiblePsi/implementation.html:36`) | 只取思路 | 其它目录未查, 视同只读 |
| garden-of-ordinals | 无 LICENSE, 无声明 | 只读 | 数据同样, 要用先问作者 |
| Fandom 博客表 | CC BY-SA 3.0 (koteitan 如此引, 手册 §9) | 只取思路 | 手工从规则推少量向量 |
| BMS-Well-Ordering-Lean | Apache-2.0 + `NOTICE` | 可抄带署名 | 用不上 |
| 1Y-Well-Ordering-Lean | Apache-2.0; `vendor/` 另算 | 可抄带署名 | 1y-wo-por 的 `NOTICE` 说 vendor 快照无许可 |
| 1y-wo-por | Apache-2.0 + `NOTICE` | 可抄带署名 | |
| btbms-formalization | 无 LICENSE | 只读 | |
| column-ordinal-notations-hzy | 根无 | 只读 | `lean/licenses/` 只针对上游 |
| universes, ir-metatheory | 无 LICENSE | 只读 | |
| agda-ordinal-analysis-id1, agda-mahlo-universe | 无 LICENSE | 只读 | |
| czf-in-mahlo | MIT | 可抄带署名 | |
| QIITOrd | AGPL-3.0-only | 只取思路 | |
| cj-xu/OrdinalNotations | GPL-3.0 | 只取思路 | |
| echo-types, ordinal-notation | MPL-2.0 (文档 CC-BY-SA-4.0) | 只取思路 | 文件级 copyleft; 没有值得拿的 |
| hydra-battles, lean-ordinal-analysis | MIT | 可抄带署名 | |
| Mathlib | Apache-2.0 (文件头, 未钉) | 可抄带署名 | |
| AzertyWasTaken/Ordinals, bms-paper-formalization | MIT | 可抄带署名 | 没用 |
| notation-explorer, vihdzp/ordinal-notation | 无 | 只读 | |
| Dybjer–Setzer | 未知, 未取得 | 不适用 | |

**把 `ExBuchholz` (MIT) 移植进本仓库要什么.** 需用户决定:

1. **范围.** 只限 `E/{Basic,Order,Std,WF,Sum,FS,Closure,Cofinal}`. 不碰 `pss` (Lake 依赖, 无许可), 不碰 mathlib 语义部分. `NOTICE` 的 Apache 例外不含这些目录 (已核).
2. **声明.** MIT 要求版权与许可声明随 "所有副本或实质部分". 文件头写上游路径、提交 `6da2de5`、改动说明, 并收一份 MIT 全文 (仓库现在没有放第三方许可的位置).
3. **与仓库许可的关系.** `README.md:30` 是全仓库一句话, 要加例外说明. 两种写法: (a) 移植文件保持 MIT, 列为例外; (b) 按 MIT 允许的再许可, 整体 BY-NC-SA 但保留 MIT 声明. (a) 更清楚 [推断]. 这是用户的选择.
4. **Lean → Agda 算不算演绎作品?** 不敢断言. 稳妥做法: 贴合的翻译按演绎作品处理, 署名照做; 只用定理陈述和证明思路时, 仍在文件头注明来源.
5. **位置.** 按目录规则先进 `probes/`, 进 `src/` 须用户另行发起任务.

**现状里要用户看一眼的两处.** `probes/Survey/scripts/ebo_vs_exbuchholz.py` 文件头写着是对 Lean `dom/fs` 的转写, 没有 MIT 声明; `mnot.py`、`cmp.py` 转写的社区规则也没有来源许可说明. 是否补声明由用户决定, 本任务没动.

**方向相反的后果.** BY-NC-SA 之下, 别人不能把本仓库的 Agda 并回 MIT 项目, 除非作者另行授权. CC 自己不建议把 CC 许可用于软件 (据记忆, 本次未核). 这些也是用户的决定, 这里只记下.

## 6. 未读与待核

**没读.**

| 对象 | 范围 |
|---|---|
| `gl` | `Closure.lean` 中 `Trian` 情形的证明体; `OTLt_wf`、`Mono`、`Onto` 证明体; `lessBT_iff_lt` 证明体 ((h) 的 "句法保序" 由第一行与文件头推断); `Trio/`; `R2/` 除 `Cited.lean` 头部; `Trans/BMS/PoR` |
| `pss` | `W4`、`SY cofinality` 的证明体 (只有陈述与文档); `Support_8_B`; `lean/8/`; `bijectivity/` 证明 |
| `bt`, `ph`, `hz` | `U2`/`U3`/`U5` 证明体; Phyrion 的 ZFC 论证; hzy 的 ARD/IPD/ARD2; PDF |
| 类型论 | Kovács `TTGUModel`/`TTFLModel`; `ir-metatheory` 规范性; Coquand id1 的 `BHFml`, `Inf/BHCut`, `RA*`; Coquand Mahlo 其余约 195 模块; `QIITOrd` `Order/Code*` 代码本体; `ordinal-notation` `Rank*`; `czf-in-mahlo` `Inaccessibles/*` |
| JS | Naruyoko 的 `IPsi`, `*Experimental`, `weakKPsi`, `strongKPsi`; Exmachina 的 `RathjenK`, `Stegert1/2` 的 `fs` |
| 论文原文 | BCW (B2), Buchholz 1987, Rathjen 1990/1994 (这次都没对); 博客这次没重读, 用手册的转述 |
| 未取得 | Dybjer–Setzer 仓库 |
| 跳过 | 所有 `.claude/`, `CLAUDE.md`, `AGENTS.md`, `GEMINI.md` 等面向代理的文件 |

**单一来源或推断.**

| 声称 | 现状 | 缺什么 |
|---|---|---|
| 线性模 $n\le\mathrm{size}\,Y+1$ | 逐支读证明, 手算紧性 | 测试或 Agda 上界 (§4 第 1 项) |
| $\psi_I(0)$ 在不同系统的值 | ML 说 φ-free 是 $\Lambda$, φ 原语是 $\Phi$ 的 Γ-不动点; LP 说 `InaccPsi` (φ 原语) 与 $\Lambda$ 同值. **我方判断二者不矛盾但 ML 的分界写宽了**: 分水岭应是闭包含不含 $\Phi$ (即 $\varphi^1$), 不是含不含 φ. `InaccPsi` 与 Setzer OT_I 有 φ 无 Φ, 值看来是 $\Lambda$ [推断, F10 只证 Ω-不动点] | 手册记此修正; 无人证明 |
| $W_u$ "可直接搬到 `--safe`" (WO §1.6) | 陈述层面无序数; LP 查到 39 处经典写法未核, 且下标只到 ℕ | 第 3 项的玩具 |
| `W_u` 是 `G` 的现成解, `Pool` 能绕开 `T₂-cert→⊥` | 形状类比 | 第 4 项 |
| `Trian_fs_thm` 是经典 Bachmann 的 `G` 形式 | LP 的读法; `triGBC` 与 `Trian` 同义未逐字对照 | 对 BCW 原文 |
| Maksudov 层 1 两项大小和下降 | 手算逐子句 | 机检; KawamoYurase 版未查 |
| 规则 13–15 三版本互为共尾; φ-free 上限仍达 $T(M)\cap M$ | 只手算几项; 无人证明 | 证明 |
| Exmachina 忠实于 Rathjen 1990 | 论文未对 | 对原文 |
| Naruyoko 的 M 规则忠实于博客 | 只有编号对齐; Γ₀ 种子手算三项 | 对博客 |
| 强度对应表 (WO §6: KPω 等) | 文献常识或仓库自述, 未核 | 原文 |
| `gl` 全库 axiom 数 | 去注释 156/27 与不去注释 160/31 的差额未逐项核. 手册 §5.1 把 `OmegaY/WellOrder/OmegaY/Reflection.lean` 算进声明; 其 `:25` 是块注释里的 "axiom is assumed", 不是声明 | 重跑脚本 |
| 外部仓库的公理足迹 | README 或文本计数 | `#print axioms` |
| YesMetaZFC 的许可 | 1y-wo-por `NOTICE` 说快照无许可; BMS-Well-Ordering-Lean `NOTICE` 说上游后来发布 Apache-2.0, 基线不变 | 与我们无关, 用到再核 |
| 提交日期 | 报告与手册个别差一天 (时区), 提交号一致 | 无需处理 |

**本次抽查** (只读, 2026-11-02). 对照克隆核了 100 处左右 file:line, 跨 `gl`, `pss`, `br`, `bt`, `hz`, `ph`, `cq`, `kv`, `xu`, `hy`, `nr`, `ex`, BM4, 1y-wo-por, Mathlib, 除下面两处都定位正确. 行号: WO 把 `OrdinalClassifier` 记在 `Generic/Classifier.lean:18`, 实际 `ClassificationResult` 在 `:20`, `OrdinalClassifier` 在 `:57`. 说法: WO 说 Γ₀ 的 "draft" 无法印证, 实际在 hydra `README.md:145` (§3). 另外 TT 的 Coquand、cj-xu、ordinal-notation 路径省略了仓库内前缀 (`IDHAT/`, `src/`, `verification/proofs/agda/`).
