# 候选的两个有限测试（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 01:56 至 02:34 |
| 工具调用 / agda 编译 (粗数) | 64 / 21 |
| token (usage 字段，按消息去重) | 输出 213263；新写入缓存的输入 624436；读缓存的输入 13689646；其余输入 110 |
| 写过的仓库文件 | `YiCTBase.lagda.md`, `YiCTCall.lagda.md` |
| 文件前缀 | `YiCT` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 2 件全部退出 0，禁用构造 0，导入闭包干净；cand₂ 的实际路径上那一格槽位与目标在同一个孩子 3 下，对一切来源表走链（cell、org-P₁），只给比较表加 (3,3) 条目就保留（cf-pos，有限测试）；两层 ink 处清空来源表无影响（same），一层 ink 之后有一格不同（clr/anc，有限测试）；执行方判断来源表暂不改成族 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b75/YiCT.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiCT 回报（候选的两个有限测试，Opus 5.5）

#### 1. 判决

**对纲领与目标的意义.** 树、折叠、合法性都没有改。两个新文件都是 `--safe`，导入闭包不含记号（`importclosure.py` 显示 OK）。

对目标来说：
- 两份审核担心的缺陷确实出现在 `cand₂` 的实际折叠路径上，见 (a)。`cand₂` 指 d = 1、目标 h₁ 2 的那个实例。
- 在这条路上，丢掉保留的那一格不在来源表 `Org` 的定义域里，任何表都救不了它。只改比较表证据就能让它保留（有限测试）。所以在这一支上，起决定作用的是比较表（台账 V50、V290），不是 (C) 的来源表。
- `up` 行的底把来源表清空（`org-no`），会丢掉一个保留，但只在主表非空处才丢。经两层 `ink` 的孩子处主表是空的，所以不受影响，见 (b)。
- (c) 的判断：暂不把 `Org` 改成对目标的族。

**各步到哪里.** (a) 完成；(b) 完成；(c) 是判断。没有撞堆墙（无 251）。每次编译 4 到 21 秒，最大驻留 0.4 到 2.0 GB。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| `cand₂` 的折叠是否用到审核那一格的同形格 | `YiCTCall` `E0`–`E10`、`kp-P₁` | 有限测试（具体闭项上的 `refl`；`E3`、`E8` 对变量 z） |
| 那一格对一切证据、一切来源表、孩子 3 里的一切路径都给 `nothing` | `YiCTCall.cell`、`org-P₁` | 编译定理 |
| 只给比较表在孩子 (3,3) 加 `self` 条目，同一探针就保留在目标自己的槽位 q′ | `YiCTCall.cf-pos` | 有限测试 |
| d = 0（`cand₁`）的同形格槽位层号是 zero，由 (A) 的地板保留 | `YiCTCall.d0-cell` | 编译定理 |
| 两层 `ink` 的孩子处，带祖先表与 `org-no` 在每个槽位上相同 | `YiCTBase.same` | 编译定理 |
| 一层 `ink` 之后，两种表在 X₀ 顶槽位上不同 | `YiCTBase.clr`、`anc`、`hx`、`pxᵃ` | 有限测试 |
| (ii) 那个底在 (h₁ 2, `inc 0 u`) 处是否被实际查询 | — | 未追踪 |
| 来源表要不要改成对目标的族 | 本节 (c) | 判断 |

##### (a) 那一格在实际路径上（有限测试）

**调用点.** 从 `brᵍ 1 0` 出发（`cand₂` 的 `Branch` 在 c = 0 的分支），逐步展开到 `E10`：

`kpᶜ (tw 1) O PV P₁ (inc 3 (inc tt self)) OT`，结果是 `nothing`（`kp-P₁`）。

这里 `kpᶜ` 是候选 (C) 的保留判定，`OT` 是主折叠此刻带的来源表。

**这一格的位置.**
- P₁ 在塔第 1 项的孩子 3 里，层号 h₁ 1，低于目标 h₁ 2。
- 目标 h₁ 2 自己有一个槽位 q′，层号与分支类型都和 P₁ 相同（`at-q′`、`br-q′`），并且在目标自己的路径下保留（`own-q′`）。
- 所以这一格没有实现 "低于目标保留"。

**展开经过（`E0`–`E10`）.**
1. X₀ 的孩子 0 是 L₁ = `nd sS (λ _ → tw 1)`。L₁ 上的结点槽位层号是 tw 1，高于目标，走链（`E2`）。
2. 链点进入 tw 1，路径是 `inc 3 (inc tt self)`（`v-form`）。
3. tw 1 的顶结点保留在地板槽位 qf（`kp-top`、`E5`）。
4. 分支 3：最小比较表 `rbᶻ` 在 (3,3) 没有条目（`tb33`），于是走上折回退 `ψˡ`（`E6`）。
5. 在 P₃ 上（层号 h₁ 2，与目标同层）走链。这一处回灌的目标和路径与原折叠逐字相同（`at-P₃`、`posW-P₃`、`E7`）。按 "同层以输出作下标对角"，这里走链是对的。
6. 链点下到 h₁ 2（`E8`、`E9`、`E9′`）。
7. Ωt (h₁ 2) 的结点搬到 P₁，这就是那次调用（`mv-P₁`、`E10`）。

**与输出相连.** `probe-call` 写出 `pr (brΩ (pr t₀) tt 3)` 就是这次调用的输出加上前面的部分和；`hd₃` 显示它的头是 ℕ 极限。

**和简报说法的差别.**
- 实际路径是 `inc three (inc tt self)`，不是 `inc two self`。目标 h₁ 2 在孩子 3 下面，是 h₁ 3 的后继孩子。
- 槽位和目标都在**同一个**孩子 3 下，不是 "材料在一个孩子、目标在另一个孩子"。`kpʳ` 的 `(inj₂ _) (inc _ _) = nothing` 一行不区分这两种情形。
- `AuditDCand` 的原格（目标 h₁ 3，路径 `inc three self`）不在我追踪的这条路上。路上的目标只有 h₁ 2 和回灌目标 tw 1。我只追踪了 c = 0 支里的一条路，其他路没看。

**为什么任何表都救不了.** `kpʳ` 落在 `(inj₂ _) (inc _ _)` 一行。来源表只给 Ω 形状结点的下标槽位记条目，`org-at` 在 P₁ 上走到 `inj₁` 就结束（`org-P₁` 对一切 T 成立）。P₁ 的层号非零，(A) 的地板也不适用。

**对照（`cf-pos`，有限测试）.** 我只换了比较表这一个证据参数，没有改定义：只在孩子 (3,3) 加一个 `self` 条目，其余同最小表。同一次折叠就如实进入孩子 3，同一位置的探针成为保留在 q′ 的 Ω 结点。

**对值的影响.** 没有判定，`Branch` 仍是未判定的前提。

##### (b) `up` 行底参数清空来源表的影响

"带祖先表" 只指：把一次底折叠调用里的 `org-no` 换成该层主折叠此刻带的表。这不是新的折叠。

**(i) 经两层 `ink` 的孩子：相同（编译定理 `same`）.**
- 实例：tw 3 朝 tw 1 经 `ink (ink self)`，进孩子 0 即 tw 2（路径仍是 `ink self`，见 `wₜ-form`），在 tw 2 上再走一次 `ink` 行。
- 祖先表的形状是 `altOrg (org-no) (mapOrg Fₜ (org-no))`（`otₜ-form`）：继承部分来自起点的 `org-no`，新增部分来自 `pvT 3` 在前缀上的 `org-no`。
- 结论：对每个槽位 p、每条路径 w，`kpᶜ … otₜ ≡ kpᶜ … (org-no …)`。
- 另外，(a) 那条路在 tw 1 上的主表也是空表（`OT-empty`），所以在 P₃ 回灌处（目标和路径与主折叠相同）换成带祖先表也不会变。

**(ii) 一层 `ink` 之后：不同（有限测试）.**
- 位置：`outᶜ 1` 第 1 个部分和的第 2 个链点，X₀ 的孩子 0，底的前缀是 Ωt X₀（`link₁`、`link₂`）。
- 不同的那个槽位是 X₀ 的顶槽位 `inj₁ (inj₁ tt)`，层号 h₁ 1，朝 h₁ 2 经 `inc 0 (inc tt (inc 3 (inc tt self)))`：
  - 带 `ot₂` 时保留在 `qᵍ 1`，即 h₁ 2 的槽位 `inj₂ (tt , inj₁ tt)`（`anc`、`hxᵃ`、`pxᵃ`）；
  - 带 `org-no` 时走链（`clr`、`hx`）。
- 主折叠能保留这个结点，也只是靠表里的这一条。
- 这个底在 (h₁ 2, `inc 0 u`) 处是否被实际查询，我没有追踪。

**判断（纸面）.** 在塔一类的对象里，第二次 `ink` 只出现在前缀叶子上（读回部分里的路径都来自 `lift`，全是 `inu`），而前缀上的来源表由 `Org⊕ … (org-no …)` 给成空表。所以清空只在一层 `ink` 之后的读回部分起作用。

##### (c) 判断：候选 (C) 的来源表暂不改成对目标的族

1. **改族管不到 (a) 那一格（编译事实）.** 那一格对一切表都走链（`org-P₁`、`cell`），单目标的表和对目标的族都一样。让它保留的是比较表证据（`cf-pos`）。这一格的两个孩子都是数字（3 与 3），属于 D 路所说的 "数字孩子可判定" 的特例。真实链孩子 a (chain m) 上能不能填表，本路没有测。
2. **族需要一个生成处（判断）.**
   - `dlg` 只能沿经过下标层的路径 v : j ≤ k 为目标 j 生成条目。
   - 底的查询点是 (i, `inc c u`)，带的是孩子侧的路径，没有 i ≤ k。
   - 所以族在非主目标处只能是空表；要在 i 等于主目标时查到它，要么判定层号相等（层号里含 Tr k 的函数，一般不可判定），要么让查询点带上经过下标层的路径。后者要改 `up` 行和 Ω 行的回灌，属于定义改动，按简报我停在判断。
3. **(ii) 丢的信息与路径无关（判断）.** 丢掉的是 "X₀ 顶结点的下标槽位来自 h₁ 2 的 qᵍ 1"，这是层号 X₀ 相对于 a₁ 3 的下标层 h₁ 2 的事实，和走哪条路径无关；现行设计只把它沿主目标的路径放进 `ot`。一个可能的方向是让这类信息随层号证据 `Pv` 走，但查询时同样要认出目标就是 h₁ 2，与第 2 条是同一个障碍。建议记进台账，不建议现在派。
4. **对下一步（判断）.** (a) 的结果与 D 路一致：这一支上决定成败的是比较表与换基的选择（V50、V290），不是来源表的形状。

#### 2. 文件表

| 文件 | 代码行（非空） | 物理行 | 冷编退出码 |
|---|---|---|---|
| `probes/OCF/Lean/YiCTCall.lagda.md` | 211 | 346 | 0（约 5 秒，最大驻留约 0.46 GB） |
| `probes/OCF/Lean/YiCTBase.lagda.md` | 81 | 133 | 0（约 4 秒，约 0.40 GB） |

- 每个文件都先删掉自己的接口再冷编，日志里只有自己模块的 `Checking` 行。
- 禁用构造与本机路径的检索结果为 0。
- 两个文件文首都标 "不读记号"，`importclosure.py` 检查为 OK（禁用表命中 0）。
- 临时文件 `CT0`–`CT3.agda` 在 `<实验目录>/work/YiCT/`。

#### 3. 定理表（陈述逐字）

| 名字 | 陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `cell` | `∀ o pv {j} (v : j ≤ h₁ n3) ot → IsNothing (kpᶜ (tw 1) o pv P₁ (inc n3 v) ot)` | 那一格对一切证据、来源表、孩子 3 里的路径都走链 | YiCTCall | 编译定理 |
| `org-P₁` | `∀ {j} (T : Org j (tw 1)) → org-at j (tw 1) T (inj₂ P₁) ≡ nothing` | 任何来源表在 P₁ 上都没有条目 | YiCTCall | 编译定理 |
| `d0-cell` | `∀ o pv (v₀ : h₁ n1 ≤ h₁ n2) ot → IsJust (kpᶜ (tw 1) o pv (inj₂ (n2 , inj₂ (inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))))) (inc n2 v₀) ot)` | d = 0 的同形格由地板保留 | YiCTCall | 编译定理 |
| `own-q′` / `at-q′` / `br-q′` | `kp (h₁ n2) (proj₂ (Ok-tw 1) n2) q′ self ≡ just (q′ , (λ z → z) , refl)`；`at (h₁ n2) q′ ≡ at (tw 1) P₁`；`Br (h₁ n2) q′ ≡ Br (tw 1) P₁` | 目标自己有同层号、同分支类型、可保留的槽位 | YiCTCall | 有限测试 |
| `E0` | `brᵍ n1 zero ≡ proj₁ (next⁺ β) + t₀` | 从 `cand₂` 的分支出发 | YiCTCall | 有限测试 |
| `E6` | `FC.ψ (tw 1) O R PV Bt j v OT βt y₃ ≡ FC.ψˡ (tw 1) O PV Xt j v OT βt′ (h₁ n3) (down stop n3) (proj₁ (Ωt (h₁ n3)))` | 分支 3 因表缺 (3,3) 走上折回退 | YiCTCall | 有限测试 |
| `E7` | `FC.ψˡ (tw 1) O PV Xt j v OT βt′ (h₁ n3) (down stop n3) (proj₁ (Ωt (h₁ n3))) ≡ limc⁺ F₃` | P₃（同层）走链 | YiCTCall | 有限测试 |
| `E10` | `FC.ψˡ (tw 1) O PV X₃ j v OT βt″ (h₁ n2) (down (down stop n3) tt) (proj₁ (Ωt (h₁ n2))) ≡ node⁺ (kpᶜ (tw 1) O PV P₁ v OT) (λ z → …) (λ z → …)`（两个函数逐字见文件第 285–289 行） | 那次调用及其参数 | YiCTCall | 有限测试 |
| `kp-P₁` | `kpᶜ (tw 1) O PV P₁ v OT ≡ nothing` | 这次调用走链 | YiCTCall | 有限测试 |
| `probe-call` | `pr t₂ ≡ proj₁ (Fch 0) + (proj₁ (F₃ 0) + proj₁ (FC.ψˡ (tw 1) O PV X₃ j v OT βt″ (h₁ n2) (down (down stop n3) tt) (proj₁ (Ωt (h₁ n2)))))` | 输出里的探针就是这次调用 | YiCTCall | 有限测试 |
| `hd₃` | `HeadLim (pr t₂)` | 那里是 ℕ 极限 | YiCTCall | 有限测试 |
| `cf-pos` | `posΩ (pr new₃) tt ≡ q′` | 比较表加 (3,3) 条目后，同一处保留在 q′ | YiCTCall | 有限测试 |
| `noOrg` | `(j b : L) (t : Pos⁼ b) → org-at j b (org-no j b) t ≡ nothing` | 空表没有条目 | YiCTBase | 编译定理 |
| `emptyOrg` | `(k j b : L) (F : …) (t : Pos⁼ b) → org-at j b (altOrg j b (org-no j b) (mapOrg k j F b (org-no k b))) t ≡ nothing` | `dlg` 在两部分都空时给空表 | YiCTBase | 编译定理 |
| `same` | `∀ (p : Pos (tw 2)) (w : tw 1 ≤ tw 2) → kpᶜ (tw 2) oₜ pvₜ p w otₜ ≡ kpᶜ (tw 2) oₜ pvₜ p w (org-no (tw 1) (tw 2))` | 两层 `ink` 处清空无影响 | YiCTBase | 编译定理 |
| `OT-empty` | `∀ t → org-at j (tw 1) OT t ≡ nothing` | (a) 那条路在 tw 1 上的主表为空 | YiCTBase | 编译定理 |
| `clr` / `anc` | `IsNothing (kpᶜ X₀ o₂ pv₂ top (inc zero u) (org-no j X₀))`；`IsJust (kpᶜ X₀ o₂ pv₂ top (inc zero u) ot₂)` | 不同的那个槽位 | YiCTBase | 有限测试 |
| `hx` / `pxᵃ` | `HeadLim (proj₁ (B₁ˣ j u))`；`posΩ (proj₁ Bxᵃ) tt ≡ qᵍ n1` | 底折叠输出：清空时走链，带祖先表时保留在 `qᵍ 1` | YiCTBase | 有限测试 |
| `link₁` | `brΩ (el (el (el (outᶜ n1) 1) 0) 1) tt zero ≡ proj₁ (next⁺ β) + proj₁ (G (proj₁ (Ωt X₀) + brΩ (proj₁ (Ωt X₀)) tt zero))` | 这个底出现在 `outᶜ 1` 里 | YiCTBase | 有限测试 |

#### 4. 第一个障碍

本路没有被挡住，三步都完成了。

我找到的数学上的障碍是两行定义的组合：`kpʳ (nd (sΩ k) h) _ _ (inj₂ _) (inc _ _) = nothing`，加上 `YiMTTab.tbᶻ` 在后继对后继时给 `nothing`。两者合起来，使 (3,3) 落到 `ψˡ` 回退。
- 对数字孩子，这是证据层面的问题：表可以字面填满，`cf-pos` 已验证。
- 对非数字的真实链孩子，我判断是可判定性上的数学障碍。这一点本路没有测试。

#### 5. 偏离与事故；未读、只凭转述引用的东西

**偏离.**
- 起初两个文件导入了 `YiKFValue`，它的闭包含记号。后来改为在 `YiCTCall` 里逐字复制 `At`、`brᵍ`、`posΩ`、`brΩ`、`IsInu`、`unU`（`YiKFValue` 第 77–143 行），文首已写明。
- (b)(i) 的两层 `ink` 实例（tw 3 → tw 2）是我挑的；它在任何实际折叠路径上出现，我没有证明。`cand₂` 这一支里只有一层 `ink`，所以我另给了 (ii)。
- `cf-pos` 换了比较表这个证据参数（局部定义 `R′`），没有改任何定义。

**小事故.** 第一次编译外面套了 `/usr/bin/time -l`，因沙箱不允许 sysctl，它返回 1；agda 本身是通过的，之后改用 `+RTS -s`。另有两处名字冲突（`R`、`own`），改名后通过。

**未读、只凭转述引用的.**
- `Reports-2026-11-16/AuditD.md`、`YiVA.md` 正文，以及附件 `AuditD-AuditDFin`、`AuditD-AuditDRow`：其中 `colFin`、`col-total`、`honest` 只按简报引用。我读过的是 `AuditD-AuditDCand` 和 `AuditD-plan`。
- 台账 V50、V149、V158、V287、V290，`YiSYReduce`，`YiKTSlot.Cand`，`YiRQDom`，`YiUSBound`，`YiVALeaf`，`YiBS*`，`YiBT*`。
- Bedrock 手册的 Q-1、Q-23 只定位、没有读（没有撞墙，用不到）。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：候选的两个有限测试（前缀 YiCT，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。这是两条 `refl` 级的检查，用来判断候选 (C) 的来源表要不要改；不改任何定义。同批另两路与你互不导入。

#### 作者的决定与背景（2026-11-17）
- Fable 5.2 的路线审核 D 路（先读定义、封存后再读结论；留档 `probes/Survey/Reports-2026-11-16/AuditD.md`，判定件附件 `attachments/AuditD-*.txt`）与此前的独立审核 YiVA（`Reports-2026-11-16/YiVA.md`）两份封存件独立判断：现行折叠在 "Ω 形状结点下、材料在一个孩子里、目标在另一个孩子下面" 时没有实现 "低于目标保留"（`YiRWFold.kp` 的 `(inj₂ _) (inc _ _) = nothing` 一行与 `YiTBRow.ψ` 的退路行），同步对象上的那一步链步（`YiKTSlot.Cand`）不成立。**作者据此定（选项原文）："按两份审核关闭 (Recommended)"**：现行折叠上 `Cand` 这一格及其值否定线关闭，不再派它的任何变体（它在第七十一到七十四批以 `TightStep 1`、`TightDom`、`Top₁`、`Refute`、`single`、`Branch`、`cand₁` 七个名字出现过；台账 V287）。
- 第七十五批作者选三路（选项原文）："真实链孩子上的最小实例 (Recommended)"、"对折叠参数化的整体接口 (Recommended)"、"候选的两个有限测试"。前缀 `YiRK`（Opus 5.5）、`YiFI`（Fable 5.2）、`YiCT`（Opus 5.5），互不导入。**主线定义不动**；改树、折叠、合法性只在新文件里做候选。
- D 路审核要点（判断，未编译）：决定成败的是台账 V50（读回域上被问到的 "目标孩子 c′、材料孩子 c" 的对，是否都带字面证据）。真实同步对象的链在第 0 层（`YiSYReduce`：层号 `nd (sΩ zero) a`，`chain` 是 `feed` 的迭代），真实链孩子是 `a (chain m)`，`chain m` 是回灌输出，不是数字；第七十二到七十四批的测试都在数字孩子 `a₁ (suc d)` 上。数字孩子是可判定的特例：比较表在 "任一端是数字" 的整列可字面填满（`AuditDFin.colFin`、`col-total`），换表后那一格如实进孩子层朝原目标折（`AuditDRow.honest`；现行表下是 `fallᶻ`）。对一般孩子，任何表都不能让每一支如实，只能指望与目标孩子字面共尾的那一族如实；这是换基（台账 V149、V158）要做的，11-14 选比较表而不选换基的决定要重看（V290）。
- 已编译的机制（主审复核过）：`YiVALeaf.fall-diag`、`leaf-branch`（不读记号）；`YiRQDom.drop`、`fall`、`start-form`、`kp*ᵍ`、`kp₀ᵍ`；`YiUSBound.base-form`、`leaf-node₂`；候选原型 `YiDXFold`（`Fold (K : KeepFn) (lifted : Bool)`，(A) `kpᴬ`，(B) 上折回退 `ψˡ`）、`YiKFKeep`/`YiKFFold`（(C) 来源表 `Pv`、`Org`、`kpʳ`、`kpᶜ`），`YiKFValue`（值定理用标准底 `B₀`，不是 `Cand` 的继承底）；`AuditDCand.cand`（候选在塔第 1 项、目标层 ≥ 2 时对层号非零的槽位仍走链）。换基原型：`YiBSFold`、`YiBSBase`（`split`、`seen`）、`YiBSReadNeg`、`YiBSClean`、`YiBSCrit`（只到数字孩子）、`YiBTZero`、`YiBTOne`。
- 主线现状：第一档成品已完成；终点无条件值 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω)（`YiFYRef.target-low`）；里程碑 ψ₀(Ω_{Ω₂}) 未达到。

#### 要做的（按序）
**(a) 审核那一格在不在实际折叠路径上。** `AuditDCand.cand`（附件 `attachments/AuditD-AuditDCand.agda.txt`）：槽位在 `tw 1` 的孩子 3 里、层号 `h₁ 2`，目标 `h₁ 3` 自己有这个槽位（`own-slot`），路径 `inc three self`，候选 `kpᶜ` 对一切来源表给 `nothing`。问：`YiKFValue.cand₂`（d = 1，目标 `h₁ 2`）与 `top` 的实际折叠过程里，是否用到这一格或它的同形格（例如槽位层号 `h₁ 1`、目标 `h₁ 2`、路径 `inc two self`）。办法：沿 `outᶜ` 的定义展开到用到 `kpᶜ` 的地方，用 `refl` 或对变量的等式写出那次调用的参数（仿 `YiKFValue.hdᵍ`、`posᵍ`、`br-form`）；闭项大时按 C-9 在变量上陈述，具体闭项放 `opaque`。交：在路径上（给出调用点）、不在（说明为什么），或判断（标档）。
**(b) 来源表在 `up` 行底参数处清空的影响。** `YiKFFold.ψ` 的各 `up` 行把底参数写成 `λ i u → ψ … (org-no _ _) …`。取一个经两层 `ink` 到达的孩子，比较底折叠里某个槽位在 "带祖先来源表" 与 `org-no` 下的 `kpᶜ` 结果（写一个临时的 "带祖先表" 版本作对照，只在临时文件或新文件里）。交：两者在这一格上相同还是不同（编译事实），不同时写出不同的那个槽位。
**(c)** 一页判断（标档）：候选 (C) 的来源表是否要改成对目标的族（`Base` 是对一切目标的族，`Org` 是单目标的）。

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

