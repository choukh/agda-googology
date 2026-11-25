# F 路：LowSlot 会不会重蹈覆辙（先读定义，后读结论）（Fable 5.2）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-17 06:36 至 06:54 |
| 工具调用 / agda 编译 (粗数) | 36 / 3 |
| token (usage 字段，按消息去重) | 输出 97893；新写入缓存的输入 248020；读缓存的输入 3928523；其余输入 58 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `AuditF` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审核封存哈希一致（3a877710…，UTC 2026-11-17T06:40Z）；三个判定件主审 8G 冷编退出 0（附件 attachments/AuditF-*.txt）；LowSlot 是主线全域律里原先没写出的一半，照现陈述直接攻会重蹈覆辙；现有两个不变式下的 LowSlot 被编译否定（¬LowSlot₀、¬LowSlot₁），那两个实例上的 ebo-endˢ 前提不可满足；加强不变式后接线合上（Plus.ebo⁺），但对一切树量化仍太宽（FCross 形状档）；建议先把量化域收到读回域，再证 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b80/AuditF.md`。先用 Read 工具完整读它，再逐条照做（含 "先读"、"第 1 步封存之前不要读"、"规则" 与 "回报" 各节）。只在简报指定的临时目录里写，不改仓库里任何文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### F 路回报：LowSlot 会不会重蹈覆辙（Fable 5.2，2026-11-17）

#### 0. 对纲领与目标意味着什么

- **结论**：`LowSlot` 就是主线那条全域律里原先没写出来的一半（朝非零目标层的保持）。照现在的陈述直接攻，会重蹈覆辙。
- **现有两个实例前提为假（编译）**：`W₀.LowSlot` 与 `W₁.LowSlot` 都可反驳。所以这两个实例上的 `ebo-endˢ` 前提不可满足，什么也没说（AGENTS "前提要可满足"）。`ebo-end₀`、`ebo-end₁`（前提是 `ChainRel`）不受影响。
- **读法**：反例状态不可达（底与上下文 K 无关），属 "谓词太宽"，不是数学障碍，不否定换基路线。
- **换一个不变式后接线能合上（编译）**：把 "槽位层的底对着 ψ_κ(K)" 记进不变式，`Wire` 三个参数都能实填，条件定理仍成立，零树反例消失。
- **仍然太宽（判断）**：改后的陈述对一切树 y 与一切槽位 p 量化，孩子侧槽位的分叉出口在它的量化域里；形状已编译，值的否定没有。
- **对纲领**：三件都是验收侧文件（读记号），不改树、折叠、合法性；没有新的值，终点 ψ₀(Λ) 的状态不变。
- **对 "让树自足"**：这一轮问题全在量化域与不变式（参照一侧的记账），没有新的树侧判据。

#### 1. 封存

- 文件：`<实验目录>/audit/F/plan.md`
- SHA-256：`3a87771002f44c7fe7a6b57b37541e294086ec08a51af46cb9bbc904d84ae330`
- UTC：2026-11-17T06:40:39Z，封存后未改。
- **污染声明**：封存前 grep `KeepAt` 时命中了 `YiBAEbo` 文首第 3–4 行（判决段），看到 "ψ₀ 根上下文下 Below 与 NodeRef 不成立，KeepAt 条件下成立"。计划里已写明。

计划全文：

```
# F 路第 1 步: 只读定义后的判断 (封存件)

读过的只有定义体: YiRWBlock/Path/Ops(Ωt, ⊞)/Fold(kp, node⁺), YiTBRow.ψ, YiMTTab.rbᶻ, YiAbsGIface, YiGIInst, YiGIEnd, YiBSBase, YiBSFold.ψ, YiWRZero, YiWREnd, YiGIRel, YiHCRel, EBO(cof, cofψ₊, fsT 签名, γ 链说明), EboLeanDef.fsn.
污染声明: grep `KeepAt` 时命中了 YiBAEbo 文首第 3–4 行 (判决段), 看到了 "ψ₀ 根上下文下 Below 与 NodeRef 不成立, KeepAt 条件下成立" 一句. 下面 (a) 里 "派发一致" 一条在看到它之前已从 kp 与 cofψ₊ 的定义得出, 但不能排除受它加强. 以下全是判断档, 没有编译.

## (a) LowSlot 要证的是什么, 哪里最难

陈述: 对一切层号 a, 一切状态 s = (o, r, B, β) (只受 Inv s K 约束), 一切槽位 p, 一切满足 Nu a p κ 的 κ, 一切 R a η y:
R (at a p) (ψ_κ(K ++ η)) (ψ a o r B (at a p) (posW a p) (B (at a p) (posW a p)) y).
朝第 0 层的那一半 (lowᶻ) 之所以能合上, 是因为 z≤ 在非零层处处是 inu, 嵌入行逐字落进孩子 (fallᶻ′ = refl), 第 0 层没有槽位所以 kp 恒为 nothing. 朝槽位层的路径 posW 由 inc / ink 加 self 组成, 所以 LowSlot 要过折叠的全部行. 按对 R a η y 的推导归纳, 四处:

1. 零树 (y = zero, η = []): 结论是 R (at a p) (ψ_κ(K)) (B (at a p) (posW a p)). Inv₀ 只说 β, Inv₁ 只说 B i u ⊵ Ωt i. ψ_κ(K) 对非空 K 高于 Ω_κ, 而 Ωt 对着 Ω_ν (Leaf). 所以对 W₀, W₁ 这两个实例, LowSlot 在基础情形就缺前提; 我判断它对 Inv₀ 是假的 (取 a = tw 1, p 为下标槽位, κ = [], B = B₀, β 很大, K 非空: 要 R zero (ψ₀(K)) (suc zero)). 这是 "谓词太宽" 一类, 不是数学障碍.
2. 把 Inv 加强到 "∀ i u κ. R i (ψ_κ K) (B i u)" 才够基础情形; 但 inv-step 要对 stepᶻ 之后的底 B′ i u = ψ a … i (inc c u) (B i (inc c u)) x 证同一条, 这是朝任意层 i, 沿任意路径 inc c u 的保持, 比 LowSlot (只沿 posW) 更宽. 而 Wire 的 inv-step 只给朝第 0 层的结论 q. 所以够用的 Inv 不能由 Wire 现有的参数签名供给: LowSlot 与 Inv 的保持是互递归的, 合起来就是 "一切目标层, 一切路径" 的全域律.
3. 结点 y = Ω q g (cof η = cΩ κ′): 树一侧按 kp a o q (posW a p) 的字面结果派发 (just: 在目标层的槽位上保留; nothing: 链的部分和极限), 参照一侧按 cmpᵀ (κ′+1) κ 派发 (gt: 余尾 ω, γ 链; lt/eq: 余尾 Ω_{κ′+1}). 两边必须一致. 但 Nu a p κ 与 Nu a q κ′ 只是上界 (Rd = Cl, 有 c0 与向下封闭 cc), κ 不由 p 决定; 例如 κ = [] 对一切 p 都满足 Nu. 树保留而参照取链时, R 的规则里 Ω 结点只经 ◃w 接第一分支, 对不上 γ 链; 树取链而参照保留时, ℕ 极限对着余尾 Ω 的项, 只剩 mc 一条规则可用. 我判断这是最难的一处, 而且在 "∀κ. Nu a p κ" 的量化下陈述本身可能为假. 另: kp (nd (sΩ k) h) _ (inj₂ _) (inc _ _) = nothing 是无条件的, 即使槽位与目标经同一个孩子.
4. 嵌入 y = up x c y′, a = nd (sΩ k) h, 路径 inc c′ v: 换基行按 r 的 Schema 与 route 分三路: j ≤ floor 进孩子 c (要 stepped 状态上的同一条律, 回到第 2 点); floor ≤ j 给 seen ⊞ ψ₀ y′; r 无 Schema 给 ψ x ⊞ ψ₀ y′. 后两路是加法, 参照一侧是 ψ_κ(K ++ t ++ s), s 随 y′ 无界. LowSlot 对一切 r 量化 (Stᶻ 含 rb-no), 所以加法行在陈述的量化域里.

## (b) 主线全域律卡在哪, 是否同一处

主线 LowKeep 的实例 (domsᵍ) 只管 Wl = z≤ (朝第 0 层), Gx = Ωt ℓ. 按定义看它不能对自己归纳: 结点的链步是朝槽位层 (非零) 的折叠, 嵌入行把状态换成 stepped 的底, 所以证明必须推广到一切树, 一切目标, 一切路径; 推广后就碰到表 rbᶻ 缺项时的加法行与 (a)3 的派发一致. 我判断主线卡在 "朝非零目标的保持没有陈述 + 加法行". LowSlot 把前一半陈述出来了, 是同一条律里原先没写出的那一半, 不是另一条律; 卡点 (a)2, (a)3, (a)4 与主线推广后的卡点是同一组.

## (c) 换基与 ψ_κ 上下文改变了什么

改变: (i) 参照一侧的头从固定的 ψ₀ 换成 ψ_κ, 使朝非零层的结论有了能与 fsT 交换的形状 (chain←slot 的 go (suc k) 只用 fsT++), 朝第 0 层的那半已无条件归约到 LowSlot. (ii) Schema 让 "目标 ≤ floor" 的情形进孩子而不走加法, 比 rbᶻ 表 (只有字面零孩子有条目) 覆盖更多.
没改变: 状态与底的量化仍是全域; Inv 不约束槽位层的底与 r; κ 仍只是上界; floor ≤ j 与无 Schema 两路仍是加法; kp 的字面派发与记号比较的一致性没有进陈述.

## (d) 更便宜的路

终点只用 folded n, 即 ChainRel 只在从 rootᴮ n 出发, 沿 dom-top (dom-keel n) 这一棵推导实际到达的 (状态, 槽位, κ, g) 上被调用. 候选:
1. 把 Inv 取成可达谓词 (由 inv-root, inv-step 生成的最小者, 并记下 r = rb-tw 的后代, B 的来历), κ 取槽位层的规范读数而不是 "一切 Nu"; 先在 tw 1, tw 2 上实填, 再定陈述.
2. 把律改成对结构参数 n 的一步定理: 设 tw n 层上 (一切目标, 路径) 的保持成立, 推 tw (n+1); 只有这一步新用到的字段进前提.
3. 不经 R 的全域归纳, 只对规范树与规范读法证一步支配 (参照项的每一步基本列被折叠值的一步 ◃ 支配), 链点的支配用 chain-dom 在目标层的推广.
判断: 直接攻现在的 LowSlot (W₀ 或 W₁) 大概率得到退化反例; 应先换陈述 (候选 1), 并先编译 (a)1 的否定来确认量化域太宽.
```

**封存件里事后要更正的两处**（封存件未改，在此说明）：

- **(a)2 说重了**。不变式的保持只要孩子的槽位路径：孩子 `h c` 的槽位 p′ 的路径 `inc c (posW (h c) p′)` 逐字就是本层槽位 `inj₂ (c , inj₂ p′)` 的 `posW`，所以 `inv-step` 可以用 `LowSlot` 自己供给（`FWire.inv-step⁺`，编译）。"要一切路径" 这一条只对 `LowSlot` 的证明内部成立（判断）：`ink` 行把路径换成 `v ∙ kh c`，不是 `posW` 形。
- **(a)3 里 "κ 取小时陈述可能为假" 不成立**。小 κ 可由规则 `mc` 从较大的 κ 得到（ψ 的下标先比）。代价是 `mc` 结点变多，而出口条件 `Exᴴ` 要求每个 `mc` 结点两边是标准形且可数（见缺口 G5）。

#### 2. 对照之后逐条

**(1) "`LowSlot` 与主线全域律同类"：同意，可以说得更准。**

- 主线 `LowKeep` 的实例只管朝第 0 层（`Wlᵍ` 只有 `wz`）、Ω 树（`Gx`）、`rbᶻ` 的底。它不能对自己归纳，因为结点的链步是朝槽位层的折叠（`YiRWFold.ψ` 的 Ω 行）。
- `LowSlot` 正是那个链步的保持，所以它是同一条律推广后的另一半，不是平行的另一条律。
- `lowᶻ` 已把朝第 0 层的一半无条件归约到它（冷编过的定理，我只读了陈述与定义体）。

**(2) "换基让树一侧分叉出口不出现，前提里不再有现行折叠那几格被否定的东西"：对 `LowSlot` 这个前提不成立。**

- 这句话在读回域里成立（LOG 中 YiXT 的读法、对照表 §9）。但 `LowSlot` 对一切状态（含无 `Schema` 的证据 `rb-no`）、一切树 y、一切槽位 p 量化。
- `kp` 是现行与换基共用的同一定义，孩子侧槽位那一行（R77）换基没有改（对照表 §5、§9）。
- **编译（形状）**，`FCross`：塔第 2 项，目标是孩子 0 一侧的槽位（层号 `tw 1`），结点槽位是孩子 0 里 `tw 1` 的下标槽位（第 0 层）。
  - 对一切状态与分支函数，折叠值是 ℕ 极限（`tree-lim`）。
  - 参照 ψ_{Ω₁}(X + Ω₁) 的余尾是 Ω₁（`ref-cof`）。
  - Ω₁ 是目标槽位允许的下标（`rd-Ω₁`、`nu-p`）。
- **判断（值）**：取 X 为塔第 2 项 Ω 树的参照，g c = `up x_X zero (嵌入 (suc c))`。树的链点全可数，值约为 ψ_{Ω₁}(X) + 可数量；参照 ψ_{Ω₁}(X + Ω₁) 更高。这个 y 在根状态 `rootᴮ 2`、K = [] 上就有，不靠退化状态，但不在读回域里。值上的否定未编译：`R` 在非零层没有值的读法，要先有 `R` 的可靠性引理。
- 对照表把同一格标为 "低（判）"，把 "y 一般只进尾项" 标为 "低（判）"；若属实，改后的 `LowSlot⁺` 在全域上也是假的。
- **主审那句话应改成**："在读回域里换基没有分叉出口；`LowSlot` 的陈述没有限制在读回域里，分叉出口仍在它的量化域内。"

**(3) 直接攻 `LowSlot` 还是先换陈述：先换陈述。**

- `W₀`、`W₁` 两个实例已编译否定（`FNeg.¬LowSlot₀`、`¬LowSlot₁`）。
  - 反例：层号 `nd sS (λ _ → zero)`，默认底 `B₀`，K = 1，底值 `next⁺ (Ωt zero)`，零树。
  - 结论要求 `R zero (ψ₀(1)) (suc zero)`，而对着树 1 的参照项只有 0 与 1（`inv1`，对一切层）。
  - 前提可满足：`inv₀-s₁`、`inv₁-s₁` 实填。
- 换陈述第一步已合上（`FWire`，编译）：`Inv⁺` = 底值条件 + "每个槽位 p、每个允许的 κ，槽位层的底对着 ψ_κ(K)"。
  - `Plus.ebo⁺ : ExitCondition (chain←slot ls) → toL EBO-tree′ ≼ readRW EBOᴮ`。
  - 模块前提：`LeafSlot`（塔各项槽位层上 Ω_κ 对着 Ω 树，未证）与 `LowSlot⁺`（未证）。
  - `base-need`（`FNeg.Need`）说明这个加强是必要的：任何使 `LowSlot` 成立的不变式都推出它。
- 还要再收一次量化域：对 y 与 p 收到读回域（依据 (2)）。连同 YiQD、YiZS 的 "对任意树量化"，这已是同形的第三次，按 AGENTS 应停下查量化域，不逐个加字段。
- `RR3-Backward` §3.1 的 "一步支配的解释"：它只把终点定位到 "值忠实的 ι + 两条一步不等式"，文中自己说不降低难度。现在的 `R` + `Exᴴ` + `exitᴴ` 已是它的一个实例（ι 是 "存在带出口条件的 `R` 推导"）。所以它不是绕开全域律的另一条路；它给的提示是终点只要规范项 ψ₀(Ω 塔第 n 项) 的推导，不要全域的 `R`。

**(4) 有没有重复同一类引理：有。**

- **同一条 "朝低层保持" 至少七个名字**：`LowKeep`（`YiAbsGIface`）、`lowᴮ`/`lowᵗ`（`YiBLFold`）、`lowˣ`、`lowᴰ`、`lowΩ`、`lowᶻ`、`LowSlot`（后四个出自 LOG 与台账的转述及 `YiWREnd`）。区别只在目标、路径、上下文的头 ψ_ν、量化域、不变式五个参数。建议合成一条带这五个参数的接口，记进 `YiAbsGIface` 一族。
- **分级结构实例重复**：以 `GR.R` 为关系的 `Graded` 实例至少四份（`gradedᵍ`、`gradedᴮ`、`gradedᴱ`、`gradedˢ`），生成原理 `genᴮ` 在 `YiWREnd` 与 `YiBAEbo` 各一份。
- **小引理重复**：`ψ-⊵` / `ψ-⊵ᴮ`；`mz′` 与各处的零规则；`Inv₁` 的第二项就是 `Bdᵍ` 的第二项。我写的 `lift⁰` 很可能与 `YiGLDom.liftᴰ` 一类重复（未核）。
- **过程层面**：第七十八、七十九批与 `YiGIEnd.Assembly` 之后的拆分是同一形态（条件归约，主前提是全域律）。主审在 LOG 里已如实写了这一点。

#### 3. 缺口清单

| 编号 | 陈述 | 档 |
|---|---|---|
| G1 | `W₀.LowSlot → ⊥`，`W₁.LowSlot → ⊥`。后果：`W₀.ebo-endˢ`、`W₁.ebo-endˢ` 前提不可满足 | 编译（`FNeg`） |
| G2 | `LowSlot⁺`（不变式 `Inv⁺`）未证。零树情形由不变式给出；后继与极限情形有 `nextψ`、`cofψω` 一类（只见用法）；结点与嵌入情形未做 | 未证 |
| G3 | `LowSlot⁺` 在孩子侧目标槽位 + 孩子侧结点槽位上，树取链而参照保持余尾 | 形状：编译（`FCross`）；值上为假：判断 |
| G4 | `LeafSlot`：∀ n p κ. `Nu (tw n) p κ → R (at (tw n) p) (Ω_κ) (Ωt (at (tw n) p))`。是主线 `Leaf` 在 `GR.Rd` 上的形式；已编译的 `leafᴰ` 在另一个域 `Dom` 上。两个域的接法 LOG 记为未查 | 未证 |
| G5 | 出口条件 `ExitCondition (chain←slot ls)` 依赖 `ls` 这个证明项的内容，不只依赖它的类型：`R` 在 `Set` 里，`Exᴴ` 对推导递归，要每个 `mc` 结点两边标准形、较大一边可数。`LowSlot` 的证明里用 `mc` 调下标或调派发的地方会经 `dom-top` 的 `dc`、`leE` 流到第 0 层的推导里。所以 `LowSlot` 与出口条件不是两个独立前提 | 判断（依据 `Exᴴ`、`restᴱ.leE`、`dom-top` 的定义体） |
| G6 | `LowSlot` 的证明内部要一般路径上的保持：`ink` 行给 `v ∙ kh c`；Ω 形状层号的 `inc` 行在 `floor ≤ j` 与无 `Schema` 时是加法（`seen ⊞ ψ₀ y`），参照是 ψ_κ(K ++ t ++ s) | 判断；对照表标 "未知" / "低（判）" |
| G7 | 在终点实际走到的推导（`lowᶻ` 作用于 `rootᴮ n` 与 `dom-top (dom-keel n)`）里，孩子侧目标槽位与 Ω 形状层号上的 `inc` 行是否出现 | 判断：不出现（Ω 树一族只在后继形状层号上有孩子侧槽位，嵌入的左部是零树）。没有编译，没有逐链点展开 |
| G8 | 值：换基闭项 `EBOᴮ` 没有任何站值定理；终点下界仍是条件定理 | — |

#### 4. 推荐的下一步

1. **换陈述，不直接攻。** 把 `LowSlot` 的量化域收成读回域的谓词：状态可达（由根与 `stepᶻ` 生成），树在 Ω 树一族里，槽位是实际链步用到的那几种。先在 tw 1、tw 2 的规范实例上实填，通过后定稿。依据：G1（编译）、G3（形状编译 + 判断）、AGENTS "量化域先取带证据的读回域"。在跑的 YiSO 若证的是全域的 `LowSlot`，应把 `FNeg` 与 `FCross` 的两个实例转给它。
2. **把 G7 编译掉。** 写一个可达谓词，证明 "可达状态上被折叠的树都在 Ω 树一族里，结点槽位是下标侧的或后继形状孩子侧的"。这决定第 1 条的读回域够不够，也决定换基行在终点里到底用不用得上。若 G7 成立，换基对终点的作用只剩孩子的底，要重新算账。
3. **先处理 G5 再证律。** 两个做法任选：把标准形与可数的要求放进 `R` 的 `mc` 规则（验收侧关系，不动树）；或另证一条 "规范推导满足 `Exᴴ`"。否则 `LowSlot` 证出来以后出口条件仍可能不成立。
4. **合并。** 把 `LowKeep`、`lowᶻ`、`lowˣ`、`lowᴰ`、`lowΩ`、`LowSlot` 写成一条带（目标、路径、ψ_ν、域、不变式）参数的接口；`Graded` 实例与生成原理各留一份。

**不建议的**：把 "一步支配的解释" 当作绕开 `LowSlot` 的新路线单独开一路（理由见 (3)）。

#### 5. 编译过的文件

都在 `<实验目录>/audit/F/`，各自 8G 单独编译，退出 0，日志是同名 `.log`。选项行按简报；无 `postulate`、洞、`TERMINATING`、K、`trustMe`。警告只有 `UnsupportedIndexedMatch`，以及 `FCross` 里一处多余的 `using`。接口取仓库已有的，没有删 `.agdai`。

| 文件 | SHA-256 | 主要陈述 |
|---|---|---|
| `FNeg.agda` | `4702090da2a91471aaa5d269dd9b900cdfb9641a9e05e52b2a34ac5f60be8692` | `inv1`、`lim-le1`、`inv₀-s₁`、`inv₁-s₁`、`¬LowSlot₀`、`¬LowSlot₁`、`Need.base-need` |
| `FWire.agda` | `d53dc815cedf835a9a9895a72c054cdc568cfb585d4049b4b6866b94a4f6e514` | `Inv⁺`、`LowSlot⁺`、`LeafSlot`、`inv-step⁺`、`inv-root⁺`、`Plus.same`、`Plus.ebo⁺` |
| `FCross.agda` | `0cc25d58a81a9a613ced40bc01df768ef334a49c3cd22558c5cec84124287f46` | `tree-lim`、`ref-cof`、`lift⁰`、`rd-Ω₁`、`nu-p`、`nu-q` |

逐条说明：

- `inv1 : Mᴴ S Low Chd Nu τ x → x ≡ suc zero → (τ ≡ []) ⊎ (τ ≡ 𝟏 ∷ [])`，对一切层。
- `lim-le1`：余尾 ω 的项第 2 项不是 0 也不是 1。
- `Need.base-need`：对任何不变式，`LowSlot` 推出槽位层的底对着 ψ_κ(K)。
- `Plus.same : W⁺.LowSlot → LowSlot⁺` 是恒等，即 `Wire` 里的 `LowSlot` 逐字就是 `LowSlot⁺`。
- `FCross` 是形状档，不是值的否定。

#### 6. 没有读、只凭转述引用的东西

- **简报列为关键但没有打开的模块**：`YiCMExit`、`YiXTIface`、`YiXTReb`、`YiXTCur`、`YiBAWeak`、`YiSDIface`、`YiSDRead`、`YiQDIface`、`YiQDFold`、`YiUFExit`。关于它们的说法（`kp-exit`、`stuck`、`Below`/`AboveL`、`lowˣ`、`lowᴰ`、`lowΩ`、`nodeʳ`、`keepS` 等）全部来自 LOG 11-17 各段、台账 V300–V309 与对照表 §5–§10。
- **只读了一部分的**：
  - `YiBAEbo`：文首、`KeepAt`、`¬below`/`¬noderef`/`main-¬below₀` 的陈述。
  - `YiBALemma`：`keepψ`、`collψ`、`inv0`、`fsn1` 一段。
  - `YiGLDom`：`Dom` 前三个构造子、`dom-top`、`leafᴰ`、`liftᴰ`、`dom-keel` 的签名。
  - `YiGTGen`：`weakenᴿ`、`closeᴿ`、`Ω≤ψ`。
  - `YiRWOps`：`Ωt`、`⊞`、`limc⁺`、`cum`。
  - `CompareTable`：§0、§1、§5–§10。
  - `RR3-Backward`：§2 与 §3.1。
- **只见用法、没读定义体的**：`YiFIIface`/`YiQDIface`/`YiXTIface` 里的 `Sys`、`OutDN`、`AboveL`、`XTree`、`SuffD.keepAllᴰ`，以及 `nextψ`、`app≤ν`、`fsT++`、`cofψΩ`、`Up`、`emb`、`pre` 的展开。"`lowᶻ` 已把朝第 0 层的一半归约到 `ChainRel`" 依据的是 `YiWRZero`/`YiWREnd` 的定义体与主审的冷编记录，我没有重编这两件（`FWire` 的编译用到了它们的接口）。
- **没有独立核对的**：
  - G3 的值的论证（ψ_{Ω₁}(X) + 可数量 < ψ_{Ω₁}(X + Ω₁)）是纸面的序数估计，其中 "根状态在 `tw 1` 层的底约为 ψ_{Ω₁}(Ω_{Ω₁})" 是按行展开的估计，没有编译。
  - 对照表各格的 "低" 是该表自己的判断，我没有独立核对。
  - 在跑的 YiSO、YiWC 两路的内容没有看。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：F 路，LowSlot 会不会重蹈覆辙（先读定义，后读结论）（Fable 5.2）

你在 Agda 研究仓库 `<仓库>` 上做一次独立的数学审查。全程用中文。你的临时目录是 `<临时目录>/`，只在那里写。

#### 先读
- `AGENTS.md` 全文。
- **第 1 步封存之前不要读**：`probes/README.md`、`probes/LOG.md`、`probes/RESULTS.md`、`probes/Survey/RouteReview3.md`、`probes/Survey/IdeaLedger.md`、`probes/Survey/GoalOdds.md`、`probes/Survey/Reports-*`、`probes/Survey/CompareTable.md`，以及各模块文首的判决段。

#### 问题
终点 EBO = ψ₀(Λ)。主线早有一条终点的条件定理（`YiGIEnd.Assembly`：Leaf、Lift、全域律 LowKeep、出口条件 ⇒ `toL EBO-tree′ ≼ readRW EBOᶻ`），全域律一直没证出，后来拆成了站与格。现在换基候选上有一条同形的条件定理（`YiWREnd.Wire.ebo-endˢ`），主前提是 `LowSlot`（朝非零目标层的保持）。你要独立判断：`LowSlot` 会不会像主线那条全域律一样卡住；换基加 "参照下标随目标层号走" 是否真的改变了它的难度；有没有不经这条全域律的更便宜的路。

#### 第 1 步：只读定义，写自己的判断并封存
只读这些定义（`grep`/`sed` 查签名与定义体，不整篇读大文件；都在 `probes/OCF/Lean/`，参照在 `probes/OCF/Align/`）：
- 主线：`YiRWFold`（`kp`）、`YiTBRow`（`ψ`）、`YiMTTab`（`rbᶻ`）、`YiAbsGIface`（`LowKeep` 与 `Graded`、`Doms` 的字段）、`YiGIInst`（`gradedᵍ`、`domsᵍ`）、`YiGIEnd`（`Assembly`）。
- 换基：`YiBSBase`（`Schema`、`split`、`seen`）、`YiBSFold`（`ψ`）、`YiWRZero`（`Stᶻ`、`slotFold`、`ptᶻ`、`fallᶻ′`）、`YiWREnd`（`Wire` 的模块参数、`LowSlot`、`ChainRel`、`chain←slot`、`ebo-endˢ`）、`YiBAEbo`（`gradedᴱ`、`KeepAt`）。
- 参照：`EBO.lagda.md`（`cof`、`fsT`、`γT`）、`EboLeanDef`（`fsn`）、`YiGIRel`（`R`、`Rd`、`Nu`）、`YiHCRel`（`Mᴴ`、`Exᴴ`）。
写一页以内的判断：(a) `LowSlot` 要证的是什么，在哪一种结点、哪一种路径上最难；(b) 主线那条全域律最可能卡在哪里（只从定义判断），`LowSlot` 是否卡在同一处；(c) 换基与 ψ_ν 上下文改变了什么、没改变什么；(d) 有没有不经全域律的更便宜的路（例如只对规范树与规范读法的一条一步定理，像 `RR3-Backward.md` §2 说的 "一步支配的解释"）。写进 `<临时目录>/plan.md`，`shasum -a 256` 算哈希、记 UTC，回报里给出。封存后不改。

#### 第 2 步：对照并挑战
封存后读：`probes/Survey/CompareTable.md`；`probes/Survey/RR3-Backward.md` §2；`probes/LOG.md` 从 "2026-11-17: YiCM (对照表) 回来, 复核" 起到文末；台账 V300 到 V309。关键模块：`YiCMExit`、`YiXTIface`、`YiXTReb`、`YiXTCur`、`YiBAEbo`、`YiBAWeak`、`YiSDIface`、`YiSDRead`、`YiQDIface`、`YiQDFold`、`YiUFExit`、`YiWREnd`。挑战主审判断：(1) "`LowSlot` 与主线全域律同类"；(2) "换基让树一侧分叉出口不出现，前提里不再有现行折叠那几格被否定的东西"；(3) 接下来该直接攻 `LowSlot`，还是先换陈述（更窄的量化域、一步支配的解释、或别的）；(4) 过程里有没有又在重复同一类引理。

#### 第 3 步（可选）：编译一个判定件
纯 `.agda` 放在你的临时目录，选项行 `{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns #-}`。编译（仓库根目录）：`agda +RTS -M8G -RTS --library-file=<库文件> -i src -i probes -i <临时目录> <文件> > <临时目录>/<文件>.log 2>&1; echo "exit $?"`。同时只跑一个 agda。不许 `postulate`、洞、`TERMINATING`、K。

#### 规则
- 只在你的临时目录里写文件。不改仓库里任何文件，不删 `.agdai`，不用 `--ignore-interfaces`，不 `rm`/`pkill`，不写 `/tmp`，不装包，不提交。
- 区分三档：编译定理、有限测试、判断。判断路线走不通必须指明依据；没有就写 "未走通" 或 "存疑"。不用比喻和方向性形容。强度写 ψ₀(Ω_x)。

#### 回报（最后一条消息就是回报，主审会原样留档）
0. 对纲领与目标意味着什么。1. 封存：哈希、UTC、计划全文。2. 对照之后逐条（上面 4 问）。3. 缺口清单（精确到陈述，标档）。4. 推荐的下一步（最多 4 条）；若认为应换陈述或换攻法，明说并给依据。5. 编译过的文件（若有）。6. 没有读、只凭转述引用的东西。

