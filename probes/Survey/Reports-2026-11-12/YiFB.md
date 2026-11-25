# 路二：经 F2 的两座桥（数学，构造） (YiFB)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-16 第六十七批（选项四路全选）；外部模型，作者转发 |
| 前缀 | `YiFB` |
| 回报 | 2026-11-16 代码已由 Claude 主审冷编复核；回报原文尚未留档；作者已复核并接收，本会话免复核 |

## 简报原文（本机路径换成占位）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

## 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第六十七批四路之一（作者选项原文："路一：证后继一步 (Recommended), 路二：经 F2 的两座桥 (Recommended), 接线重派 (Recommended), 摆脱侧：接着填树侧比较 (Recommended)"）；本路的侧面：路二：补两座桥，用 F2 对一切可数层号的定理直接得到所有孩子的第 1 层关系，绕开后继一步。四路在数学上互不依赖，不等也不导入彼此的文件。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **终点归结为各站的值下界**（编译定理）：`YiS1Accept.Kᴱ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)`，`YiS1Accept.ebo-from-stations : (∀ n → Kᴱ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`。各行的参照：第 1 站 ψ₀(Ω₁)，第 2 站 ψ₀(Ω_Ω)，第 3 站 ψ₀(Ω_{Ω_Ω})。第 0、1、2 站在实际底上已成立（`YiFRStations.k0`、`k1`、`k2`；第 1、2 站由已有的 BTBO 下界得到）。已知的无条件终点值是 ψ₀(Ω_Ω+ψ₁(Ω_ω))，低于第 3 站的参照。
- **站间归约**（`YiFRStep`，先读定义的独立审查交的，编译过）：`module Step (n : ℕ)` 里 `ℓ = tw (suc n)`，`k = tw n`，`child c = k ⊕ ↑ k c`，`g c` 是孩子 c 处的 Ω 树，`feed c` 是 `g c` 经路径 `ink self` 折到槽位层 k 的输出，`chain = iter feed zero`（实际回灌链，住在槽位层 `tw n` 上），`out c` 是 `g c` 折到第 0 层的输出（`baseᴱ (suc n)`、`betaᴱ (suc n)` 是终点第 n+1 支实际继承的底与起点）；`branch-upper`：每个链点的输出不高于第 n+1 支；`step : Kᴱ n → Tail → Kᴱ (suc n)`，`Tail = (m : ℕ) → Σ ℕ λ q → (h : HC (E.fsn (row (suc n)) (suc m))) → tree h ≼ readRW (proj₁ (out (chain q)))`。
- **第一个缺口**（`YiFRStep` 末尾，逐字）：
  ```agda
  FirstMissing = Σ ℕ λ q → (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1))
    → SI.E.tree h ≼ K.readRW (proj₁ (Step.out 2 (Step.chain 2 q)))
  ```
  主审用一个故意失败的等式让检查器展开了左边那一项（留档 `probes/Survey/Reports-2026-11-12/attachments/SelfCheck-SC4Row.agda.txt`）：`E.fsn (row 3) 1` 是 `E.ψ [] (E.fsT Ω_{Ω_Ω} (E.γT Ω_{Ω_Ω} [] 1)) ∷ []`，其中 Ω_{Ω_Ω} 写作 `E.ψ (E.ψ (E.ψ (E.ψ [] [] ∷ []) [] ∷ []) [] ∷ []) [] ∷ []`。这正是很早就卡住的 "K(2) 第 1 行"（`YiMTValue.K2-redᶻ`、`YiKQSuff.K2` 都停在这里）。
- **先验教训**（这几批编译的否定）：凡写成 "对一类对象全称成立" 的保持律都被否定了（`YiLLLeafNeg.noLeaf`、`YiSUNeg.no-step`、`YiGTIndexNeg.no-frame₂`、`YiMXNeg.¬Exit′` 等）；正面结果都是对实际对象的直接构造（`YiS1Low.folded¹`、`YiCNTw1.leaf-tw1`、`YiPJQ.qω+1`）。本路只对实际的链点与实际的那一项陈述，不写全域律。
- **上一批之后的事实**（主审复核过）：
  - 每一站的关系推导连同出口证据都可由该站的值下界经语义反射得到（`YiS2Low.station→certificate`），关系路线与值路线合成一条；终点只差从第 3 站起的站值下界。
  - 目标项 `E.fsn (row 3) 1` 展开为 ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}})（YiMS 回报），已知不低于 ψ₀(Ω_{Ω_ω})（`YiFNTarget.lower`）；是标准形，G 集成员已实填（`YiLBStart`）。
  - 实际链点：第 2 个链点的输出不低于 ψ₀(Ω_Ω+1)（`YiMSValueRef.bound`，沿第 0 支展开 22 次；再推到 ψ₀(Ω_Ω+2) 时 8G 堆耗尽）；一切链点的输出都严格低于第 3 支（`YiFNUpper.strict-upper`，相对上界，不是记号上界）；各链点孩子在非零层上的关系对一切链点成立（`YiLBActual.child-gamma`、`g-gamma`）；第 2 站的链在塔第 1 项那一层上的关系（`YiS2Chain.actual-chain`）。
  - 文献式不变量（`YiLBInv`）：`Inv q`（第 q 个链点的输出支配一切参数为标准形、G 集低于参数、参数不超过第 q 个参数的 ψ₀ 项），`inv0` 成立，`step→first : InvStep → FirstMissing`。
  - **三路停在同一条具体的闭项不等式上**（YiLB 回报第 4 节，逐字）：
    ```agda
    missing-child-low₁ :
      (h : SI.E.HC (E.fsn (Keel⁻.row GI.keelᴱ 3) 1)) →
      SI.E.tree h ≼ K.readRW (proj₁
        (TB.ψ h₁ (proj₂ (P.Ok-tw 3) c₁) (MT.rbᶻ h₁)
          (λ i u → GI.baseᴱ 3 i (P.inc c₁ u))
          B.zero (P.z≤ h₁) (GI.betaᴱ 3)
          (proj₁ (O.Ωt h₁))))
    -- c₁ = FR.Step.chain 2 1，h₁ = FR.Step.child 2 c₁ = tw 2 ⊕ ↑ (tw 2) c₁（Ω 形状）
    ```
    `YiLBActual.out-child 1` 把右边与 `Step.out 2 (Step.chain 2 1)` 逐字接上；有了它，`FirstMissing` 以链点 1 为见证成立。
- **上一批之后的新事实**（主审复核过）：`YiUPBase.base-form : ∀ i u → proj₁ (baseᴱ 3 i (inc c₁ u)) ≡ ((Ωt i + ι δ0) + ι δ1) + ι δ2`（`refl`，δ 取自标准底下的 `twᶻ`）：第 3 站链点 c₁ 的孩子折叠时拿到的底只是 Ω 树加三段固定的可数尾项，不随实际回灌链增长。原因（纸面审计 YiPA，回报 `probes/Survey/Reports-2026-11-12/YiPA.md`）：塔第 3 项根上最小比较表的（源孩子 `zero`，目标孩子 c₁）一项是 `lo (h zero) (h c₁)`，而 `lo (nd _ _) b = nothing`（`YiMTTab` 第 29–41 行），于是走退路行，把底与起点重置为标准底 `B₀` 与 `Ωt zero`。能否达到目标、定义是否丢值都未判定（YiFN、YiUP 均未得到独立的记号上界）。
- **性能**（作者 2026-11-15："内存等性能问题参考手册"）：具体闭项先封进 `opaque`、引理在变量上陈述再实例化（Bedrock `<Bedrock>/dev/cubical-agda-performance.md` 的 C-9、C-10、S-1、S-3），先用 `--profile=definitions` 或二分定位（Q-1、Q-23）；手册 `probes/Survey/EBOHandbook.md` 4.2 节第 1 至 8 条。
- **第 3 站的工程层已完成**（YiE4，主审复核过，回报 `probes/Survey/Reports-2026-11-12/YiE4.md`）：`YiE4Base`、`YiE4Objects`（第 3 站一切作函数用的折叠在出生处封进 `opaque` 并导出定义等式）、`YiE4Inner`/`YiE4ParamInner`（内层链与整行的部分和极限等式，`YiE4Cut20.first-row`）、`YiE4Frame.at-one`、`YiE4ParamFrame.Missing`（对表 `r : Rb Λ` 参数化的那一条值不等式：`Missing = (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ (Q.collapse D.ctx D.β))`）、`YiE4Instances`（最小比较表与空表的实例）、`YiE4Default`（`OriginalAtOne = Bound LS.target (FR.Step.out 2 (FR.Step.chain 2 1))`，`from-original`/`to-original` 与封装的 `Missing` 互推，`first-at-one` 以它为参数给出 `FirstMissing`）。**在这个框架里做**，不要重写具体对象；同义对照：直接写 8G 耗尽，封装加变量化 16 秒约 1.5G（手册 `probes/Survey/EBOHandbook.md` 4.6 节末）。
- **目标项与它的基本列**：`LS.target`（`YiLBStart`）即 ψ₀(Ω_{Ω_A})，A = ψ₀(Ω_Ω)；标准形与 G 集成员已实填。纸面审计（YiPA，回报 `YiPA.md` 第 3.3、5 节，判断档）：记 ρ₀ = 1，ρₙ₊₁ = ψ₀(Ω_{ρₙ})，则 A[n] = ρₙ₊₁，目标的基本列 T[n] = ψ₀(Ω_{Ω_{ρₙ₊₁}})；建议的骨架：把输出写成内层序列的累计极限 P_M = G(0) + G(s 0) + … + G(sᴹ 0)，对每个 n 找 M(n) 使 T[n] 不高于 P_M(n) 的读回，再经累计极限出口得到不等式；不要假设同一下标 n 对应同一内链点。
- **可用的关系与值工具**：`YiLBInv`（文献式不变量 `Inv`、`inv0`、`step→first`）、`YiLBActual.child-gamma`/`g-gamma`（孩子在非零层上的关系，对一切链点）、`YiS2Chain.actual-chain`（第 2 站的链在塔第 1 项那一层上的关系）、`YiS2Low.station→certificate` 与 `YiKCSem.sem→M⁰`（值不等式与关系推导互推）、`YiMSValue`/`YiMSValueRef`（沿分支的值界，只作局部工具）、`YiNDAccept`（新终点上经 F2 对照关系的做法）。
- **里程碑**（YiAZ，主审复核过，`YiAZLocal`）：第 3 站缺口里的目标基本列第 0 项 T[0] 往下展开，第 m 项是 `S m = ψ₀(Ω_{Ω_m})`（`S-form`）；`S-below-T0 : ∀ m (h : HC (S m)) (h₀ : HC (T 0)) → tree h ≼ tree h₀`；`S 0`、`S 1` 就是第 1、2 站的行（`S0`、`S1`），实际链点上的值界由现有结论得到（`S0-low`、`S1-low`）。所以第一个真正新的里程碑是 **`S 2` = ψ₀(Ω_{Ω₂})**。它高于项目历史上验收过的一切值：现主线的无条件值 ψ₀(Ω_Ω+ψ₁(Ω_ω))，旧差树主线（`probes/OCF/Align/EmbVVInstO2`，行结构取自记号）的 ψ₀(Ω_{Ω·ω²})。
- **目标**：干净对象（`YiUTTwo`、`YiUTTwoLocal`）上里程碑基本列的第 1 项 `YiC0Next.RowOneAtTwo = K.M⁰ row₁ (UL.P 2)`（`row₁ = ψ₀(Ω_{slot})`，`slot` 为 ψ₁(Ω_Ω)）。第 0 项已成立（`YiC0Accept.first-row`）。**第 1 项尚未证出。**
- **已编译的零件**（主审 8G 冷编复核过）：
  - `YiC0Next`：`NextSlot = H.M 1 slot (Inner.chain 2)`、`ChildSlot`、`chain2-child`、`child→slot`。`YiC1Slot`：`kept`、`branch`、`actual-below`、`BranchNeed = ∀ η d → K.M⁰ η d → H.M 1 (E.fsT N.slot η) (branch d)`（未构造）。`YiRXOmegaHead.omega-head`（分支关系 ⇒ Ω 头的关系）。关系沿 ⊴ 向上：`YiKVRel`、`YiHCRel` 里的 `m⊴`（第 1 层 `YiCLFam` 里的先检索）。
  - 最小实例 `YiBVSmall`（`layer = nd (sΩ zero) child`，`child d = two ⊕ ↑ zero (suc d)`，`MinimalGoal`）。**`YiQLRead`**：`Need η d = R.At (Target η) (S.child d) (S.lower d)`，`formula : Target η ≡ ψ₁(Ω_η)`；`zero`、`limit`、`weak` 已填；`Step = ∀ {η d} → E.cof η ≡ E.c1 → K.M⁰ (E.pred η) d → Need (E.pred η) d → Need η (B.suc d)`（**未填**）；`leaf : Step → ∀ η d → K.M⁰ η d → Need η d`，`minimal-from : Step → S.MinimalGoal`。`YiQLSuccessor`：后继孩子上的内层链（`feed`、`chain`、`part`、`out`、`row`），`first`（归纳假设给第 0 行），`Rows`、`from-rows`，`SecondRow`（未填）。`YiQLCheck.step-at-one`（有限情形的后继一步）。
  - **F2 一侧**：`YiPVF2.lower-one`（F2 块 `YiLSFold` 对一切由零、后继、ℕ 极限生成的层号 `V.NL ℓ` 成立，目标第 1 层，结论是 `R.Rel one (L.ψ p … (L.Ω κ)) (…)`，参照为 `OCF.Align.Level` 序数）；`YiPVOne.back : ∀ {t x x′} → RelT K.one one′ x x′ → AF.M 1 t x′ → H.M 1 t x`（第 1 层 F2 关系搬到现主线）；`YiPVZero`；`YiPVSmall.one-child`（有限层号 4 的孩子上试搬成功，用的是 F2 有限层号的 `YiANLv.Th.tcLeaf`）。
  - `YiNIIface.Law`、`YiNISuff.first-at-two : ∀ f → Law f → NextCover f → N.RowOneAtTwo`、`known-no-next`。
  - 摆脱侧：`YiTZLocal`（`Cover`）、`YiTZAccept.from-cover`、`YiTQChain`、`YiTYLocal`（`ChainAdvance n = ChainItem n → ChainItem (suc n)`、`CumAdvance`，未填）、`YiTYPath`、`YiTYNoDirect.no-direct`（只否定直接用第一位置证据调 mono 的证法）。
- **已有的否定，不要绕回去**：`YiLLLeafNeg.noLeaf`（反例含 Ω 孩子，不碰可数层号）；一般的跨层单调 `YiMXNote.¬Mono`。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

## 背景（另见上面的共同陈述）
- **桥 (i)，参照一侧**：`YiPVF2.lower-one` 的结论是 `R.Rel one`（`YiLSRel`，参照为 `OCF.Align.Level` 的序数 `L.ψ p … (L.Ω κ)`）；`YiPVOne.back` 要的是 `AF.M 1 t x′`（参照为 EboLean 项）。先检索已有的第 0 层同类桥（BTBO 验收里 EboLean 树与 `Align.Level` 序数的比较，如 `YiC0Connect` 用到的 `RT.tree-≼`、`XR.row₂-btbo`，以及 `CS.sem→M⁰`），再看第 1 层要什么。
- **桥 (ii)，层号对应**：一般孩子 `S.child d = two ⊕ ↑ zero (suc d)`（d 是第 0 层树）与 F2 的 `V.NL` 层号之间的 `RelE`（`YiBRRel`；`YiPVSmall.child-E` 是 d 为有限时的实例），以及 `Corr κ ℓ` 的对应。

## 要做的（按序）
0. **最小检查**：在 `YiPVSmall` 的孩子（有限层号 4）上改用 `lower-one`（而不是有限层号的 `tcLeaf`）走完整条管道：`lower-one` → 桥 (i) → `back`。确认两座桥的陈述类型。不成立就停下回报。
1. **桥 (i)**：`R.Rel one` 到 `AF.M 1` 的桥（只对 `lower-one` 给出的参照形状，不写一般的）。
2. **桥 (ii)**：对一切 d 的 `RelE (S.child d) …` 与 `Corr`。
3. **合成**：对一切 d 得到 `YiQLRead.Need η d` 所需的关系（或直接得到 `MinimalGoal`），绕开 `Step`。挡住就交第一个挡住的地方。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

## 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiFB`（模块名 `OCF.Lean.YiFB…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiSQ`、`YiWX`、`YiTN`）。验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径，写 `<实验目录>`）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <标准库的 .agda-lib 路径>
  <cubical 的 .agda-lib 路径>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - **堆上限 8G**：同时最多五路在编译，机器共 64G。若某个文件确实要超过 8G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
  - 不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`，是就是库文件的问题）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
  - 堆墙：不要在具体推导上直接比较两个读回；具体参照树放 `opaque`；经非单射的头求解的隐式参数显式写出。
- 不在你的临时目录与你前缀的新文件之外删除或移动任何东西，不 `pkill`，不装包，不提交，不推送。不改 `probes/README.md`、`probes/LOG.md`、台账与留档（这些由主审更新；回报交给作者转回）。
- 查签名用检索（`grep`），不整篇读大文件。
- **停下的条件（本路特别规定，覆盖上面的通用写法）**：退出 251 时不原样重跑（Bedrock H-6），先按 C-9、C-10、S-1 改形状并定位；改过形状后在同一上限下仍撞墙才停，附二分或 profile 数据；要加堆在回报里写明，由主审安排。同一处两次重新设计仍过不了检查器也停。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0。

## 回报格式（回报交给作者转回主审）
1. 判决：先说对纲领与目标意味着什么；第 0 步；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码、内存（`+RTS -s` 的数）。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。
