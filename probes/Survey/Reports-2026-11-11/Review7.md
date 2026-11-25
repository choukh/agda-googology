# 第七次独立审查：BTBO 是下界的更省证法：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-11 14:37 至 15:23 |
| 工具调用 / agda 编译 (粗数) | 57 / 4 |
| token (usage 字段，按消息去重) | 输出 281924；新写入缓存的输入 767459；读缓存的输入 14043733；其余输入 106 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `YiBtbo` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 第十二批两路返回并复核; BTBO 是下界, 无前提 (主审)” 一节 |
| 主审复核后的一句结论 | BTBO 是下界，无前提：审查者的两个临时文件由主审移入 YiBtboV2、YiBtboLower 并冷编复核，退出码 0；七条更正都接受 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一位独立审查者. 任务是 **判断 "BTBO 的参照是下一站闭项 `T⁺` 的下界" 有没有更省的整体证法**. 你不产出仓库文件, 只交一份回报; 需要时可以在你的临时目录里做最小的编译实验 (纯 `.agda`). 主审 (派你的会话) 会复核你的实验. 全程用中文.

#### 背景 (只给事实, 不给结论)

- 作者 2026-11-11 定的短期目标: 一个闭项, 读法超过 BTBO, 值不低于 BTBO, 所在的块里塔与 Λ 合法, 定义前三层 500 行以下. 作者同日补充: "只要证明 'BTBO是下界' 即可" (不要求上界, 不要求同值).
- 现状: 闭项 `T⁺` 合法, 连同塔与 Λ 的合法性 475 行. 值: `T⁺` 不低于参照的 ψ₀(Ω_ω); 主线闭项 `T₃` 不低于参照对角链的第 2 项. "BTBO 的参照 ≼ 读回的 `T⁺`" 有好几条条件定理, 前提都没有证. 为这一站写的验收代码已超过 5000 行 (按文件粗数).

#### 次序 (这是审查的条件, 请严格遵守)

1. **先读规则与对象的定义, 写下你自己的看法 (存到你的临时目录里的 `preview.txt`), 再读别人的结论.**
   - `AGENTS.md` 全篇 (纲领, 中间站给界, 量化域先取读回域, 结论的写法).
   - 被验收的对象 (都在 `probes/OCF/Lean/`): `YiLeanCore.lagda.md` (块), `YiLeanFold.lagda.md` (折叠), `YiLeanTw3.lagda.md` (主线闭项 `T₃`: 链 `pts` 从 `top` 起, 下一点是这一点加上它的折叠值), `YiNextTop.lagda.md` (下一站的闭项 `T⁺`, 第 0 项是 `T₃`). 读值用的 `YiLeanAccFin.lagda.md` 的 `read`.
   - 参照: `probes/OCF/Align/Level.lagda.md` (只看 `Ordᶜ`, `Ordᴵ`, `ψ`, `ψ⁰` 的定义, `Ω`, `toLevel`, `_⊑ᴵ_`, `Ψ⁰-mono`), `probes/OCF/Align/Diagonal.lagda.md` (不累加的 BTBO 对角线 `γ`, `L`, `BTBOᴵ`), `src/OCF/BTBO.lagda.md` 第 770 到 1110 行 (已发布的 BTBO: `cumsum`, `ordᴰ`, `ψⁿ`, `BTBO`), `probes/OCF/Align/BTBOFull.lagda.md` 的 `BTBO≈` 的陈述 (两个 BTBO 同值).
2. **再读已编译的定理陈述 (只读陈述, 不读回报).** 都在 `probes/OCF/Lean/` 或 `probes/OCF/Align/`, 用检索看签名:
   - 下界与链: `YiLeanValFold.lower-any`, `YiLeanValFin` (`T₃-own`, `T₃-Ωω`, `κ`, `ChainP`, `btbo-p`, `FromVM`, `btbo-vm`), `YiChainOne.chainP₁`, `YiChainCond.T₃-γ₂`, `YiNextValFin` (`T₃≅`, `btbo⁺-from-main`), `YiNextAcc.T₃≼T⁺`.
   - 值单调: `YiMonoVM` (`VMᴸ`, `EmbV`), `YiVmConExact` (`≼ˣ`, `≼ᵖ`, `VMᵖ`), `YiEmb2.VMˣ`, `YiLowChain` (`VMᶜ`, `FromVMᶜ.btbo⁺`), `YiLowPos.vm-ω²`.
   - 否定: `YiMonoBreak.no-L`, `YiLeanValBreak.no-L`, `YiZeroAcc.nz-any`, `YiVmConLPO.tri→LPO`, `YiVmNegSeg.embVᴰ→LPO`, `YiVmNegIrr.vm¬¬→MP`, `YiLowNeg.embVˢ→LPO`, `YiLowNeg.embV→LPO`, `YiUBNeg.no-UB`, `YiDiagAccNeg.no-γ₂`.
   - 归约: `YiPEKey.btbo-FS⁺` (前提 `FUNC`, `KEYsuc`, `SpineT`), `YiUBP2.btbo-str`, `YiSucWire.btbo⁺-str`, `YiEmb2.btbo-cond₂`.
   - 设计候选: `YiDiagTw3` (链不累加的闭项), `YiDiagAcc.read-pt1` (它第 1 步与参照结构互模拟), `YiZeroAccP.readΨ`.
3. **最后才读回报与日志**: `probes/Survey/Reports-2026-11-11/README.md` 的第四批以后各批, 与 `probes/Survey/IdeaLedger.md` 的 §3, §4.

#### 要回答的问题

1. **更省的整体证法.** 有没有一条证 "BTBO 的参照 ≼ 读回的 `T⁺`" 的路, 比现有各条归约都省. 至少评估这几类 (都要自己判断, 不要照搬):
   - (a) 换参照: 例如用已发布的 BTBO (累加在 `ordᴰ` 里) 加 `BTBO≈`; 或在参照框架里造一条与主线同样累加的对角线, 一次性证它与不累加的同值 (参照框架内的工具较多), 再证主线不低于它.
   - (b) 小改树的设计, 让下界在结构上直接成立 (结构可比 `⊑ᴵ` 加 `Ψ⁰-mono`): 哪些设计选择 (链累加并把上一点放在叶上, ω 倍从第 1 项起, 极限层号的顶取部分和) 挡住了结构可比, 它们是不是被合法性逼出的. 注意: 作者对最终定义有 "不改前 3 层只为验收方便" 的规则 (AGENTS 第 4 层一条), 改设计要有树侧自身的理由, 或者明说是新的主线候选.
   - (c) 只对链点的结构办法 (现有的 `FUNC`, `KEYsuc`, `SpineT`) 还是在 ψ⁰ 层直接对链证值单调.
   - (d) 你发现的别的路.
   对每一类: 第一个障碍在哪, 规模的粗估 (标明是判断), 与已编译的否定是否冲突.
2. **哪些已有的工作可以复用, 哪些是死路.** 按已编译的定理说, 不按回报的措辞.
3. **最便宜的决定性实验.** 一两个能在一个下午编译出来, 能判定你推荐的那条路可行与否的实验; 若你已经在临时目录里做了, 交出来.
4. **主审与各路的结论里, 哪些超出了定理支持的范围.**

#### 规则

- 不改任何仓库文件, 不新建仓库文件. 实验只放你的临时目录 `<实验目录>/agents/review7`, 用纯 `.agda`, 选项行 `{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns #-}` (要导入仓库模块就得写这几个). 编译: 在仓库根目录 `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes -i <你的临时目录> <你的临时目录>/<文件>.agda > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`; 同时只跑一个 agda, 堆上限 6G; 不用 `--ignore-interfaces`; 不删任何仓库里的 `.agdai`. 不许 `postulate`, 洞, `TERMINATING`, K, 函数外延 (作前提可以).
- 不在临时目录之外写文件, 不 `rm` 临时目录之外的东西, 不 `pkill`, 不装包, 不提交.
- **过程要求**: 每次回复都要有工具调用, 不要在一次回复里只思考; 读完定义后先把 `preview.txt` 写下来.

#### 回报格式 (只在回报里交一次)

1. 一句话结论与推荐.
2. 问题 1 到 4 的回答, 每条标明是编译事实 (写出文件与名字), 临时试验 (写出你的文件与退出码), 还是判断.
3. 与主审和各路不一致的地方 (表: 他们的说法, 你的说法, 依据).
4. 你没有读的, 只凭转述引用的.
不用 "只差", "自然" 一类形容.

## 回报原文

#### 1 一句话结论与推荐

有更省的整体证法，而且我已经在临时目录里编译通过（exit 0）：`D.BTBOᴵ ≼ NA.read NT.T⁺` 无前提成立；用 `BTBO≈` 换成已发表的 BTBO 也成立。证法不用 `FUNC`、`KEY`/`KEYsuc`、`SpineT`、`StrChain`、`ChainP`，也不用任何值单调的假设。新增验收代码共 333 行，其中约 60 行是已编译的 `V2` 的副本，另有注释和自检；前三层一行不改。

**推荐**：主审从头复核这两个文件，再决定是否以验收文件的身份放进 `probes/`。在跑的 `YiFunc` 那一路，对 "BTBO 是下界" 这个目标已经不需要，是否停下由作者定。

#### 2 问题 1 到 4

##### 问题 1：更省的整体证法（临时试验，已编译）

**文件**：
- `<实验目录>/agents/review7/R7V2.agda`（84 行，exit 0）
- `<实验目录>/agents/review7/R7Route.agda`（249 行，exit 0）

两个文件冷编译（仓库接口已缓存）共 10.7 秒，常驻峰值 1.78G。日志里只有 30 条 `UnsupportedIndexedMatch` 警告，仓库的库文件本来就关掉这一条；没有未解元、公设、洞、停机指示、函数外延。

**要点**：链上的不变量只取值序 `D.γ n ≼ read (co (pts m))`，每一步在 "累加规范化的层号" 上把值序换成前驱嵌入。"累加规范化的层号" 指 src 的 `ordᴰ`：每个极限换成部分和 `cumsum`，相邻项之间夹一个后继，所以有空位。主要陈述（照抄）：

```
V2′    : ∀ (x y : S.Ord₀) → St (tr₀ x) → Mono (tr₀ y) → tr₀ x ≼ tr₀ y → Eb (ordᴰ x) (ordᴰ y)
Fsuc   : ∀ a (l : Lgl zero a) → read (F a l) L.≺ read (F (G.suc a) l)
V3m    : ∀ η (l : Lgl zero η) → Σ (WT.Eb (ordᴰ (cp η)) (read (F η l))) (λ e → ∀ {c} (p : c B.< ordᴰ (cp η)) → L.𝟎 L.≺ WT.map e p)
emb    : ∀ n m → D.γ n ≼ read (co (pts m)) → PEmb (D.L n) (κ (suc m))
chainV : ∀ n → Σ ℕ (λ m → D.γ n ≼ read (co (pts m)))      -- 取 m = 2n
embT   : EmbTⁿ
btbo   : D.BTBOᴵ ≼ read T₃
btbo⁺  : D.BTBOᴵ ≼ NA.read NT.T⁺
src-btbo⁺ : tr₀ S.BTBO ≼ NA.read NT.T⁺
```

文件 §0 另有三条 `refl`：`D.γ ≡ N.γ`、`D.L ≡ N.L`、`D.BTBOᴵ ≡ N.BTBOᴵ`（`YiBtValBT.D` 就是 `NoCumsum.D`）。

**`emb` 的四段**，全是 `PEmb-∘`：
1. `PW₃ (V1 (SV-L n))`：参照的层号嵌进它自己的累加规范化。已编译，`BTBOFullV1`。
2. `PW₁ (V2′ …)`：规范化的层号之间，由值序给出嵌入。`V2` 已编译；`V2′` 只把目标一侧的 `St` 放宽成 `Mono`（极限逐项不降）。合法的第 0 层树由 `cp⊑` 直接满足 `Mono`，所以不必证主线链点的严格性。
3. `PW₂ … (V3m η)`：链点 η 的规范化层号嵌进主线折叠值 `read (F η)` 的字面前驱。这是新的，只谈主线：
   - 后继情形用 `Fsuc`；
   - 极限情形用已编译的 `Blk.Lim`。主线在极限层号上的顶取部分和，第 n 块恰好是 `read (psum n) + (…)`，与 `cumsum` 的分块逐块对上。块顶放在 `read (psum (n+1))`，下一块的像非零，所以放得下。
   - `V3m` 对一切合法 η 成立，不限于链点。
4. `shift-κ m`：已编译，`YiPEStep`。

然后用 `Ψ-emb` 得到值，再接 `lower-read` 与 `plus≽` 推进不变量，最后接 `YiPEBase.btbo-embⁿ` 与 `btbo-emb⁺`。

**`Fsuc` 的证法**：
- `topfp`：`G.top` 是任何 `Ψ m V x G.top` 的第一位置；
- `succfp`：`succ zero (Ψ X)` 是 `Ψ (X + top)` 的第一位置；
- 再用 `lead0`、`Z-top`、`cp⊑`、`Ψ-cp`、`add-cp`。

**四类的评估**：
- **(a) 换参照**
  - 换成已发表的 BTBO：编译事实，`src-btbo⁺`，多一行。
  - 在参照框架里造一条累加的对角线再比：判断。第一个障碍与 `FUNC` 同类，要沿嵌入搬运折叠。没有做，已无必要。
  - 真正起作用的是这一类的变体：参照框架里的层号规范化（`BTBOFull` 的 `V1`/`V2`/`Blk`），这些工具早已编译。
- **(b) 小改设计**：不需要（编译事实：现有 `T₃`/`T⁺` 上直接成立）。
  - 部分和非但不挡，反而是 `V3m` 极限情形用到的结构。
  - 链累加由 `shift-κ` 处理。
  - ω 倍从 y 起与这条证法无关。
  - 结构可比（`⊑ᴵ`）仍被 `no-L` 否定，但这条路不用它。
- **(c) `FUNC`/`KEYsuc`/`SpineT`，以及在 ψ⁰ 层直接证值单调**：对本目标不再需要。
  - 判断，未编译：一般的 `FUNC` 难在保 `≅ᴵ` 的一致性。照 P 搬运出来的映射，在 P 不把 0 送到 ≅0 时会不一致；平移嵌入就是这样。
- **(d)**：就是上面这条。规模是编译事实：333 行。

**与已编译的否定不冲突（判断，附机制）**：
- `embVˢ→LPO`/`embV→LPO` 否定的是 "由值序在同等高度的原层号 `toLevel x → toLevel y` 之间造嵌入"。这里的嵌入落在规范化层号（`V2`），或者落到下一个链点 `κ (suc m)`（下标高一格，有余量）。
- `no-L`：这条路不用 `⊑ᴵ`。
- `tri→LPO`、`cplᵖ→LPO`：不用 `Tri`，也不用完备性。
- `vm¬¬→MP`：`V2′` 读推导（`≼lim⁻` 取下标）。
- `no-UB` 是上界，这里不涉及。

##### 问题 2：可复用的与死路（按编译的名字）

**本证法用到的（编译事实）**：
- `YiLeanValFold.lower-any`（经 `YiLeanValFin.lower-read`）；`YiLeanValFin.{κ, HS-read, cp⊑}`
- `YiLeanAccFin.{read, read-plus, plus≽}`
- `YiLeanLegal.{dnLc, add-cp, Ψ-cp, Ψn-dn, ΨN-dn}`
- `YiFlatChain.{Z-top, lead0}`
- `YiPEStep.{Fκ, shift-κ}`；`YiPEBase.{EmbTⁿ, btbo-embⁿ, btbo-emb⁺}`（内含 `T₃-own`、`YiNextValFin.T₃≅`、`YiNextAcc.T₃≼T⁺`）
- `YiMonoEmb.PEmb-∘`
- `BTBOFullEmb.{PEmb, Ψ-emb}`
- `BTBOFullV1.{V1, PW₁, PW₂, PW₃}`
- `BTBOFullEb.{Blocks, Blk, inv}`，以及 `V2`（副本）
- `BTBOFullV3.{𝕋₀, bkᴵ, ≺→⊑₀, add-left}`
- `BTBOFullLv.SV-L`
- `BTBOFull.{St-bk, bk≅γ, BTBO≈}`
- `BTBOValNeg.add-≺`；`BTBOFullQ.{<ᴰ-irrefl, clash-lt}`

**对本目标不再需要的条件定理**（前提仍未证，但不是死路，也不否定）：
- `YiPEKey.btbo-FS⁺`、`YiPEStep.btbo-FK`
- `YiUBP2.btbo-str`、`YiSucWire.btbo⁺-str`
- `YiEmb2.btbo-cond₂`、`YiChainCond.btbo-cond`
- `YiLeanValFin.btbo-p`/`btbo-vm`
- `YiLowChain.FromVMᶜ`、`YiNextValFin.btbo⁺-from-main`

**有编译否定的证法（死路，范围以各定理的陈述为准）**：
- 链上的 `⊑ᴵ` 加 `Ψ⁰-mono`：三处 `no-L`、`nz-any`
- 由值序在原层号上造嵌入：`embVᴰ→LPO`、`embVˢ→LPO`、`embV→LPO`
- `≼ˣ`/`≼ᵖ` 的完备性与 `Tri`：`YiVmConLPO`
- 不读推导的值单调：`vm¬¬→MP`
- 一切合法层号上的上界：`no-UB`
- 不累加候选的第 2 步结构互模拟：`no-γ₂`
- 字面第一位置之下逐项的写法：`no-termwise`

##### 问题 3：最便宜的决定性实验

已经做完，就是上面两个文件。

复核办法：从仓库根目录，用同样的命令编译 `R7Route.agda`（它会连带检查 `R7V2.agda`）。接口是我本地生成的，复核时可删掉我目录里的 `.agdai` 再编。然后核对 `btbo⁺` 与 `src-btbo⁺` 的类型，以及导入表（全是仓库里 `--safe` 的模块）。

我只写了自己目录里的文件；新出现的 `probes/_build/.../YiFunc*.agdai` 不是我写的。

##### 问题 4：超出定理支持的说法

见下表。

#### 3 与主审和各路不一致的地方

| 他们的说法 | 我的说法 | 依据 |
|---|---|---|
| 台账 V8："换成累加的参照……搁下，那边的机制要目标在每个极限处都累加，树只在根链累加" | 机制可用。`V2` 的目标取链点的规范化 `ordᴰ (cp η)`；主线折叠在每个极限层号上本来就取部分和，`V3m` 正是靠它把规范化层号嵌进 `read (F η)` | 编译：`R7Route.V3m`、`emb` |
| 台账 V8 与回报总表："两个参照是否同一个没有核对" | 是同一个，定义性相等 | 编译：`R7Route` §0 三条 `refl` |
| 第十一、十二批的走向：BTBO 下界归约到 `FUNC`、`KEYsuc`、`SpineT`，再派 `FUNC` | 这些是充分条件，不是必要的；本目标不需要它们 | 编译：`btbo⁺` 不依赖它们 |
| 台账 V6 把 `ChainP` 称作 "主线上缺的那一条" | 它只是充分条件之一（`btbo-p`）；我的证法不经过它 | 编译：同上 |
| 台账 C1："值上要逐例的吸收" | 不需要逐例吸收；左加数由平移嵌入 `shift-κ` 处理 | 编译：`emb` |
| 台账 V7："以前驱嵌入为底在左极限碰一致性" | 先把源换成规范化的 `Ordᴰ`（字面序），左极限的一致性由 `Blk` 的分块直接得到，不必比较各项的推导 | 编译：`V3m` 极限情形 |
| 第十一批 YiLow 的下一步只列 "ψ⁰ 层直接证 Crux" 与 "链点的结构嵌入" | 漏了 "规范化层号上的值单调（`V2`）加主线一侧的 `V3m`" 这一条 | 编译 |

#### 4 没有读的与只凭转述引用的

**没有读**：
- 各路的单篇回报（`Reports-2026-11-11/*.md` 除 `README.md` 以外）
- `LOG.md`、`RouteReview3.md`、`RR4`、`RR6`、`Retro`、`EBOHandbook.md`
- `BTBOFullLe`、`BTBOFullV1` 中 `V1` 的证明体，`Uniform`
- `YiPEStair`、`YiEmb2Le`、`YiFlat*`（只看了 `YiFlatChain` 的两条签名）、`YiSuc*`、`YiUB*`、`YiOver*`、`YiFunc*` 的内容
- 回报 `README` 第一到第三批的表

**只凭陈述或文首引用**：`V1`、`V2`、`Blk`、`SV-L`、`St-bk`、`bk≅γ`、`BTBO≈`、`shift-κ`、`btbo-emb⁺`、`T₃≅`、`T₃≼T⁺`、`lower-any` 的证法。它们都作为已编译的依赖参与了我的编译。

我自己的预览写在 `<实验目录>/agents/review7/preview.txt`。其中 "SL 要从头写、800 到 2000 行" 的估计，在读到 `lower-any` 已编译后作废；"不可省的核心是一条结构嵌入值的折叠引理" 的判断，被 `V2` 加 `V3m` 推翻。
