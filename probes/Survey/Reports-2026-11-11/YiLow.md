# 只用下界：严格的树上的值单调 (YiLow)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-11 13:47 至 14:30 |
| 工具调用 / agda 编译 (粗数) | 46 / 10 |
| token (usage 字段，按消息去重) | 输出 263737；新写入缓存的输入 1048565；读缓存的输入 10695126；其余输入 82 |
| 写过的仓库文件 | `YiLowBase.lagda.md`, `YiLowChain.lagda.md`, `YiLowNeg.lagda.md`, `YiLowPos.lagda.md` |
| 文件前缀 | `YiLow` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 严格树上的值单调一路返回并复核; 第十一批的合读 (主审)” 一节 |
| 主审复核后的一句结论 | 这条证法被编译否定：严格树上值序推出前驱嵌入推出 LPO，连带一般的版本；ω² 以下成立；只在链上的值单调推出 BTBO 下界（条件）；四件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 任务是 **只用下界证明 "BTBO 的参照 ≼ 主线闭项"**, 不要求任何上界或两个方向的对上. 作者 2026-11-11 的原话: "只要证明 'BTBO是下界' 即可". 你的路线: 证参照框架上的值单调在 "严格的树" 上成立, 再用已有的链归纳. 另有一路 (前缀 `YiPE`) 同时用另一种办法 (沿链造前驱嵌入) 攻同一个目标, 互不依赖. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 "量化域先取带证据的读回域", "第 4 层不反过来改前 3 层", Agda 一节 (选项, 文字预算, 退出码, 堆; 函数外延只准作前提), "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 与 §5.4.
3. **回报原文**: `probes/Survey/Reports-2026-11-11/YiVmNeg.md` (全读; §5 末有一条证明思路: 严格的树里借下一项的推导把前一段的像压在一个前驱之下, 再逐段延拓; 也列了哪些写法推出全知原则), `YiVmCon.md` (保值嵌入, 定义域 `≼ˣ`/`≼ᵖ`, 以及为什么 "保值" 在一般情形要 LPO), `YiMono.md` (前驱嵌入 `PEmb` 的工具与左极限的一致性问题).
4. 代码 (都已定稿, 可以导入, 不许编辑):
   - **链归纳 (已有)**: `probes/OCF/Lean/YiLeanValFin.lagda.md` (模块 `FromVM`: `chainV : ∀ n → D.γ n ≼ read (co (pts n))`, `mono`; `btbo-vm : VMᴸ → D.BTBOᴵ ≼ read T₃`, 用的只是值单调加已有的下界 `lower-read`, 不要任何上界). 你要做的是把 `VMᴸ` 换成一个只对严格的树陈述, 能证出来的版本, 并说明链上出现的对都是严格的.
   - **陈述**: `probes/OCF/Align/YiMonoVM.lagda.md` (`VMᴸ`, `EmbV`, `embV→vm`).
   - **前驱嵌入**: `probes/OCF/Align/BTBOFullEmb.lagda.md` (`PEmb`: `map`, `bnd`, `mono`, `coh`; `Ψ-emb : PEmb a b → ψ⁰ (Ω a) ≼ ψ⁰ (Ω b)`), `probes/OCF/Align/YiMonoEmb.lagda.md` (`PEmb-⊑`, `PEmb-∘`, `PEmb-limʳ`, `PEmb-suc`, `PEmb-limˡ`: 左极限的拼接要各项嵌入在公共前驱上一致).
   - **已知的边界 (不要撞上)**: `probes/OCF/Align/YiVmNegSeg.lagda.md` (保初始段的嵌入推出 LPO, 只限严格的树也一样: `embVᴰˢ→LPO`), `YiVmNegIrr.lagda.md` (不读推导推出 Markov 原则), `YiVmConLPO.lagda.md` (把推导改写成保值的推出 LPO), `probes/OCF/Lean/YiChainNegAdd.lagda.md` (`Strict` 的定义; 严格树上 `≼ˣ` 完备推出 LPO). 你的嵌入**不要求保值, 不要求保初始段**, 并且要读值序推导里的数据.
   - 可用的: `probes/OCF/Lean/YiFlatChain.lagda.md` (`X≺ : ∀ n → read (co (pts n)) L.≺ read (co (pts (suc n)))`, `κ≺`), `YiSucGood.lagda.md` (`good-read`: 合法的读回是好树), `YiOverRef.lagda.md` (`≤ₚ`, `mono⁰`), `YiChainNegAdd.lagda.md` (`Strict`).
   - 参照: `OCF.Align.Level` (`toLevel`, `toLevel-⊑`, `toLevel-≺`, `HS`, `_≺ᴵ_`, `_≅ᴵ_`, `<ᴵ-dec`), `OCF.Align.Value`, `OCF.Align.YiBtValBT` 的 `module D`.
   查签名用检索, 大文件不要整篇读.

#### 1 要交的, 分步; 每做成一步先交

1. **严格的树上的前驱嵌入.** 选一个 "严格" 的谓词 S (例如极限处相邻两项值上严格: `L.suc (f n) ≼ f (suc n)`, 或结构上 `f n L.≺ f (suc n)`, 递归到子树), 证
   ```agda
   EmbVˢ : ∀ x hx y hy → S x → S y → x ≼ y → PEmb (L.toLevel x hx) (L.toLevel y hy)
   ```
   从而 `VMˢ` (同样前提, 结论是 `L.ψ⁰ (L.Ω (toLevel x hx)) ≼ L.ψ⁰ (L.Ω (toLevel y hy))`, 经 `Ψ-emb`). 难处在左极限 (`l≼`): 各项的嵌入互不相关. 思路 (否定路的判断, 未验证): 严格时, 下一项的推导 `f n ≼ f (suc n)` 一类的数据可以把第 n 段的像压在 y 的某个前驱之下, 再从那里接着嵌第 n+1 段; 要的大概是 "从 a 起的一段嵌进从 b 起的一段" 的相对版本 (例如 `PEmb` 对 "加上一段" 的平移). 先在最小的实例上做: x 有限; x = ω; x = ω+1 对任意严格的 y.
2. **链上出现的对都是严格的.** `S (D.γ n)` 对一切 n (参照的对角链); `S (read (co (pts n)))` 对一切 n (主线的链点读回). 后者若做不到一切 n, 写清卡在哪个子树.
3. **无条件的 BTBO 下界.** 照 `FromVM` 写一个以 `VMˢ` 为工具的链归纳 (要的只是链上那些对的 `VMˢ`, 前提 S 由第 2 步给), 得 `D.BTBOᴵ ≼ read T₃` (主线, `YiLeanTw3.T₃`). 再接到下一站: 由 `probes/OCF/Lean/YiNextValFin.lagda.md` 的 `T₃≅ : MA.read MT.T₃ L.≅ NA.read NT.T₃` 与 `probes/OCF/Lean/YiNextAcc.lagda.md` 的 `T₃≼T⁺ : read T₃ ≼ read T⁺` 得 `D.BTBOᴵ ≼ NA.read NT.T⁺`. 两条都写成无前提的定理.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理, 另给不带它的最强结果); 堆到 6G 仍耗尽 (先按手册 §4.2). 若发现你的严格版本也推出某条全知原则, 写成编译的定理交回 (说明否定的是哪种写法). 做不成的部分写成带确切类型的模块参数, 说明前提在哪些实例上是定理. 没有编译的否定定理时只能写 "未走通".

#### 2 过程要求

- 读完上面的文件后尽快动手: 第一个文件 (哪怕只是 x 有限的情形) 在 20 分钟内写出并编译.
- 每写完一个文件就编译; 每次回复都要有工具调用, 不要在一次回复里只思考.

#### 3 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiLow` (模块名 `OCF.Lean.YiLow…`). 都是验收文件, 文首标 "验收文件"; 允许导入带记号闭包的 `OCF.Align.Value`, `OCF.Align.Level` 与旧验收文件. 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`. 同时在跑的另一路用前缀 `YiPE` (在 `probes/OCF/Lean/`), 不要动也不要依赖它的文件.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/low`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步; 一段话说对纲领与目标意味着什么 (`D.BTBOᴵ ≼ read T₃` 与对 `T⁺` 的同一条是无条件定理了没有).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型与它的可满足性.
4. 办法: 严格谓词怎么选的; 左极限的拼接怎么做的; 为什么不碰已知的那几条全知原则.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型; 它是不是在要求判定什么.
6. 偏离与事故.
强度写 ψ₀(Ω_x), 标明是定理还是读法; 下界不写成同值; 不用 "只差", "自然" 一类形容.

## 中途消息（主审发给这一路）

转录时间戳 2026-11-11 14:26 (UTC)：

主审通知 (你的任务不变, 多给已定稿可导入的工具与一条归约): 另一路 (`YiPE`) 已返回并经主审冷编复核, 四个文件定稿, 你可以导入 `OCF.Lean.YiPEBase`, `YiPEStep`, `YiPEStair`, `YiPEKey` (撤销简报里 "不要依赖 YiPE" 这一条).

它没有闭合目标, 但给了几样对你有用的 (都已编译):
- **阶梯粘接** `YiPEStair` 的模块 `Stair` 的 `stair : PEmb (L.lim f s) B`: 源是 `L.lim f s`, 每一步 `(f n ≅ᴵ f (suc n)) ⊎ (f n ≺ᴵ f (suc n))`; 目标逐块累加 `(t n ⊕ Y (suc n)) ≅ᴵ t (suc n)` 且 `t n ⊑ᴵ B`; 各块任给嵌入 `P n : PEmb (f n) (Y n)`. 结论: 粘成极限的嵌入, **不要求各块在公共前驱上一致** (一致性由逐块延拓 `glue`, `glue-ext` 给出). 这是你第 1 步左极限的一种现成办法 —— 条件是目标一侧能写成逐块累加.
- `PEmb-shift : ∀ x b → PEmb b (x ⊕ b)` (平移嵌入; `⊕` 是层号上的左加, `YiPEStep`), `toLevel-+` (读回的和的层号 ≅ᴵ 层号的左加), `ψ⁰-≺`, `ψ⁰Ω-≺` (第 0 层 ψ⁰ 与 ψ⁰∘Ω 结构严格单调), `PEmb-≅ʳ`, `PEmb-≅ˡ`.
- 它把下界归约成: `FUNC = ∀ {a b} → PEmb a b → PEmb (L⁺ a) (L⁺ b)` (参照一侧, `L⁺ a = toLevel (ψ⁰ (Ω a)) (Uniform a)`), `KEYsuc` (主线后继层号上参照对折叠的结构下界), `SpineT` (链点读回的极限相邻两支相等或严格). `btbo-FS⁺ : FUNC → KEYsuc → SpineT → D.BTBOᴵ ≼ NA.read NT.T⁺`.

和你的关系: 你的 `EmbVˢ` (严格树上的前驱嵌入) 若做成, 应当直接给出 `FUNC` 在严格层号上的版本 (`PEmb a b` 换成值序加严格), 也可能给出 `KEYsuc` 一类. 它的执行方判断: 对一切合法树判定 "相邻两支相等或读回严格上升" 推出 LPO (反例: 由二进制序列决定的极限), 所以严格性要作为对具体链点的命题出现, 不作为对一切合法树的引理 —— 你选严格谓词 S 时请注意这一点. 它列的第一个障碍: `FUNC` 的第一个实例 `PEmb (L⁺ (D.L 1)) (L⁺ (κ 1))`; 后继情形要比较两条塌缩链而层号之间只有嵌入.

## 回报原文

#### YiLow 回报：严格树上的前驱嵌入 (第 1 步被一条编译否定挡住)

##### 1 判决

- **第 1 步的一般陈述被否定，是编译定理：`embVˢ→LPO : EmbVˢ → LPO`。**
  - 严格谓词取 `SHS`：极限处相邻两项结构上严格上升 (`YiVmNegBase`)。
  - 探针都是严格的：x 固定为 ω+ω² (`xP`)，y 是由布尔序列 α 决定的严格树 `yP α`，两边都 `SHS`。推导 `der α : xP ≼ yP α` 对一切 α 一致给出。允许嵌入读推导里的数据，照样推出 LPO。
  - 推论 `embV→LPO : EmbV → LPO` (`YiMonoVM.EmbV`，普通前驱嵌入，不要求保初始段)。这是新的：此前只编译了保初始段版本推出 LPO (`embVᴰ→LPO`) 和不读推导的版本推出 MP。
- **界线在 ω² (编译定理)。** x = ω·k + n (ω² 以下的一切序数，`emb-ω²`) 对一切严格的 y 都有读推导的嵌入，`VMˢ` 在这些 x 上成立 (`vm-ω²`)。简报点名的 x 有限、ω、ω+1 都在其中。
- **第 2、3 步：`D.BTBOᴵ ≼ read T₃` 和对 `T⁺` 的同一条仍是条件定理，不是无条件定理。**
  - `FromVMᶜ.btbo` 与 `FromVMᶜ.btbo⁺` 的前提 `VMᶜ` 只要链上那些对的值单调，推导可以任意。
  - n = 0 的实例是定理 (`vmᶜ₀`)，链上两边在 n = 0 的严格性也是定理 (`S₀`)。
  - n ≥ 1 未走通。经 "值序推出嵌入" 去证它，这条路已被上面的否定挡住。
- **对纲领与目标的意思。**
  - 否定的是这条证法："先证一切严格树上值序推出前驱嵌入，再沿链归纳"。经嵌入证 `VMᴸ` 的一般写法 (`embV→vm`) 也一并挡住。
  - 不否定 `VMˢ` / `VMᴸ` 本身：ψ⁰ 层的左极限不需要一致性，难处只在后继情形 `Crux`，这一层没有找到否定。
  - 也不否定只对具体闭项 (链点) 陈述的嵌入：探针 `yP α` 依赖 α，不是任何链点的读回。按 AGENTS，这读作 "对一切严格树的全称太宽"，不是对 BTBO 下界本身的障碍。
- **与 YiPE 的关系 (判断)。**
  - 它的 `FUNC` 从嵌入到嵌入，不经过值序，不在这条否定的范围内。
  - 但任何需要 "一般严格对上由值序造嵌入" 的环节都被挡住，所以 `KEYsuc` 一类只能结构地做。
  - 我的 S 是作为前提出现的谓词，不是对一切合法树的判定，与它执行方的提醒一致。
- 强度：没有新的强度定理。

##### 2 文件表

都在 `probes/OCF/Lean/`，都是验收文件。冷编译：只删自己四个 `.agdai`，按依赖顺序编译，每份日志只有本模块一行 `Checking`，堆上限 6G。

| 文件 | 代码行 (agda 块非空行) / 总行 | 冷编译退出码 | 常驻峰值 |
|---|---|---|---|
| `YiLowBase.lagda.md` | 62 / 97 | 0 | 1.38G |
| `YiLowNeg.lagda.md` | 306 / 418 | 0 | 1.51G |
| `YiLowChain.lagda.md` | 39 / 57 | 0 | 1.43G |
| `YiLowPos.lagda.md` | 89 / 123 | 0 | 1.37G |

- 选项行都是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。
- 检索 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`--irrelevant-projections`、`--cubical`、`Funext`、本机路径：0 处。
- 日志在 `<实验目录>/agents/low/cold-*.log`。

##### 3 定理表

**YiLowBase**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `EmbVˢ` | `∀ (x : Ordᶜ zero) (hx : HS x) (y : Ordᶜ zero) (hy : HS y) → SHS x → SHS y → x ≼ y → PEmb (toLevel x hx) (toLevel y hy)` | 严格树上值序给出前驱嵌入 | 定义 |
| `VMˢ` | 同样的前提，结论 `ψ⁰ (Ω (toLevel x hx)) ≼ ψ⁰ (Ω (toLevel y hy))` | 严格树上的值单调 | 定义 |
| `embˢ→vmˢ` | `EmbVˢ → VMˢ` | 经 `Ψ-emb` | 编译定理 |
| `Into` | `Into a ha = ∀ (y : Ordᶜ zero) (hy : HS y) → SHS y → a ≼ y → PEmb (toLevel a ha) (toLevel y hy)` | 固定 x、y 取一切严格树 | 定义 |
| `into-suc` | `∀ {a} (ha : HS (suc a)) → Into a (hs⁻ ha) → Into (suc a) ha` | 后继提升 | 编译定理 |
| `emb-nat` | `∀ n (hx : HS (natᶜ n)) → Into (natᶜ n) hx` | x 有限 | 编译定理 |
| `emb-ω` | `∀ (hx : HS ωᶜ) → Into ωᶜ hx` | x = ω | 编译定理 |
| `emb-ω1` | `∀ (hx : HS (suc ωᶜ)) → Into (suc ωᶜ) hx` | x = ω+1 | 编译定理 |

**YiLowNeg**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `embVˢ→LPO` | `EmbVˢ → LPO` | 严格树上读推导的前驱嵌入推出 LPO | 编译定理 (否定) |
| `embV→LPO` | `EmbV → LPO` | `YiMonoVM` 的嵌入陈述推出 LPO | 编译定理 (否定) |
| `embX→LPO` | `EmbX → LPO`，`EmbX = ∀ (y : Ordᶜ zero) (sy : SHS y) → xP ≼ y → PEmb (toLevel xP (SHS→HS SHS-x)) (toLevel y (SHS→HS sy))` | 只要固定 x = ω+ω² 一个就够 | 编译定理 (否定) |
| `SHS-x`, `SHS-y`, `der` | `SHS xP`；`∀ α → SHS (yP α)`；`∀ α → xP ≼ yP α` | 探针严格，推导一致 | 编译定理 |
| `lc` | `∀ (A P Q : Ordᶜ zero) → A + P ≼ A + Q → P ≼ Q` | 值序的左消去 | 编译定理 |
| `rel-val` | 层号 T 的前驱保序地映进 [v, w) ⟹ `forget v + forget T ≼ forget w` | 相对的秩 | 编译定理 |

- `LPO` 用的是 `OCF.Barrier` 那一份。
- **否定的是什么**：`EmbVˢ`、`EmbV`、`EmbX`，即值序推出前驱嵌入，嵌入可以读推导。
- **不否定**：`VMˢ`、`VMᴸ`、`Crux`、`VMᶜ`，以及只对链点陈述的嵌入。
- **探针不退化**：每个极限的相邻项都结构上严格上升。
- **机制，逐条核过**：
  - 定理里没有折叠，也没有 ψ。失败的字段是 `map` (ω 的像 v)。
  - v 与 `z₀ α` 的比较由有界三歧决定 (`tri`)。
  - α 全假时 `z₀ α` 是 ω，v 在它之下就违反计数 (`cnt`)。
  - α 在第 k 位为真时，`yP α` 里 `z₀ α` 之上只有 ω·k 的空间，放不下 ω² (`room`：由 `rel-val` 得 z₀ + ω² ≼ z₀ + C，左消去后与 C 的界 `cc-bound` 矛盾)。
  - 它不是壁垒定理的实例 (没有下标类型)，也不是保初始段 (只用到 `PEmb` 的四个字段)。
- **可满足性 (判断)**：经典地两棵树的前驱模 `≅ᴵ` 都是良序，序型等于值，值序给出保序嵌入，所以 `EmbVˢ` 在经典模型里成立。没有编译 `LPO → EmbX` 一类的实例。

**YiLowPos**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `into-+ω` | `∀ {a} (h : HS (a + ωᶜ)) → Into (suc a) (hl₁ h 1) → Into (a + ωᶜ) h` | a+1 有嵌入则 a+ω 有 | 编译定理 |
| `emb-ω²` | `∀ k n (hx : HS (mulω k + natᶜ n)) → Into (mulω k + natᶜ n) hx` | ω² 以下一切 x | 编译定理 |
| `vm-ω²` | 同上的 x，结论 `ψ⁰ (Ω (toLevel (mulω k + natᶜ n) hx)) ≼ ψ⁰ (Ω (toLevel y hy))` | `VMˢ` 在 ω² 以下 | 编译定理 |

**YiLowChain**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `VMᶜ` | `∀ n → D.γ n ≼ read (co (pts n)) → L.ψ⁰ (L.Ω (D.L n)) ≼ L.ψ⁰ (L.Ω (κ n))` | 只在链上的值单调 | 定义 |
| `FromVMᶜ.btbo` | `D.BTBOᴵ ≼ read T₃`，模块参数 `vm : VMᶜ` | 主线 BTBO 下界 | 条件定理 |
| `FromVMᶜ.btbo⁺` | `D.BTBOᴵ ≼ NA.read NT.T⁺`，同一参数 | 经 `T₃≅` 与 `T₃≼T⁺` 接到下一站 | 条件定理 |
| `vmᴸ→vmᶜ` | `VMᴸ → VMᶜ` | | 编译定理 |
| `vmˢ→vmᶜ` | `VMˢ → (∀ n → SHS (D.γ n)) → (∀ n → SHS (read (co (pts n)))) → VMᶜ` | | 编译定理 |
| `S₀` | `SHS (D.γ 0) × SHS (read (co (pts 0)))` | 链上严格性在 n = 0 | 编译定理 |
| `vmᶜ₀` | `D.γ 0 ≼ read (co (pts 0)) → L.ψ⁰ (L.Ω (D.L 0)) ≼ L.ψ⁰ (L.Ω (κ 0))` | `VMᶜ` 在 n = 0 | 编译定理 |

`VMᶜ` 的可满足性：n = 0 是定理；`VMᴸ` 推出它；经典地成立 (判断)。

##### 4 办法

- **严格谓词**：选了结构严格的 `SHS`，而不是值严格的 `Strict`。理由有两条：
  - 结构严格时 `toLevel (f n) ≺ᴵ toLevel (f (n+1))`，前驱落在哪一段可以由有界三歧判定。
  - `SHS` 推出值严格，所以对 `SHS` 的否定也否定值严格的版本。
- **能拼的左极限**：
  - y 是严格的极限时，余下各段若是单点，就映到 y 的后续各项。y 严格保证后续还有 ω 个点。
  - a + ω 的前驱按 "在 a+1 之下 / 是点 a+(j+1)" 分类 (`cls`, `side`)。前者用 a+1 ≼ g m 那条推导给出的嵌入，后者映到 g (j+m)。一致性来自这个分类本身，不要求各项嵌入在公共前驱上一致。
- **为什么到 ω² 就不行**：
  - 左极限的第一段的像要给余下部分留出空间。余下部分达到 ω² 时，所需空间由无穷多个后项决定，有限的信息定不下来。
  - 探针把 "空间够不够" 编码成 α：α 全假时像必须高 (`z₀` 太小)，α 有真位时像必须低 (`z₀` 之上空间不够)。
- **与已知原则的关系**：这次没有绕开，而是撞上了 LPO，并写成了定理。它不是保初始段那条，也不是 Markov 那条 (推导是带数据的)。

##### 5 第一个障碍

- 没有检查器报错。缺的是 `VMᶜ` 在 n ≥ 1 的实例，类型如上。
- 经嵌入的证法要求判定 LPO，这一点已编译 (`embVˢ→LPO`)。
- 剩下的可能 (判断)：
  - 在 ψ⁰ 层直接证链上的 `Crux`，不经过对一切严格树的嵌入；
  - 或者只对链点陈述的结构嵌入 (YiPE 的 `FUNC`/`KEYsuc` 方向)。
- 第 2 步 (链上两边在 n ≥ 1 的严格性) 没有做。卡在 ψ⁰ 的 `limᵢ` 支：要证塌缩迭代 ψ⁰(f xₙ) ≺ ψ⁰(f xₙ₊₁) 结构严格，相当于把 `Uniform` 的 HS 证明加强成严格版。在否定之下，这一步对经嵌入的路线已无意义。

##### 6 偏离与事故

- 多写了两个文件：`YiLowNeg` (简报允许的否定交回) 和 `YiLowPos` (给出 ω² 的界线)，都是带定理的 literate 文件。
- 没有改任何已有文件，没碰 `src/`、`archive/`，没有用 YiPE 的文件，没有提交，也没写一次性的试验文件。
- 编译错误都是自己的，各改一次就过：
  - `{zero}` 被当成双关，改成具名的 `{b = zero}`；
  - `hz`、`out` 与 `Level` 里的名字冲突，改名为 `hz₀`、`pick`；
  - `YiLowPos` 里两处 `≅ᴵ-sym` 的方向写错了。
- 只删过自己四个模块的 `.agdai`，写的是字面路径。
