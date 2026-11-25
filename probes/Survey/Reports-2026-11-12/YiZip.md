# 保留时带结构搬运的决定性实验 (YiZip)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 03:43 至 04:08 |
| 工具调用 / agda 编译 (粗数) | 46 / 10 |
| token (usage 字段，按消息去重) | 输出 158118；新写入缓存的输入 347433；读缓存的输入 6810584；其余输入 78 |
| 写过的仓库文件 | `YiZipFold.lagda.md`, `YiZipLost.lagda.md`, `YiZipMove.lagda.md`, `YiZipSim.lagda.md`, `YiZipWay.lagda.md` |
| 文件前缀 | `YiZip` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: 保留时带结构搬运的决定性实验返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 合法一侧没有技术障碍：整个折叠接上，Λ 闭项合法；卡住的一对保留；反面：只按结构对齐会跨支保留没有槽位的一对；五件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的指示是 "朝着最终目标的关键路径走"; 这一路作者选的是第九次独立审查建议的 **决定性实验: 保留时带结构搬运**. 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 背景 (事实)

- 一致折叠 `probes/OCF/Lean/YiDlFold.lagda.md` (对派发参数化, `module Fold (D : ∀ k K → Ext k K)`; 实例取燃料搜索 `dl`). 派发的结果类型是 `YiNextBase` 的 `Way m j`: `keep (s : Pre m) (lev m s ≡ j)` 或 `fold`. 保留一个位置时, 要给出目标位置的层号与源层号的**字面相等**.
- ψ₀(Ω_Ω·2) 的下界卡在一处: 被问到的一对位置 (`YiDlLost` 的 `rN`, `pN`) 源层号是 ℕ 极限, 派发折叠它 (`dl-lim`, `lostP`). 第九次审查的实验 (`probes/Survey/Reports-2026-11-12/attachments/Review9-R9Same.agda.txt`, 主审已复核) 说明: 这一对在同一支里, 用这一支的公共上界比较就保留, 层号相等由位置搬运 (`Shift`) 算出; 缺的是派发的输入没有来历. 说明在 `probes/Survey/RR9-OmegaOmega2.md`, 全读.
- 审查的候选设计 (台账 U24, 判断): 把 `Way` 的 keep 里的字面层号相等, 换成一个**保合法、保第一位置的结构搬运** `Raw (lev m s) → Raw j` (或反方向, 看折叠哪里用到), 形状照参照框架 `probes/OCF/Align/Level.lagda.md` 的 `tr`, `tr⁻`, `res` (检索这几个), 匹配不上时取第一支的值 (仿 `YiLamFold` 的 `Kfk` 的 `lc` 子句). 这样不必判定层号相等, 只改第 2 层, 不改块.

#### 要交的 (决定性实验; 每做成一步先交)

1. **搬运**: 在两个只含 zero / suc / lim 的层号之间 (Ω 结点层号先不管) 定义树的搬运与逆搬运, 对一切这样的两个层号都有定义. 证明: 保第一位置 (`Cp`), 保合法 (`Lgl`), 由检查器保证停机 (不许 `TERMINATING`). 再证一条组合律: 分支族 (`YiNextBase` 的 `Br`) 与搬运复合后仍是 `Br`.
2. **值正确的情形**: 当两个层号由公共上界的位置搬运联系起来时 (像 R9Same 里那样, 由 `Shift` 给出层号相等), 证明搬运就是那份结构拷贝 (例如与 `subst` 沿那条相等的结果相同, 或两边读回互模拟). 说清 "值正确" 在你的陈述里指什么.
3. **接进一行**: 写一个派发结果的新类型 (例如 `Way′`, keep 带搬运而不带字面相等), 只在一个最小的折叠片段 (例如结点那一行 `ΨN` 的类似物) 上证明合法性保持. 若容易, 在 `YiDlLost` 那一对上给出一个保留它的派发, 作为有限测试.
4. **判决**: 编得过, 就说明审查的设计 (a1) 没有技术障碍, 并给出把它接进整个一致折叠的规模估计 (判断); 编不过, 给出确切的障碍 (检查器报错原文, 缺的引理的类型), 以及它是不是在要求判定什么.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理); 堆到 6G 仍耗尽. 没有编译的否定时只写 "未走通".

#### 先读什么

`AGENTS.md` 全篇 (特别是 Agda 一节, 文字预算, 结论的写法); `probes/Survey/EBOHandbook.md` §4.1 到 §4.5; `probes/OCF/Lean/YiNextCore.lagda.md` (块; `Cp`, `Dn`, `Lgl`); `YiNextBase.lagda.md` 只检索 `Way`, `Ext`, `Shift`, `lev`, `ΨN`, `ΨN-lgl`, `nodeAt`, `Br`; `YiLamFold.lagda.md` 只检索 `Kfk`, `cmpw`, `cps`; `YiDlFold.lagda.md`; `YiDlLost.lagda.md`. 查签名用检索, 大文件不要整篇读.

#### 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiZip` (模块名 `OCF.Lean.YiZip…`). 非验收文件 (只导入 `probes/OCF/Lean/` 的主线文件与标准库, 文首写 "非验收文件"); 若要参照框架作对照, 放单独的验收文件. 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`, 函数外延 (作显式前提可以, 只放验收文件).
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径. 不要把仓库整个拷到临时目录.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽. 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块; 另一路也在编译.
- 你的临时目录: `<实验目录>/agents/zip`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 过程要求: 读完上面的文件后尽快动手, 第一个文件在 20 分钟内写出并编译; 每次回复都要有工具调用, 不要在一次回复里只思考.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0; 对非验收文件跑 `python3 probes/Survey/scripts/importclosure.py <模块名…> --only OCF.Lean.`.

#### 回报格式 (只在回报里交一次)

1. 判决: 做到第几步; 一段话说对目标意味着什么 (审查的设计 (a1) 有没有技术障碍).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值, 是否验收文件, 导入闭包结果.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断).
4. 办法与翻译账 (新东西读的是什么, 哪些由树的要求逼出).
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型; 是不是在要求判定什么.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### 1. 判决

四步都做到了，第 4 步还多走了一段：没有停在规模估计，把整个一致折叠都接上了 `Way′` 并编译通过。

**对目标意味着什么.** 审查的设计 (a1)，即保留时带结构搬运、不带层号的字面相等，在合法性、停机和接进整个折叠这三件事上没有技术障碍。这三件都是编译定理，无前提；新闭项 `TΛ′`、`Tw′ n`、`T⁺ʷ′` 合法，同样无前提。`lostP` 那一对在新的比较下保留在原来的槽位 `s` 上，保留用的搬运与恒等互模拟（有限测试加编译定理）。

但实验同时编译出一个反面：Ω 结点层号那一句按目标的支做结构对齐，它不知道源位置是不是真的在同一支。所以目标层里根本没有与源层号相等的槽位时，它也会保留 (`cross-keep` 加 `no-slot`)。换句话说，搬运去掉的只是"证明层号相等"这项义务，"什么时候该保留"这个选择问题还在，就是 RR9 说的派发的输入没有来历。新折叠输出的值没有任何定理。

#### 2. 文件表

| 文件 | 总行 / 代码行 | 冷编译退出码 | 常驻内存峰值 | 验收文件 | 导入闭包 (`--only OCF.Lean.`) |
|---|---|---|---|---|---|
| `probes/OCF/Lean/YiZipMove.lagda.md` | 153 / 116 | 0 | 376 MB | 否 | OK，10 个模块，命中 0 |
| `probes/OCF/Lean/YiZipSim.lagda.md` | 119 / 79 | 0 | 380 MB | 否 | OK，11 个模块，命中 0 |
| `probes/OCF/Lean/YiZipWay.lagda.md` | 133 / 89 | 0 | 368 MB | 否 | OK，11 个模块，命中 0 |
| `probes/OCF/Lean/YiZipFold.lagda.md` | 154 / 111 | 0 | 452 MB | 否 | OK，29 个模块，命中 0 |
| `probes/OCF/Lean/YiZipLost.lagda.md` | 109 / 68 | 0 | 391 MB | 否 | OK，33 个模块，命中 0 |

- **冷编译:** 删掉这五个自己的 `.agdai` 后按依赖次序逐个编译，每个日志只有自己那一行 `Checking`，每个 2 秒以内，无警告。
- **禁用构造:** 检索为 0（无 postulate、洞、编译指示、函数外延）。
- **其他:** 仓库文件里没有本机路径；没有改任何已有文件。

#### 3. 定理表

记号: `mv` 是层号间的搬运，`Sm a` 指层号 `a` 只含 zero/suc/lim，`Sim` 是互模拟（定义见 §4）。

| 名字 | 陈述（逐字） | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `mv`, `mvN` | `mv : (a b : LF) → Raw a → Raw b` | 对一切两个层号定义的树的搬运，检查器保证停机 | Move | 定义 |
| `mv-top` | `∀ a b → mv a b G.top ≡ G.top` | 顶搬到顶 | Move | 编译定理 (`refl`) |
| `mv-cp` | `∀ a b {x y : Raw a} → Cp a x y → Cp b (mv a b x) (mv a b y)` | 保第一位置（对一切树） | Move | 编译定理 |
| `mv-lgl` | `∀ a b (x : Raw a) → Lgl a x → Lgl b (mv a b x)` | 保合法 | Move | 编译定理 |
| `mv-br` | `∀ c d {M} (h : Raw d → Raw M) → Br (layer d) M h → Br (layer c) M (λ η → h (mv c d η))` | 分支族与搬运复合仍是 `Br` | Move | 编译定理 |
| `mvN-eq` | `∀ {a} → Sm a → ∀ {M} (B : Bld M a) (r : Pre a) (h : Lay.A (Lo a r) → Raw M) → mvN a a B r h ≡ B r (λ η → h (bk a r η))` | 同层搬运时结点落回同一位置 | Sim | 编译定理 |
| `mv-sim` | `∀ {a} → Sm a → ∀ {x y} → Sim a x y → Sim a (mv a a x) y` | 搬到自己是结构拷贝 | Sim | 编译定理 |
| `mv-subst` | `∀ {L j} (e : L ≡ j) → Sm L → ∀ {x y} → Sim L x y → Sim j (mv L j x) (subst Raw e y)` | 沿层号的相等，搬运与 `subst` 互模拟 | Sim | 编译定理 |
| `sim0` | `∀ x → Sim zero x x` | 第 0 层上互模拟自反 | Sim | 编译定理 |
| `up0-sm` | `∀ η → Sm (up zero η)` | 第 0 层树的读回只含 zero/suc/lim | Sim | 编译定理 |
| `lev-sm` | `∀ {a} → Sm a → (r : Pre a) → Sm (lev a r)` | 这种层号的位置层号也只含 zero/suc/lim | Sim | 编译定理 |
| `Br-run` | `∀ {L j M} (t : Mv L j) (g : Raw j → Raw M) → Br (layer j) M g → Br (layer L) M (λ η → g (run t η))` | 任意合格的搬运与分支族复合仍是 `Br` | Way | 编译定理 |
| `ΨN′-lgl` | `∀ m k r (w : Way′ m (lev k r)) gm gk → Br (Lo k r) m gm → (∀ η → Lay.lg (Lo k r) η → Lgl (lev k r) (gk η)) → Lgl m (ΨN′ m k r w gm gk)` | 结点那一行对一切 `Way′` 保合法 | Way | 编译定理 |
| `ΨN′-dn` | `∀ m k r (w : Way′ m (lev k r)) gm gk {z} → Cp m z (gm (Lay.tp (Lo k r))) → Dn m z (ΨN′ m k r w gm gk)` | 结点那一行保第一位置 | Way | 编译定理 |
| `ΩT′-lgl` | `∀ m j (w : Way′ m j) K o → Br (layer j) m K → Lgl m (G.lim o) → Lgl m (ΩT′ m j w K o)` | `top` 那一行保合法 | Way | 编译定理 |
| `ΨN′-eq` | `∀ m k r (w : Way m (lev k r)) gm gk → ΨN′ m k r (fromWay w) gm gk ≡ ΨN m k r w gm gk` | 旧的 `keep s e` 是特例，结点逐字相同 | Way | 编译定理 |
| `ΩT′-eq` | 同上，对 `ΩT` | 同上 | Way | 编译定理 |
| `Ψ′-lgl` | `∀ m {k} (V : Lw k) x ξ → Lgl k ξ → Lgl m (Ψ′ m V x ξ)`（在 `module Fold′ (D : ∀ k K → Ext′ k K)` 里） | 新折叠对一切派发保合法 | Fold | 编译定理 |
| `TΛ′-legal` | `Lgl zero TΛ′` | 读法 ψ₀(Λ) 的新闭项合法 | Fold | 编译定理 |
| `Tw′-legal` | `∀ n → Lgl zero (Tw′ n)` | 塔的各项合法 | Fold | 编译定理 |
| `T⁺ʷ′-legal` | `Lgl zero T⁺ʷ′` | 读法 ψ₀(Ω_{Ω+1}) 的闭项合法 | Fold | 编译定理 |
| `old-fold` | `cmpw V2 rN pN ≡ fold` | 旧比较折叠这一对（即 `lostP`） | Lost | 有限测试 |
| `kept` | `IsKeep′ (cmpz V2 rN pN)` | 新比较保留这一对 | Lost | 有限测试 |
| `kept-at` | `cmpz V2 rN pN ≡ keep′ sN (byEq refl ⨾ byMv L L)` | 保留在 `YiDlLost` 的槽位 `s` 上，搬运是 `mv L L` | Lost | 有限测试 |
| `node-kept` | `∀ (g : Raw L → Raw (tw 2)) → Ψ′ LN V2 (cmpz V2 rN) (G.lc pN g) ≡ G.lc sN (λ η → Ψ′ LN V2 (cmpz V2 rN) (g (mv L L η)))` | 在新折叠里，`pN` 上的结点落在 `s` 上 | Lost | 有限测试（闭位置，`g` 任意） |
| `tw2-sm` | `∀ (p : Pre (tw 2)) → Sm (lev (tw 2) p)` | `tw 2` 一切位置的层号只含 zero/suc/lim | Lost | 编译定理 |
| `kept-copy` | `∀ {x y} → Sim L x y → Sim L (run (byEq refl ⨾ byMv L L) x) y` | 这份保留的搬运与恒等互模拟 | Lost | 编译定理 |
| `shift-copy` | `∀ {x y} → Sim (lev (comp LN 1) s₁) x y → Sim (lev (comp LN 0) s₀) (mv (lev (comp LN 1) s₁) (lev (comp LN 0) s₀) x) (subst Raw shift-eq y)` | R9Same 里由 `Shift` 算出的层号相等上，搬运与 `subst` 互模拟 | Lost | 编译定理（闭实例） |
| `root-kept′` | `rootZ (lev (tw 2) rN) zero ⌜_⌝ (witU zero) (cmpz V2 rN) ≡ keep′ (0 , 0 , 0 , inj₂ (inj₁ tt)) (byEq refl)` | 旧派发保留的根仍在原槽位 | Lost | 有限测试 |
| `cross-old` | `cmpw V2 q₂ r₃ ≡ fold` | 跨支的一对，旧比较折叠 | Lost | 有限测试 |
| `cross-keep` | `cmpz V2 q₂ r₃ ≡ keep′ (inj₁ tt) (byEq refl ⨾ byMv zero (suc zero))` | 跨支的一对，新比较保留到层号 0 的槽位，源层号是 1 | Lost | 有限测试 |
| `no-slot` | `(p : Pre (lev (tw 2) q₂)) → lev (lev (tw 2) q₂) p ≡ lev (tw 2) r₃ → ⊥` | 那个目标层里没有与源层号相等的槽位 | Lost | 编译定理 |

`cross-keep` 用的位置: `q₂` 是第 2 支（`⌜η⌝ = 2`）里的 `inj₁ tt`，`r₃` 是第 3 支里的 `inj₂ (inj₁ tt)`。

#### 4. 办法与翻译账

**"值正确" 在陈述里指互模拟 `Sim`.**
- 定义: 同一层上两棵树逐个构造子对应，结点的位置与孩子的下标字面相同，结点的分支把互模拟的输入送到互模拟的输出。
- 写法: 是部分等价关系，形状照参照框架 `Level` 的 `lᵢ≅`。数据类型 `SimAt` 把低层的关系作参数，所以严格正；不要函数外延。
- 它不比 `≡` 弱于必要: 分支在搬过的输入上取值，没有函数外延就证不出和原树字面相等，第 0 层也一样。
- 一般层上 `Sim` 不自反，因为分支函数未必尊重互模拟；所以 `mv-subst` 带的前提 `Sim L x y` 是互模拟的定义域条件。

**读自哪里.**
- 参照框架 `Level` 的 `tr`/`tr⁻`/`res`：借了形状（分支的输入反向搬运），停机度量换成两个层号互换且都严格下降，所以不需要层号关系的证明，对一切层号对都有定义。只借形状，没有导入代码。
- 对不上时取 `top` 那一支：来自 `YiLamFold` 的 `Kfk` 的 `lc` 子句（树侧）。
- 位置的结构对齐 `PT`，以及 Ω 结点那一句"先问 `D`，`D` 折叠再按目标的支比较"：来自审查的建议，是派发上的启发式，不是树的要求逼出的。
- 不读记号，没有 `Lab`。

**由树的要求逼出.**
- `Mv` 的四个字段：`run-tp` 是 `Ψn′-dn` 要的（结点的第一位置经过 `top` 那一支）；`run-cp`、`run-lg` 是 `Br` 要的。
- 值正确只对 `Sm` 层号陈述：Ω 结点层号的位置带合法性证明，要做结构拷贝就得让 `mv` 与 `mv-lgl` 互相定义，而且位置会换成 `mv η`，与 `c≈` 要求的同一位置冲突（判断）。

**翻译账.**
- 新脚手架：`Mv`、`Sim`、`PT`/`viaM`/`orW`。前两样是合法性与"无函数外延地陈述值"所需；后一样是派发的选择。
- `cross-keep` 加 `no-slot` 是一条编译过的反面，划出了"仅按结构对齐"不能有的行为：它违反树自己的判据"目标层没有该层号的槽位就必须折叠"。

**规模（事实，不再是估计）.** 搬运、`Way′` 和整个折叠合计 316 代码行（Move 116 + Way 89 + Fold 111）。审查估计 300 到 450 行，指的是同一件事里的合法性部分。

#### 5. 第一个障碍

检查器上没有障碍，没有报错原文可附。第一个障碍在值上：
- **事实.** `cross-keep` 与 `no-slot` 是编译过的反面。
- **缺的引理（判断）.** 要让 Ω 结点那一句的保留在值上可靠，需要一条判据，大致是 `(q r : Pre (lc k g)) → Dec (proj₁ q ≡ proj₁ r)`（两支相等），或者对 ℕ 极限层号判定 `At (lev (lc k g) q) (lev (lc k g) r)`。
- **是不是在要求判定（判断）.** 若这条判据只能从派发的输入（目标位置、裸源位置）造出来，它就是在要求判定两棵含 ℕ 极限的树相等，或判定极限层号相等，这正是要避开的。不判定的出路是让来历随树走，例如位置相对于外层结点的支编码，但那要改块，属于 (a2)，要作者定。没有编译的否定，这一点只算 "未走通"。
- **未查清的（判断）.** 闭项 `T⁺ʷ′`、`Tw′ n` 里这种跨支保留是否真的出现、出现后是升值还是降值，都没有测。纸面上看，`Kfk zero Tt a` 部分的结点在根位置上会自比较而折叠，内层位置多因 suc/lim 形状不合而对不上，所以可能少见。

#### 6. 偏离与事故

- **定义域放宽.** 简报只要求零、后继、ℕ 极限层号之间的搬运；`mv` 对一切层号对都有定义，Ω 结点层号走回退分支。值正确只对 `Sm` 陈述。
- **超出第 3 步.** 把整个折叠也接上了（`YiZipFold`），所以第 4 步的规模是编译事实。
- **`cmpz` 的设计改过一次.** 起初 Ω 结点那一句只做结构对齐。纸面上看到它会丢掉 `YiDlInst.root-kept`（根对根自比较会折叠），于是改成先问 `D`、`D` 折叠再做结构对齐；`root-kept′` 确认改后根仍在原槽位。"只做结构对齐会丢根"这一点没有单独编译测试，是纸面判断。
- **一次编译错误.** `YiZipSim` 的构造子 `s` 与 `YiDlLost` 的 `s` 撞名，报 `SplitError.NotADatatype`；改名后通过。
- **一次 shell 失败.** zsh 下一个含反引号的 heredoc 没有执行，没有副作用。
- **没碰别人的模块.** 没有重编别人的模块，所有日志只有自己模块的 `Checking` 行；没写临时目录以外的地方；没有提交。
