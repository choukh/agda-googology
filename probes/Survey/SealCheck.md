# 封存族的编译检查, 与 `lab-NF` 能否接替参照角色 (2026-11-05)

> 对应 `RouteReview2` 的 P7 与 §4 第 6 条, `EBOHandbook` 3.11 ("封存路线悄悄腐烂"). 三档分开: **编译** = 本次跑过, 退出码 0; **启发** = 文件时间戳、导入图这类机械事实, 不是编译; **判断** = 纸面.
>
> **结论.**
>
> 1. `RouteSeal` §1–§6 与 §8 列的入口, 除 5 个大堆入口外, **41 个全部退出码 0** (编译, 堆上限 12G, 用已有接口). 41 个入口共用时 406 秒, 单个最大常驻内存 6.0G (`EmbVV`). 只有 `BTBOVal` 真的重新检查了模块 (4 个没有接口的模块: `BTBOVal`, `BTBOValLe`, `BTBOValLeInst`, `BTBOValTest`), 其余全部从接口加载. 参照侧 `EboLean` (3 秒), `WfFsn` (带归档拷贝, 73 秒, 9.5G, 新拷贝的 42 个归档模块要检查一遍), `EboLeanCmp` (26 秒) 也都是 0.
> 2. 5 个大堆入口 (`LadderOrd`, `CrossM`, `CrossNext`, `WorldTH`, `WeakBridge`) 没有跑, 列在 §3, 留到单独的时段. 但它们导入闭包里的大部分模块已经被别的入口加载过 (编译): `LadderOrd` 115 个里 114 个, `WorldTH` 15 个里 14 个, 只差入口文件本身. 没被加载的只有入口文件和几个叶模块 (`CrossMNeg`, `CrossNextInst`, `WeakBridgeOp` 等).
> 3. **作为序数值验收的尺子, §1 可以由 `lab-NF` 接替, 而且在活集里实际上已经接替了** (判断, 依据见 §4.1–§4.2): 活集 142 个模块的导入闭包里没有一个 §1 模块; 活集的验收要么用 `WfFsn` (`EndLowAccept`), 要么用 §3 的 `BTBOFull`/`NoCumsum` (`SumOneAccept`, `TLRuleAccept`). **§1 还不能降成 "只封存, 不必可编译"**, 原因有两条, 都不是参照角色: §2–§6 的封存族有 36 个模块直接导入 §1 (数据类型和比较对象 `T⊤`); `README` 死路索引里有 10 条否定定理, 还有 `AGENTS.md` 举例用的 `same-M₂`, 都在 §1 里.
> 4. 附带发现 (启发): **§3、§4、§5 各有一部分其实在活集里**. `CumReadCF` (主线的类型 `A`), `BTBOFull*`, `BTBOVal*` (除 `Le`/`LeInst`/`Test`), `CumUpAcceptSim`, `NoCumLit`, `LevelFixCore`, `LevelFixVal`, 共 23 个模块. 它们随活集复核, 不能当封存族对待.

## 1 方法

- **命令** (从仓库根, 一次只跑一个, 顺序执行):

  ```sh
  /usr/bin/time -l agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/<入口>.lagda.md +RTS -M12G -RTS > log 2>&1; echo exit=$?
  ```

  `/usr/bin/time` 原样返回 agda 的退出码, 没有经过管道. 内存取 `maximum resident set size`. "检查数" 是日志里 `Checking` 行的条数: 0 表示整个闭包都从接口加载.
- **档.** 用的是已有接口, 没有用 `--ignore-interfaces`, 也没删接口 (按简报). Agda 加载接口前会核对源文件哈希和选项, 所以退出码 0 说明: 当前源码的每个模块, 都有一份由这个 Agda 版本 (2.8.0.2) 检查通过的接口. 这不是从头复核: 没有重新检查证明本身, 而 Agda 版本或 stdlib 一换, 接口就全部作废.
- **上游没动 (启发).** `git status` 显示, 封存提交 `a5b202c` (11-04 22:06) 以后, `probes/OCF` 和 `src` 下没有被跟踪的文件被修改, 新增的都是新文件. 所以封存族的源码和它们依赖的源码与封存时相同. 腐烂的风险来自将来的改动 (例如 RouteReview2 R1 提到要改 `H`), 不是来自现在.
- **入口的选法.** 每族取 `RouteSeal` 写的入口. §1 另加 `EmbVV`, `OrdLabAccept`, `OrdLabReadTop`, `ValLabNeg`, `ValLabNegTop` (§1 的验收和否定在这几个文件里, 不在 `LadderOrd` 的导入闭包里); §4 加 `NoCumNodeAccept`; §3 加 `BTBOVal` (它的入口在 11-04 的复核里被删过接口, 一直没有重建). §7 是 `README` 的已关闭方向和 `archive/`, 没有入口可编译.

## 2 入口表

| 族 | 入口 | 退出码 | 秒 | 最大常驻 | 检查数 | 状态 |
|---|---|---|---|---|---|---|
| §1 | `LadderNF` | 0 | 7 | 1.3G | 0 | 通过 |
| §1 | `LadderInf` | 0 | 15 | 2.3G | 0 | 通过 |
| §1 | `TLOne` | 0 | 11 | 1.8G | 0 | 通过 |
| §1 | `TLCode` | 0 | 11 | 1.9G | 0 | 通过 |
| §1 | `EmbVV` | 0 | 39 | 6.0G | 0 | 通过 |
| §1 | `OrdLabAccept` | 0 | 33 | 4.9G | 0 | 通过 |
| §1 | `OrdLabReadTop` | 0 | 33 | 4.8G | 0 | 通过 |
| §1 | `ValLabNeg` | 0 | 32 | 5.0G | 0 | 通过 |
| §1 | `ValLabNegTop` | 0 | 35 | 5.1G | 0 | 通过 |
| §2 | `GuardTight` | 0 | 4 | 0.8G | 0 | 通过 |
| §2 | `GuardRead` | 0 | 5 | 0.8G | 0 | 通过 |
| §2 | `GuardWeak` | 0 | 5 | 0.8G | 0 | 通过 |
| §2 | `GuardCert` | 0 | 6 | 1.1G | 0 | 通过 |
| §2 | `GuardBridge` | 0 | 5 | 0.9G | 0 | 通过 |
| §3 | `CumRead` | 0 | 2 | 0.4G | 0 | 通过 |
| §3 | `CumUp` | 0 | 4 | 0.8G | 0 | 通过 |
| §3 | `CumVal` | 0 | 8 | 1.6G | 0 | 通过 |
| §3 | `CumHt` | 0 | 4 | 1.0G | 0 | 通过 |
| §3 | `Om1Cum` | 0 | 11 | 1.8G | 0 | 通过 |
| §3 | `BTBOFull` | 0 | 7 | 1.1G | 0 | 通过 |
| §3 | `BTBOVal` | 0 | 10 | 1.5G | 4 | 通过 (重新检查了 `BTBOVal`, `BTBOValLe`, `BTBOValLeInst`, `BTBOValTest`, 接口是新写的) |
| §4 | `NoCum` | 0 | 3 | 0.8G | 0 | 通过 |
| §4 | `NoCumHn` | 0 | 4 | 0.8G | 0 | 通过 |
| §4 | `Om1Hn` | 0 | 4 | 0.8G | 0 | 通过 |
| §4 | `NoCumNode` | 0 | 5 | 1.0G | 0 | 通过 |
| §4 | `NoCumNodeAccept` | 0 | 10 | 1.5G | 0 | 通过 |
| §4 | `TLOps` | 0 | 5 | 0.9G | 0 | 通过 |
| §4 | `TLPrefix` | 0 | 19 | 2.8G | 0 | 通过 |
| §4 | `CtxMono` | 0 | 9 | 1.5G | 0 | 通过 |
| §5 | `LevelFix` | 0 | 3 | 0.6G | 0 | 通过 |
| §5 | `LevelNoK` | 0 | 2 | 0.5G | 0 | 通过 |
| §5 | `NoKCert` | 0 | 3 | 0.5G | 0 | 通过 |
| §6 | `TreeJudge` | 0 | 3 | 0.5G | 0 | 通过 |
| §6 | `ValueJudge` | 0 | 17 | 2.6G | 0 | 通过 (文档记 "约 12G", 那是从头检查的数) |
| §6 | `TLEnd` | 0 | 12 | 2.1G | 0 | 通过 |
| §6 | `TLBehave` | 0 | 5 | 1.1G | 0 | 通过 |
| §6 | `AddClo` | 0 | 2 | 0.4G | 0 | 通过 |
| §6 | `AddTwo` | 0 | 2 | 0.4G | 0 | 通过 |
| §8 | `SumHt` | 0 | 2 | 0.4G | 0 | 通过 |
| §8 | `SumClimb` | 0 | 2 | 0.4G | 0 | 通过 |
| §8 | `SumVar` | 0 | 4 | 0.6G | 0 | 通过 |
| 参照 | `EboLean` | 0 | 3 | 0.6G | 0 | 通过 (不要归档) |
| 参照 | `WfFsn` (`-i <scratch>/sealcheck/arch`) | 0 | 73 | 9.5G | 42 | 通过. 42 个检查全是 scratch 里新拷的归档 `Mahlo` 模块 (新拷贝没有接口); `probes` 的模块一个也没重查 |
| 参照 | `EboLeanCmp` (同上, 归档接口已建) | 0 | 26 | 3.8G | 0 | 通过 |

没有失败, 没有堆耗尽, 所以 "第一个错误" 一栏省略. 日志在 scratch (`sealcheck/log-<入口>.txt`), 不入库.

## 3 需单独时段 (本次没跑)

| 族 | 入口 | 文档记的堆 (从头检查) | 闭包里已被别的入口加载的模块 (编译) | 没被加载的模块 |
|---|---|---|---|---|
| §1 | `LadderOrd` | >14G (14G 堆耗尽, 45G 通过, 约 14 分钟) | 114 / 115 | `LadderOrd` (90 行, 只有导入) |
| §1 | `CrossM` | 25G | 55 / 59 | `CrossM`, `CrossMNeg`, `CrossMClosedTest`, `CrossMTopTest` |
| §1 | `CrossNext` | 22G | 57 / 61 | `CrossNext`, `CrossNextDn`, `CrossNextInst`, `CrossNextTest` |
| §3 | `WorldTH` | 峰值约 15G, 约 15 分钟 (`WorldTHInst` 8G 三次堆耗尽) | 14 / 15 | `WorldTH` |
| §2 | `WeakBridge` | `WeakBridgeOp` 峰值约 16G (15G 上限内通过); 入口约 5 分钟 | 68 / 80 | `WeakBridge`, `WeakBridgeOp`, `WeakBridgeMain`, `WeakBridgeNext` 等 12 个 |

- 第 4 列来自导入图 (`cover.py`, 正则读 `import`, 启发): 一个模块在某个已通过入口的闭包里, 就说明它的接口有效 (编译). 例如 `LadderOrdMain` (闭包定理 `GᴺTᵠ`)、`LadderOrdNeg` (`no-all-Ord` 等) 由 `EmbVV`, `TLPrefix`, `TLEnd` 的闭包加载过; `CrossMClosed` (`T⊤`) 由 `TLEnd`, `TLOps` 加载过.
- 没被加载的模块, 接口文件都在, 修改时间都晚于源文件 (启发, 不是 Agda 的哈希检查).
- **判断:** 接口有效的话, 这 5 个入口应当只是加载, 用时和内存与 `EmbVV` 同量级 (几十秒, 6G 以内). 建议统筹者在别的路不编译时, 用 `-M12G` 依次跑这 5 个. 退出码 0 就补进 §2 表; 若是 251, 说明有接口失效、在重新检查, 那就按文档的堆 (45G, 25G, 22G, 16G, 15G) 单独再跑.

## 4 参照角色: `lab-NF` 能否取代 §1

### 4.1 现在谁在用 §1 (启发, 导入图)

- **活集不用.** 活集按 RouteReview2 P7 的清单取前缀: `TLRule`, `SumOne`, `HtFeed`, `HtOut`, `HtCross`, `DVal`, `KVal`, `EndLow`, `WfFsn`, `L1Val`, `EboLean`, `Brw`, `Cv`, `LayerTr`, `Review2Blind`, 共 142 个模块, 导入闭包 322 个模块. 闭包里 §1 模块 0 个, §2 0 个, §6 0 个, §8 0 个; §3 20 个 (`BTBOFull*`, `BTBOVal{Absorb,Base,Dn,Main,Neg,Up}`, `CumReadBase`, `CumReadCF*`, `CumUpAcceptSim`), §4 1 个 (`NoCumLit`), §5 2 个 (`LevelFixCore`, `LevelFixVal`, 由 `BrwMidZero` 导入).
- **活集的尺子已经不是 §1.** `EndLowAccept` 用 `WfFsn.EBO-tree`/`ebo-lab` (opaque 的 `treeE k`), 第 2 级靠 `Lab-uniq` 与 `BTBOᴵ` 认同 (`treeE2≅ = Lab-uniq (treeE-lab 2) BTBO-label`). `SumOneAccept.T₀≈`, `TLRuleAccept.T≈` 用 `BTBOFull`, `NoCumsum`. 也就是说, ψ₀(Ω_Ω) 以下的尺子是 §3 的 `BTBOᴵ`, 一般的尺子是 `WfFsn`. ψ₀(Ω_Ω) 以上, 主线没有任何值定理 (RouteReview2 R5), 所以 ψ₀(Ω_Ω) 到 ψ₀(Ω_{Ω·ω²}) 之间没有人在用 §1 量东西.
- **§1 的实际使用者全是封存族**, 直接导入 §1 的模块:
  - §2: `WeakBridge{Main,Rel,Op,C,Label}`, `GuardCertHt`, `GuardTightAccept`, `GuardBridgeAccept`. 用 `LadderInf*`, `LadderNFTree`, `OrdLabAccept`.
  - §3: `CumHt`, `CumHtCode`, `CumHtAccept`, `CumHtTest`, `WorldTHAccept`. 用 `LadderOrdCode`/`Pos` (序数码), `CrossMClosed`/`CrossMAccept` (`T⊤`).
  - §4: `TLOpsAbs`, `TLOpsTest`, `TLPrefixVal`. 用 `LadderOrdNeg`, `TLCode*`.
  - §5: `LevelFixAccept`, `LevelNoKAccept`, `NoKCertAccept`. 用 `LadderNFTree`.
  - §6: `ValueJudge*` (12 个), `TLEnd{Accept,Top,Cap,Word,Neg}`, `TLBehaveAccept`. 用 `LadderInf*`, `LadderOrdCert`, `CrossM*`, `CrossNext*`.

  这些用法分两种. 一种是**基础设施**: `LadderNFTree._<ᴸ_`, `LadderInfBase`, `LadderOrdCode`, `LadderOrdPos` 作数据类型. 另一种是**比较对象**: `T⊤` 作 "更高" 的参照, 如 `TLOneThm.T⊤≺T̃ᴬ`, `WorldTHAccept`, `TLEndTop`, `TLBehaveAccept`. `RouteSeal` §1 说的 "其余路线的序数值验收都要拿它作尺子", 指的就是这些路线, 现在它们自己也封存了.

### 4.2 `lab-NF` 为什么够当尺子 (判断, 依据是定理的陈述)

1. **定义上就对.** `AGENTS.md` 定义序数值验收为 "树与过基本列验收的树互相 `≼`". `lab-NF : isOTᵉ t ≡ true → Ctbl t → Lab (treeᴴ …) t` 对每个可数 EBO 标准形给出这样一棵树, 无前提 (`WfFsn`, 定理). 再加 `Stage2.Lab-uniq : Lab A t → Lab B t → A ≅ B` (定理), 任何过 `Lab` 的树都 `≅` 于它. 所以 "过基本列验收的树" 在 `≅` 意义下只有一棵, 就是 `lab-NF` 给的那棵.
2. **§1 本来就不是尺子本身.** §1 的值验收 `ValLabPos.VV X t = Σ Y, Lab Y t × X ≼ Y × Y ≼ X`: 是把 §1 的行和一棵带标签的树比, 被量的是 §1 的树, 尺子是那棵带标签的树. 只不过那棵树来自克隆世界 (`OrdLabZCorrespond.Lab`, `OrdLabZLevel`), 而且只到 ψ₀(Ω_{Ω·ω·2}) 有标签. `lab-NF` 把这种树一次给全了, 覆盖一切可数标准形, 包括 ψ₀(Ω_{Ω²}) 和更高处.
3. **范围.** §1 过 `Lab` 的范围到 ψ₀(Ω_{Ω·ω·2}) (`label-Tᴸ`), 过值验收的到 ψ₀(Ω_{Ω·ω²}) (`vv-ω²`); 再往上 (`T⊤`) 只有读法. `lab-NF` 没有上限 (可数部分).
4. **类型能接上.** `lab-NF` 的树在 `OCF.Align.Level.Ordᶜ zero` 里. 主线的闭项经 `HtFeedClosed.ord` 到 `OCF.Free.Level` 的第 0 层, 再经逐构造子换名 `⟪_⟫` 到 `OCF.Align.Level` (`EndLowAccept` §1, 与 `trA`, `fr` 互模拟). 所以主线与 `lab-NF` 比较, 不必经过 §1.
5. **不要归档的版本.** `EboLean` 的 `lab-NF′ : NF t → Ctbl t → Labᴸ (tree (hc …)) t` 在一棵纯布劳威尔树 `Ord` 上, 不导入归档 (本次编译 3 秒, 0.6G). 它与 `WfFsn` 的对应 (`EboLeanCmp.tree≅`) 要归档. 用 `WfFsn` 那一版, 每个新的归档拷贝都要先花约 1 分钟、9.5G 检查归档 (本次实测). 这顺带缓解 RouteReview2 R8 的复现风险.

### 4.3 `lab-NF` 替代不了的, 以及 §1 不可编译会丢什么

| 丢失 | 依据 | 档 | 有多重 (判断) |
|---|---|---|---|
| §2–§6 有 36 个模块直接导入 §1, §1 一旦编译不过, 这几族的入口全部跟着坏, 重开时要先修 §1 | §4.1 的导入图 | 启发 | **重**. "封存以备重开" 的承诺实际上压在 §1 上 |
| 关于 `T⊤` 本身的比较: `T⊤≺T̃ᴬ`, `above-α`, `WorldTHAccept`, `TLEndTop` 等. 换成 `lab-NF` 的 ψ₀(Ω_{Ω²}) 树要先证 `T⊤` 与它 `≈ᵛ`, 这没人做过 (值验收停在 Ω·ω²) | `TLOneThm`, `EmbVV` 入口 "第一个障碍" | 定理 + 判断 | 中. 这些都是封存路线的内部结论 |
| 死路索引里的否定定理: `no-all-Ord`, `all-Ord→LPO`, `viewE→LPO`, `no-tri-code`, `no-step²`, `no-cofinal` (`LadderOrdNeg`), `CrossMNeg.no-⊂⌈⌉`, `CrossMNode.≼↛⊑`, `TLCodeNeg` 的 `exact→LPO`, `binder→LPO`, `no-Good→Str`, `ValLabNeg.no-val-M₂`, `ValLabNegTop.no-val-T⊤`; 还有 `AGENTS.md` 举的 `same-M₂`. 按 "否定路线要有依据" 的规矩, 编译不过就只能算 "曾编译" | `README` 死路索引 §1 十条; `AGENTS.md` | 事实 | **重**. 而且 `no-all-Ord`, `all-Ord→LPO` (单一高度类型含全部可数高度 ⟹ ⊥ 或 LPO) 正是 RouteReview2 P2 要 HtTower 先读的边界 |
| 不读记号的值工具 `EmbVVMain.V-≃`, `Y-val`, `EmbVVForce.force≃`, `EmbVVSame.simᴴ`, `EmbVVGap.succ-gap`: 比较**两棵树侧的树** (层号去头不改值). `lab-NF` 一边是记号的树, 给不出这种比较 | `EmbVV` 入口定理表 | 定理 | 中低. 它们对 `𝕊 : HtB` 参数化, 主线 (`HtFeed`) 不用 `HtB`, 要用只能移植, 读源码就够. 但它们与 R2 的 `MonoStep` (两次折叠的值比较) 是同一类问题, 可作模板 |
| 树侧的行数标杆: `LadderOrd` 第 4 层约 21490 行 (README 口径), RouteReview2 R2、R6 拿它作对照 | README 行数口径 | 事实 | 低. 数字留在文档里, 丢的只是可复现性 |
| 计算代价 | `EndLowAccept` 把 `treeE` 放进 `opaque` (不放会 12G 堆耗尽); §1 的 `OrdLabReadTop` 也撞过 20G | 事实 | 两边都贵, 不构成差别. `lab-NF` 还要 `isOTᵉ t ≡ true` 的证明, 一般用 `refl`; 大项上 `refl` 的代价只有测试 (`WfFsn` §3 算到 `EBOψ 3`) |

**判断.** §1 作为尺子的角色可以正式交给 `lab-NF`: 新的验收只对 `lab-NF` 或 `lab-NF′` 做, 不再引入 §1. 但 §1 的 "保持可编译" 不能因此取消. 它现在承担的是另外两个角色: **封存族的公共依赖**, 和**否定定理的载体**. 这两个角色 `lab-NF` 都接不了. 好在本次实测说明, 维持可编译几乎不花钱: 接口有效时, 除 5 个大堆入口外, §1–§8 共 7 分钟、6G 以内. 真正贵的只有接口失效后的从头检查 (45G, 25G 这一档), 而接口失效只在上游源码改动时才发生.

## 5 建议的政策 (由作者定)

1. **分三类.**
   - (A) **活集依赖**: §3 的 `CumReadBase`, `CumReadCF*`, `CumUpAcceptSim`, `BTBOFull*`, `BTBOVal{Absorb,Base,Dn,Main,Neg,Up}`; §4 的 `NoCumLit`; §5 的 `LevelFixCore`, `LevelFixVal`. 归入活集, 随活集从头复核. 建议在 `RouteSeal` 对应条目注明 "部分模块是活集依赖".
   - (B) **封存但承重**: §1 全族. 理由是 §2–§6 的依赖和死路索引, 不再写 "作第 4 层参照".
   - (C) **其余封存族** (§2, §3 其余, §4 其余, §5 其余, §6, §8): 只做接口检查.
2. **里程碑检查.** 每个里程碑 (作者提交前, 或上游的共享模块有改动时) 按本文 §1 的方法, 对 (B)、(C) 的全部入口跑一次接口检查, 结果追加为本文的新一节, 或记进 `RouteSeal` 的 "编译" 一行. 大堆入口放在没有别的路编译时. 先用 `-M12G` 试, 退出码 251 再按文档的堆跑.
3. **参照角色.** 序数值验收的尺子统一用 `WfFsn.lab-NF` (或不要归档的 `EboLean.lab-NF′`, 要对接 `Ordᶜ` 时经 `EboLeanCmp`); 新的验收文件不导入 §1. `RouteSeal` §1 第一句 "其余路线的序数值验收都要拿它作尺子" 建议改写为 "尺子由 `lab-NF` 接替; 保持可编译是因为封存族依赖与死路索引". 本文不改 `RouteSeal`.
4. **上游改动前先查反向依赖.** 要改共享类型 (如 RouteReview2 R1 的 `H`, 或 `OCF.Free.Level`) 时, 先列出 (B)、(C) 中受影响的入口. 改完若有入口编译不过, 要么修, 要么在 `RouteSeal` 写明 "自 <日期> 起不可编译, 原因 …", 不能静默放着.
5. **从头复核** (删接口) 只在作者要求时做, 或在上游改动后对受影响的族做. 做时一次一族, 不与别的路并行.

## 附: 脚本 (在 scratch, 不入库)

- `run.sh <入口…>`: 顺序编译, 每个入口写一行 `入口 退出码 秒 最大常驻(字节) 检查数 首个错误` 到 `results.tsv`; `--arch` 之后的入口加 `-i <scratch>/sealcheck/arch`.
- `closure.py`, `cover.py`, `live.py`: 正则读 `import` 求导入闭包; 分别查接口时间戳、大堆入口被已通过入口覆盖的模块、活集闭包与封存族的交. 它们都是启发, 精度不如 `importclosure.py` (看不见 `module X = M args` 以外的间接引用, 但对 "导入了哪些模块" 够用).
- 归档拷贝: `archive/src/Mahlo` (树对象 `e8a92400f74b5cdfe5029d4b2f422d1a78668ada`) 拷到 `<scratch>/sealcheck/arch/`, 库文件 `name: sealcheck-arch`, `depend: standard-library-2.4`, `include: .`, `flags: --hidden-argument-puns -W noUnsupportedIndexedMatch`.
