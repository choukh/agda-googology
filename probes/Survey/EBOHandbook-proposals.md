# EBOHandbook 的修改提议 (待统筹者与作者审)

> 2026-11-05. 依据 [EBOHandbook.md](EBOHandbook.md). 本文件只提议, 没有改 `AGENTS.md`, 记忆, 地图或日志. 每条: 目标, 建议的原文, 理由 (指向手册的节). 原文按目标文件的文风写 (AGENTS 用半角标点加空格).

## 2026-11-07 状态核对

本篇是历史提案，标题“待审”不代表全部内容今天仍待审。本次对照
[现行 AGENTS](../../AGENTS.md)：A1、A2、A3、A4、A5、A6 的主要主题
均已有对应条款，执行以 AGENTS 的实际文字为准，**不是整段原提案
逐字采纳**。例如 A2 的 1.35 内存系数仍是建议，现行规则只要求留余量；
A6 中有关性能手册副本的措辞已被作者“不进本仓库”的决定取代。
B 节的记忆修改不能仅凭本篇认定已经执行，本轮没有核查或修改仓库外记忆。
本次只补状态，不修改 AGENTS，也不把历史建议升级为新规则。

## A. `AGENTS.md`

### A1. "Agda" 一节: 实际生效的选项与 scratch 文件

- **位置.** "Agda" 一节, 第一条之后.
- **原文.**
  > - 仓库的 `agda-googology.agda-lib` 与 `probes/probes.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`, 所以仓库模块实际都带这些选项. 仓库外 (scratch) 的实验文件要自己写上同样的选项, 否则导入仓库模块报 `InfectiveImport`. 构造子不能作隐式参数的 pun, 写 `{a = zero}`. 不开 K, 实验文件也不开.
- **理由.** 手册 4.1: 提取到 68 次 `InfectiveImport`, 83 次 `InvalidPun.Constructor`; "不开 K" 现在只在记忆里.

### A2. "Agda" 一节: 堆上限, 退出码, 并行

- **位置.** "Agda" 一节, "编译" 那条之后.
- **原文.**
  > - 每次 agda 都带 `+RTS -M<n>G -RTS`. 退出码: 0 通过, 42 类型错误或有洞, 251 堆耗尽 (不是类型错误, 也不是通过), 124 被 `timeout` 杀掉. 编译失败那一轮的 `--html` 与切片结果作废.
  > - 并行时每个智能体同时只跑一个 agda, 各路堆上限之和乘 1.35 不超过约 56G (64G 机器). 别的智能体在编译时, 不对共享模块用 `--ignore-interfaces`, 只删自己模块的 `.agdai`.
  > - 堆墙多出在验收与测试文件里比较具体闭项的地方: 陈述逐字写, 不用别名; 沿良基证明算出的大参照树放 `opaque` 并导出接口; 经非单射的头求解的隐式参数显式写出. 详见 `probes/Survey/EBOHandbook.md` 第 4 节与 Bedrock 项目的 `dev/cubical-agda-performance.md` (作者定不进本仓库).
- **理由.** 手册 4.2 到 4.4, 4.6. 现在这些只在简报与 `RouteSeal` 里; 1.35 的系数来自 Bedrock H-3, 我们没量过, 是保守的取法 (可以改成 "之和不超过 64G", 那是现在的做法).

### A3. "结论的写法": 前提可满足, 措辞

- **位置.** "结论的写法" 一节, "否定路线要有依据" 之后.
- **原文.**
  > - **前提要可满足.** 否定定理与条件定理的每个前提, 给一个实例或说明为何可满足; 前提矛盾的定理什么也没说 (`InaccStrikeFixed`). 以证书为前提的增长或覆盖结果, 先确认证书有居留.
  > - **比喻和方向性的形容不进结论.** "长得一样", "更自然", "严格更弱", "只差" 这类说法, 要么换成定理的陈述, 要么标成判断并说出测到哪里. 跨口径的数字不并列.
- **理由.** 手册 1.2, 3.9, 3.13. 现在前一条在记忆 `feedback-route-negation-audit` 与简报里, 后一条无处.

### A4. 新增一节 "与作者协作" (短)

- **位置.** "结论的写法" 之前.
- **原文.**
  > ## 与作者协作
  >
  > - 汇报先说对纲领与目标意味着什么, 再给定理; 第一次出现的内部名字配一句白话. 强度写 ψ₀(Ω_x), x 用 Ω 的算术, 不用 ψ₁.
  > - 要作者拍板的路线选择用选项工具, 中文, 推荐项放第一; 多选只放互不依赖、文件不相交的路. 不把 "先提交" 当默认推荐.
  > - 作者的问题多是为了理解, 不是改方向的指令; 要改派发或规则, 用选项工具问.
  > - 在跑的路回来并复核后再汇报.
- **理由.** 手册 1.1, 1.3, 2 (第 1, 3, 4, 5, 10 条). 现在分散在记忆里或无处; 子智能体看不到记忆, 只看 AGENTS.

### A5. 新增 "子智能体的安全约定"

- **位置.** "Agda" 一节末尾, 或单列一节.
- **原文.**
  > - 子智能体只在自己的临时目录与自己前缀的新文件里写; 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp`, 不装包, 不提交. 浏览器工具被内容过滤拦下时不绕开, 改读别的来源或报告.
- **理由.** 手册 2 (第 17, 18 条), 3.14, 5.3: 误删未跟踪文件 `probes.tmp`, 写出 `/tmp/null`, 绕开浏览器内容过滤, 都发生过. 现在只在简报里.

### A6. "目录" 一节: 指向手册

- **位置.** "目录" 一节, `probes/Survey/` 那条.
- **原文.**
  > - `probes/Survey/`: 查文献先看 `OrdinalNotationsGuide.md`, 查外部代码先看 `CodeGuide.md`, 工程与协作的经验先看 `EBOHandbook.md` (Agda 性能另见 Bedrock 项目的 `dev/cubical-agda-performance.md` (作者定不进本仓库), 拷自 Bedrock, CC-BY-NC-SA-4.0), 不要重新调研.
- **理由.** 让子智能体能找到手册.

## B. 记忆 (统筹者的记忆目录)

### B1. 新文件 `ebo-handbook.md` 与索引一行

- **原文 (文件).**
  > ---
  > name: ebo-handbook
  > description: 2026-11-05 蒸馏出的开发手册 probes/Survey/EBOHandbook.md (协作, 隐含规则, 幽灵清单, 工程, 子智能体管理, 估计与实际); 每批子智能体对话结束后用 probes/Survey/scripts/handbook/run.sh 增量再蒸馏
  > metadata:
  >   type: reference
  > ---
  >
  > 手册在 `probes/Survey/EBOHandbook.md`, 改规则的提议在 `EBOHandbook-proposals.md`. 作者 2026-11-05 要求本对话及以后每个子智能体对话都蒸馏: `sh probes/Survey/scripts/handbook/run.sh <scratch>/handbook --since <上次日期>`, 读 `digest/` 下的摘要, 把新经验补进手册. 状态文件 `probes/Survey/scripts/handbook/state.json` 记已处理的记录, 进仓库.
  >
  > **How to apply:** 派活前读手册第 5 节的简报模板与复核清单; 编译爆内存先看第 4 节; 汇报前对照第 1.2 节 (作者会追问哪一档).
- **索引一行.** `- [EBO 开发手册](ebo-handbook.md) — 2026-11-05 蒸馏: 协作, 隐含规则, 幽灵, 工程/OOM, 子智能体, 估计与实际; 每批对话后用 run.sh 增量再蒸馏`
- **理由.** 作者要求统筹者 "审核之后更新 AGENTS.md 和记忆, 使它们参照 handbook".

### B2. 更新 `feedback-route-choice-ask.md`

- **追加.**
  > **2026-11-05 补充 (手册):** 问题与选项用中文 (11-04 晚曾写成英文). 作者 67 个子问题中 57 个选推荐项; 不选推荐的几次偏向: 不为提交打断 (两次 "直接攻, 暂不提交"), 更多并行, 更严的形式约束 (不开 K), 分档写明. 推荐项不要默认 "先提交".
- **理由.** 手册 1.3.

### B3. 新文件 `feedback-questions-not-instructions.md`

- **原文.**
  > ---
  > name: feedback-questions-not-instructions
  > description: 2026-11-05 作者问完一串 "如果...怎么办" 后说 "以上讨论不改变任何事, 请继续": 作者的问题多为理解, 不是改方向的指令; 另有 "等结果回来再汇报", "能先派的就先派"
  > metadata:
  >   type: feedback
  > ---
  >
  > 作者 2026-11-05 原话: "以上讨论不改变任何事, 请继续". 同日: "能先派的就先派吧"; 11-04 采纳 "等结果回来再汇报".
  >
  > **How to apply:** 回答作者的问题时不顺手改派发, 规则或路线; 真要改, 用选项工具问. 能派的独立任务立刻派. 在跑的路不做中途汇报, 回来复核后一起报.
- **索引一行.** `- [问题不是指令](feedback-questions-not-instructions.md) — 2026-11-05: 作者提问多为理解, 不改方向; 能派先派; 等结果回来再汇报`
- **理由.** 手册 2 第 1 到 3 条, 现在无处.

### B4. 更新 `feedback-parallel-dispatch.md`

- **追加.**
  > **2026-11-05 补充 (手册):** (1) 堆预算: 各路 `-M` 之和乘约 1.35 留在 64G 内 (五路各 12G 已到边); 大堆单路 (`LadderOrd` 45G, `CrossM` 25G) 只在别的路不编译时跑. (2) 别人编译时不对共享模块用 `--ignore-interfaces`, 只删自己的 `.agdai`. (3) 派发前列出每路的第一个障碍会落在哪个引理上; 撞同一处的合并 (RouteReview2: KVal, EndLow, HtCross 都在等 `MonoStep`). (4) 简报里的禁令要能追到作者或 AGENTS, 不自己加.
- **理由.** 手册 4.2, 4.3, 5.2.

### B5. 更新 `btbo-barrier-theorem.md` 的 "编译环境" 段

- **改为.**
  > **编译环境:** 见 probes/Survey/EBOHandbook.md 4.1 (库文件, 实际生效的库选项 `--cubical-compatible --guardedness --hidden-argument-puns`, scratch 文件要补同样选项, 归档 OT_I 副本的配方). 重启后 /private/tmp 清空, 先重建库文件并用小模块验证.
- **理由.** 环境说明不该埋在壁垒定理的记忆里; 手册已收.

### B6. 更新 `feedback-loc-conventions.md`

- **追加.**
  > **2026-11-05 EboLean 更正:** 切片看不见模块应用 (`import M args`, 带参数的模块别名), 记号侧第 3 层旧报 6473 少算约 1470 行, 同口径重算旧版 7867 (加标签 7941); 精简版 `EBO-tree′` 6524 (加标签 6544), 其中约 5250 行是 Setzer 的 OT_I 机器, 是上界不是最小值. "记号侧层 3 未做" 的旧说法已过时 (WfFsn 完成). 比较两边前先同口径重算; 表里注明每层保证什么 (记号侧层 3 = 良基, 树侧层 3 = 合法).
- **理由.** 手册 3.10, 7; RouteReview2 §4 第 5 条, P6.

### B7. 更新 `agda-pitfalls-inacc.md`

- **追加.**
  > **2026-11-05 (EBO 阶段, 详见 EBOHandbook 4.2 到 4.5):** 16. 比较两个写法不同的证书计值 `forceᴺ _ (G …)` 会展开整条证书 (20G 堆耗尽): 陈述逐字写, 不用别名. 17. 沿良基证明算出的参照树 (`treeE`) 放 `opaque`, 否则 12G 堆耗尽. 18. `uc-app` 的 `{y}{z}` 不写出 >10 分钟, 写出 4 秒. 19. scratch 文件导入仓库模块要补库的 `--guardedness --cubical-compatible --hidden-argument-puns`, 否则 `InfectiveImport`. 20. 退出码 42 类型错误或有洞, 251 堆耗尽, 124 timeout. 21. 对照 Bedrock 的性能手册 Bedrock 项目的 `dev/cubical-agda-performance.md` (作者定不进本仓库) (规则 ID 如 C-1, S-1, I-1, H-12).
- **理由.** 这条记忆是 "Agda 实测坑" 的入口, 新的坑应当在这里能找到.

### B8. 新文件 `reboot-recovery.md` (或并入 B1)

- **原文.**
  > 重启电脑前用 TaskStop 停掉子智能体. 重启后 /private/tmp (scratch: 库文件, 脚本, 草稿) 清空, 仓库与 probes/_build 接口都在. 先重建库文件, 用一个小模块验证编译; 再给每路 SendMessage: "电脑重启导致你被暂停, 现在恢复, 任务和约束不变. 不要重复已做的工作; 先检查 <前缀>* 和你的临时目录还剩什么. 编译命令和堆上限不变". 生成与统计脚本必须在 probes/Survey/scripts/, 不能只在 scratch.
- **理由.** 手册 5.5; 两次重启 (11-02, 11-04) 都靠临场处理, 协议无处.

## C. 其他 (可选)

### C1. 地图 `probes/README.md` "工作方法" 一节

- **追加一条.** `- 工程与协作的经验 (编译爆内存, 复核清单, 子智能体简报模板) 看 Survey/EBOHandbook.md; Agda 性能的一般规则看 Bedrock 项目的 `dev/cubical-agda-performance.md` (作者定不进本仓库).`

### C2. 许可证

- Bedrock 项目的 `dev/cubical-agda-performance.md` (作者定不进本仓库) 是 CC-BY-NC-SA-4.0, 版权 2026 Bedrock Institute, 文首保留了署名与 SPDX 行. 本仓库也用 CC BY-NC-SA 4.0, 条款兼容; 是否在仓库根的 README 或许可证说明里注明这份第三方文件, 由作者定.
