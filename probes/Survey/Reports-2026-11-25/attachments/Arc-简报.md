# Arc: 重复附件去重; 编译不了的草案与导入已归档 Mahlo 的模块移到 archive/ (前缀 Arc, 工作目录 <实验目录>/arc)

作者 2026-11-25 经选项定了两件清理, 这一路只做这两件. 选项原文:
- "删重复附件: 6 组内容完全相同的附件各删一份 (共 21K) … 删了要改引用".
- "再清文件一级: 把自称草案且编译不过的模块、导入已归档的 Mahlo 而编译不了的 3 个模块移到 archive/ (不删); 不动模块内部. 要逐个实测编译".

仓库根: <仓库> . 先读 <仓库>/AGENTS.md 的 "目录", "Agda", "Git" 三节, 再读上一轮的回报 <仓库>/probes/Survey/Reports-2026-11-25/Cln-清理与悬空引用.md 与 Hyg-卫生整理.md (六组重复与悬空导入在那里已经清点过).
现在仓库的全部文件都已提交 (`git ls-files` 里都有), 所以删与移都能从 git 找回; 但每一处仍要记进清单, 研究负责人回来后逐项核对.

## 一、重复附件 (六组, 只处理这六组)

上一轮清点的六组: `probes/Survey/Reports-2026-11-24/attachments/` 里的 `M4-KOpPow` 与 `M4b-KOpPow`, `M2-KIface` 与 `M2v2-KIface`; `probes/Survey/Lead/attachments/` 的 `B10Join`, `B11Join` 各与 `Reports-2026-11-16/attachments/` 里的对应文件; `probes/Survey/scripts/scafladder/` 与 `scripts/uniform5/` 里的两份 `*-Sb2.patch`.
1. 先用校验和确认每组确实逐字节相同. 不相同的那组不动, 报出来. 若另外发现别的重复, 只列出, 不处理.
2. 每组留一份, 删一份. 留哪份: 被脚本实际读取的那份优先 (`scripts/w4klower/materialize.py` 等读的是 `M4b-`, `M2v2-`); 其次留被引用得多的那份.
3. 改引用: 全仓库检索被删那份的路径与文件名. Markdown 链接的目标改到留下的那份; 文字里以反引号写出的该文件路径也改到留下的那份 (只改路径这几个字符, 别的字不动); 脚本里读取被删文件的, 改成读留下的那份 (相对路径), 改后用 `bash -n` 或 Python 的 `compile()` 查语法 (不要用 `py_compile`, 它会在仓库里写 `__pycache__`). 写成通配的提法 (如 "`M4-KOp*`") 不改.
4. 改完后再检索一次, 确认没有指向被删文件的引用.

## 二、移到 archive/

目的地: `archive/probes/` 下与原来相同的相对路径 (如 `probes/OCF/Align/X.lagda.md` 移到 `archive/probes/OCF/Align/X.lagda.md`). 用普通的文件移动, 不用 git 命令. 只移不删, 文件内容一字不改.

**(a) 导入已归档 Mahlo 的三个模块**: `WfScoutPull`, `WfScoutTau`, `WfTauNF` (在 `probes/` 下找到它们). 逐个实测: 编译应当退出 42 且日志指出找不到 `Mahlo.…` 模块的源文件. 确认没有别的模块导入它们 (有的话, 那个导入者也编译不了: 报出来, 一并按同样的办法实测后移走). 不满足这两点的不移, 报出来.

**(b) 自称草案且编译不过的模块**: 在 `probes/` 下的 `.lagda.md` 里找文首 (第一个代码围栏之前) 自称草案、废弃、未完成、编译不过或堆耗尽的模块 (已知的两个: `OCF/Align/BoundedCompletionStageWf`, `BoundedCompletionStageWfLabel`; 其余由你检索). 对每个候选:
- 先查有没有别的模块导入它; 被导入的不移, 报出来.
- 实测编译 (命令见下, 6G, 每个限 900 秒). 退出 0 的不移. 退出 42, 251 或 124 的算 "编译不过", 移走, 并把退出码与日志首个错误记进清单.
- 候选超过 12 个时, 先做这 12 个里文首说得最明确的, 其余只列出.

**移走之后**: 全仓库检索指向它的 Markdown 链接, 把目标改成新位置的相对路径; 文字里只写模块名的提法不改. `probes/LOG.md` 与留档的回报里只改链接目标, 不改文字.

## 编译命令 (从仓库根; 同时只跑一个 agda)

`cd <仓库> && timeout 900 agda --library-file=<实验目录>/libraries -l standard-library-2.4 -l cubical-0.9 -i src -i probes <文件> +RTS -M6G -RTS > <实验目录>/arc/<名字>.log 2>&1; echo $?`
退出码 0 通过, 42 类型错误或缺模块 (先看日志首行是不是 LibraryError: 是的话是环境问题, 停下报告), 251 堆耗尽, 124 超时. 报退出码时不要经过管道. 接口文件此前已全部清掉, 所以每次都是冷编, 会比较慢.

## 硬约束

- 只做上面两件. 不删除六组之外的任何文件, 不移动 (a)(b) 之外的任何文件.
- 不碰: `src/`, `.git`, `.claude/`, `AGENTS.md`, 记忆目录, 三个定稿入口与 `scripts/w4klower`, `w5cand`, `w4rebase` 三个脚本目录. `archive/` 里只新增移进来的文件, 已有的文件不动.
- 不改 Agda 代码, 不改任何结论、数字或措辞. `probes/README.md`, `LOG.md`, `RESULTS.md`, `IdeaLedger.md`, 接手文档里只允许改链接目标与反引号里的那一个文件路径.
- 不做任何 git 写操作 (add, commit, mv, rm, stash, checkout, restore, clean, reset 都不做); git 的只读命令可以用.
- 不写 `/tmp`, 不 `pkill`, 不装包. 临时文件只放工作目录. 仓库文件里不写本机路径.
- 有疑问的不动, 列出来.

## 收尾与交付

1. 结束前清掉仓库里重新生成的 `*.agdai` 与 `_build` 目录 (只清这些可再生的产物), 使仓库里没有 `.agdai`.
2. `git status --short` 应只有: 被删的六个文件, 被移走的模块 (原位置消失, `archive/` 下新增), 以及改了引用的文件. 把它逐类对上你的清单.
3. 清单 `<实验目录>/arc/Arc-changes.tsv`: 动作 (删/移/改引用)<TAB>文件<TAB>去向或留下的那份<TAB>证据或说明.
4. 最终消息就是回报原文, 中文: 一句话结论; 六组各留了哪份删了哪份、改了几处引用; (a)(b) 每个候选的实测结果 (退出码逐字, 首个错误一行) 与去留; 没动的与原因; 验收结果. 区分 "已核实" 与 "判断".
