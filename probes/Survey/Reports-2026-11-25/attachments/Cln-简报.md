# Cln: 清理 .agdai, 清理死代码死文件, 修复悬空引用 (前缀 Cln, 工作目录 <实验目录>/cln)

作者的指令原话: "清理.agdai，清理死代码死文件，修复悬空引用". (同一句里的 "整理记忆和agents.md" 由另一路同时在做: 你不碰 `AGENTS.md` 与记忆目录.) 研究负责人 (另一个会话) 会在你回来后拿基线逐文件核对, 所以每一处删除与改动都要记进清单.

仓库根: <仓库> . 先读 <仓库>/AGENTS.md 的 "目录", "Agda", "Git" 三节, 再读上一轮卫生整理的回报 <仓库>/probes/Survey/Reports-2026-11-25/Hyg-卫生整理.md (里面已有该删的候选、断链清单与未跟踪文件的清点, 不要重做已经清点过的部分, 直接接着做).

## 最要紧的一条事实

仓库里约 3500 个文件**没有进 git** (未跟踪). 未跟踪的文件删了找不回来. 所以: **不可再生、又未跟踪的文件一律不删**, 认为是死文件的只列进候选清单. 用 `git ls-files` 判断一个文件是否被跟踪.

## 一、清理 .agdai 与构建产物 (直接删)

可再生的产物, 直接删, 不论是否被跟踪:
- 仓库内一切 `*.agdai` (`.git` 除外);
- 根目录 `_build/` 与 `probes/_build/` 下的全部内容 (接口文件, html, dot, css, json, 日志, 各审计子目录), 删空后目录本身也删;
- `__pycache__/` 目录与 `*.pyc`;
- 未跟踪的 `.DS_Store` (被跟踪的不动).
删之前把清单写进 `<实验目录>/cln/Cln-deleted.tsv` (路径<TAB>字节数<TAB>类别). `.agdai` 太多, 可以按目录汇总成一行 (目录, 个数, 总字节数).

## 二、死文件

一个文件算 "死的", 要**同时**满足 (a) 与 (b):
(a) 没有被引用: 不被任何 Agda 模块导入; 也不被任何记录提到 (`probes/README.md`, `LOG.md`, `RESULTS.md`, 两份 `STATUS-ARCHIVE`, `probes/Survey/` 下各 md 含留档目录, `AGENTS.md`, 各脚本). 按文件名, 不带扩展名的名字, 模块名三种写法检索.
(b) 下列之一: 内容为空, 或只有模块头与导入; 与另一个被引用的文件内容完全相同; 是某个仓库内脚本的生成物; 文首自称草案、废弃或未完成, 且你实测它编译不过 (退出码 42; 251 是堆耗尽, 不算).
处置:
- 满足 (a)(b) 且**被 git 跟踪**: 删, 记进 `Cln-deleted.tsv`, 写明证据 (检索命令与结果, 退出码).
- 满足 (a)(b) 但**未跟踪**: 不删, 记进 `Cln-candidates.tsv` (路径, 证据).
- 只满足 (a) 的叶子模块不是死文件: 这个仓库里多数定理模块都没有被别的模块导入, 它们是研究记录. 不删, 不列.

## 三、死代码

- 脚本 (`probes/Survey/scripts/` 下的 `.py`, `.sh`): 永不被调用的函数, 永不执行的分支, 注释掉的大段旧代码, 可以删; 前提是改后 `python3 -m py_compile` (或 `bash -n`) 通过, 且你有十足把握. 记进 `Cln-changes.tsv`.
- Agda 模块内部 (未使用的定义, 注释掉的定义): **只列出, 不改**. 改它们会改动研究记录里的数学文件. 把最明显的若干处记进 `Cln-candidates.tsv`, 不必穷举.

## 四、悬空引用

1. **Markdown 链接** (`probes/` 下的 `.md` 与 `.lagda.md` 围栏外的文字, 含留档目录): 目标不存在时, 若正确目标唯一可确定就修成正确的相对路径. 可确定的情形: 同名文件在仓库里只有一个; 目标被早先的脱敏写成了 `<仓库>/…` 占位, 可换算成相对路径; 链接是按另一个目录 (如 `Survey/Lead/`) 写的相对路径, 可换算. 不可确定的, 不改, 记进候选清单.
2. **记录里提到的路径**: `probes/README.md`, `RESULTS.md`, `probes/Survey/` 顶层各 md, `EBOHandbook.md` 里以反引号或 "见 …" 提到的仓库内文件路径, 指向不存在的文件时同样处理. `LOG.md` 与留档的回报是过程记录: 链接目标可以修, 文字不改.
3. **Agda 导入**: 扫描 `probes/` 与 `src/` 里各模块的导入 (标准库与 cubical 的不算), 分三类: 仓库内有对应文件; 只在留档附件 `*.agda.txt` 里有 (这是有意的: 由 `probes/Survey/scripts/` 下的 materialize 脚本抄成实验目录后编译, 不算悬空); 哪里都没有. 第三类只列出 (文件, 缺的模块), 不改代码.
4. 在 `.lagda.md` 模块里只改代码围栏以外的文字, 围栏行与围栏内一字不动.
5. 你在第二步删掉的文件, 删完后再检索一次, 确认没有留下指向它的引用.

## 硬约束

- 不碰 (不删, 不改): `src/`, `archive/`, `.git`, `.claude/`, `public/`, `tools/`, `AGENTS.md`, 记忆目录, 各 `attachments/` 目录里的文件, 三个定稿入口 (`probes/Survey/W4CountableLower.lagda.md`, `W5Candidate.lagda.md`, `W4Rebase.lagda.md`) 与它们的 materialize 脚本, `AGENTS.md` 点名的脚本 (`depslice.py`, `importclosure.py`, `agentreport.py`).
- 留档 (`probes/Survey/Reports-*/`, `probes/Survey/Lead/`) 里的文件不删; 允许的改动只有修链接目标.
- 不改任何结论, 定理, 判断, 数字或措辞; 不改 Agda 代码.
- 不做任何 git 写操作 (add, commit, stash, checkout, restore, clean, reset, rm 都不做); 删除用普通的文件删除. git 的只读命令可以用.
- 不写 `/tmp`, 不 `pkill`, 不装包. 临时文件只放工作目录. 仓库文件里不写本机路径.
- 同时只跑一个 agda, 堆上限 6G.
- 有疑问的不删不改, 列出来.

## 验收 (你自己先做)

1. 三个定稿入口重新编译, 都应退出 0 (这会重新生成一部分接口文件):
   `python3 probes/Survey/scripts/w4klower/materialize.py <你的目录>/k1` 后编译 `probes/Survey/W4CountableLower.lagda.md`; `w5cand` 与 `W5Candidate`, `w4rebase` 与 `W4Rebase` 同理 (各用新目录 k2, k3).
   编译命令 (从仓库根): `cd <仓库> && timeout 3000 agda --library-file=<实验目录>/libraries -l standard-library-2.4 -l cubical-0.9 -i src -i probes -i <目录> <文件> +RTS -M6G -RTS > <你的目录>/<名字>.log 2>&1; echo $?`
   退出码 0 通过, 42 类型错误 (先看日志首行是不是 LibraryError), 251 堆耗尽, 124 超时. 报退出码时不要经过管道.
2. 你改过文字的每个 `.lagda.md`: 确认围栏行的条数与位置没有变.
3. 最后再清一次 `*.agdai` 与两个 `_build`, 使结束时仓库里没有 `.agdai`. 报出前后两次清理各删了多少个、多少字节.
4. 用基线核对: `<实验目录>/cln-baseline.sha` 是开工前仓库里每个文件的校验和 (shasum, 路径相对仓库根, 不含 `.git`, `_build`, `*.agdai`). 基线里有而现在没有的文件, 必须每一个都在 `Cln-deleted.tsv` 里; 内容变了的文件, 必须每一个都在 `Cln-changes.tsv` 里 (`AGENTS.md` 除外, 那是另一路在改). 把核对结果报出来.

## 交付

- `<实验目录>/cln/Cln-deleted.tsv`, `Cln-changes.tsv` (文件<TAB>类别<TAB>处数<TAB>说明), `Cln-candidates.tsv` (未跟踪的死文件候选; Agda 内部的死代码; 悬空导入; 没修的悬空引用; 各带证据).
- 最终消息就是回报原文, 中文: 一句话结论 (删了什么各多少, 腾出多少空间, 改了几个文件几处); 四类各一小节, 数量在前例子在后; 验收四条的结果; 没有把握的地方. 区分 "已核实" 与 "判断".
