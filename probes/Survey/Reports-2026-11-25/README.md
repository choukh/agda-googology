# 2026-11-25 的留档索引

研究负责人（Fable 5.2）当天派出的各路。简报与回报是原文；主审复核过的结论以 [LOG](../../LOG.md) 11-25 各段为准。模块原件在 `attachments/`（`.agda.txt`），重建脚本在 `../scripts/`。

| 路 | 文件 | 模型 | 结果一句话 | 状态 |
|---|---|---|---|---|
| 越过 BTBO 的第一步 | [KJ](KJ-越过BTBO的第一步.md) | Opus 5.5（续做） | `EBOᶜ` 严格高于 BTBO，且不低于参照链从 BTBO+1 起步的极限；从 BTBO 本身起步不成立 | 已复核；入口 [W4CountableLower](../W4CountableLower.lagda.md) |
| 第十五次独立审查 | [RR15](RR15-第十五次独立审查.md) | Fable 5.2 | 先读定义的盲审；换基（审查称换参数）在塔上的编译核心；倾向与负责人相近 | 已复核；[预览](attachments/RR15-R15-preview.md) |
| 沿层号路径的字面单调 | [KQ](KQ-沿层号路径的字面单调.md) | Opus 5.5 | 孩子族对右加法的字面单调在塔与规范读回上保持，被折叠破坏（规范实例上的否定） | 已复核；入口 [W4Rebase](../W4Rebase.lagda.md) |
| 依赖分支与换基的一行 | [W6](W6-依赖分支与换参数.md) | Opus 5.5 | 候选 W6：换基落成折叠的一行；真实运行里仍回退的一处在读回层号上 | 已复核；候选，不替换 W4 |
| 仓库和研究记录的卫生整理 | [Hyg](Hyg-卫生整理.md) | Opus 5.5 | 改 6 个文件 105 处（路径 1，表格 104），其余只列出；[改动清单](attachments/Hyg-changes.tsv) | 已逐文件核对 |
| 清理 .agdai、死代码死文件，修复悬空引用 | [Cln](Cln-清理与悬空引用.md) | Opus 5.5 | 删 5882 个文件约 3.03G（全是可再生的产物，另加一个被跟踪的空导入模块）；修 79 个链接目标；4 个脚本删 6 个没被调用的函数；候选 130 条只列出（[删除](attachments/Cln-deleted.tsv)、[改动](attachments/Cln-changes.tsv)、[候选](attachments/Cln-candidates.tsv)） | 已按基线逐文件核对 |
| 整理记忆和 AGENTS.md | [Mem](Mem-记忆与AGENTS.md) | Opus 5.5 | AGENTS.md 只做指向更新与格式整理，纲领与目标两节逐字未动；记忆一节的原文不留在仓库 | 已按基线逐文件核对 |
| 重复附件去重；编译不过的草案移到 archive | [Arc](Arc-去重与移到archive.md) | Opus 5.5 | 六组重复各删一份并改 8 处引用；4 个自称草案且编译不过的模块移到 `archive/`（研究负责人另移 1 个）；导入已归档 Mahlo 的三个模块没有移（[清单](attachments/Arc-changes.tsv)） | 已用 git 逐项核对 |

候选 W5 的模块（`attachments/W5-*.agda.txt`）是 11-25 上午审计阶段整理的，入口 [W5Candidate](../W5Candidate.lagda.md)。
简报的公共约束模板：[COMMON-公共约束](attachments/COMMON-公共约束.md)。朝 EBO 的派发候选与接手步骤：[接手文档](../EBO-接手与派发候选-2026-11-25.md)。
