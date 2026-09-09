# Mahlo 历史归档

2026-09-09 按重新确认的核心目标整理。当前研究从 [../README.md](../README.md) 开始。

`Legacy/` 保存此前全部 23 份文档和 22 个 Agda 探针模块；归档前提交为 `dee7ebc`。历史内容保留，每份文档加归档提示，代码迁移为 `Mahlo.Archive.Legacy.*` 命名空间，更新导入和路径以保持可编译与可追溯。

| 归档内容 | 原用途 | 归档原因 |
|---|---|---|
| `Legacy/Universe/`、`WellOrder/`、`Evidence/*.agda` | 外部闭包、反射与良基性辅助实现 | 尚未从宇宙规则生成基本列，不作为当前已完成模块 |
| `Legacy/Notation/`、`Fundamental/` | 手写参考记号与候选基本列 | 目标答案由分析者提供，不能代替自动提取 |
| `Legacy/Growth/` | 通用 FGH 输出接口 | 依赖尚未生成的序结构与证书 |
| `Legacy/Extraction/` | 预给可数分支树的提取探针 | 输入不是完整宇宙规则，未证明序数基本列语义 |
| `Legacy/ROADMAP.md`、各 `*-PLAN.md`、`CRITICAL-PATH.md` | 历次执行路线 | 已被新的关键路线取代 |
| `Legacy/DEFINITION-FIRST.md`、`UNIVERSE-AND-SEQUENCES.md` | 先写定义的旧阶段 | 预先固定了候选基本列，不约束当前输出 |
| `Legacy/FINDINGS.md`、各 `*-ITERATION.md`、`Evidence/*.md` | 研究记录、反射审计、可行性及增长探针 | 保留证据和限制，不把局部进展当成核心提取进展 |
| `Legacy/THEORY.md`、`RULE-MATRIX.md`、`ENDPOINT.md`、`CALIBRATION.md`、`README.md` | 旧输入、验收与入口 | 有效要求重新整理在当前 INPUT、CONTRACT 等文档中 |

旧文档中的完成状态、下一步和命令结果描述的是当时工作。路径已尽量更新到归档位置，历史数学论证未因归档重新获得认证。

归档代码继续纳入仓库 `tools/check-src.sh` 的源码检查，保持可复现；不参与成品文档发布。未来复用某个引理时，应在当前文档中说明它解决的确切提取义务，不整体恢复旧路线。
