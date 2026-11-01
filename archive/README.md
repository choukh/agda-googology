# 归档 (2026-11-01 冻结)

本目录保存 2026-11-01 确立"交替"总方向之前的全部研究材料. 只读, 不再维护, 不参与默认构建, 其中的强度标签与不可能性判断未经独立验证; 凡与 [probes](../probes/README.md) 中的新工作矛盾之处, 以新工作为准.

- `src/Mahlo/`: 从类型宇宙规则自动提取基本列的 Mahlo 研究 (Object / Notation / Hierarchy / Probe / Inacc / Sources 及全部文档).
- `probes/OCF/`: BTBO 之外的旧 OCF 探索 (Higher, HigherGen, Kovacs, Ord1D, AlphaDec, PastBTBO, Explore, 旧 ROADMAP). 旧 ROADMAP §10 记有交替方向的初版表述, 正式版见 probes/README.md.
- `probes/OCF/Notation/`: 范式 B 的 EBO / Mahlo 表记探针与 Fusion 证书 (2026-11-01 分支 2 完成后归档; 其基本列规则是 probes/OCF/Align 的对照标准).
- `probes/Lens/`: Lens 探针 (含预期编译失败的实验).
- `probes/README.md`: 旧探针目录说明.

模块名保持原样 (如 `Mahlo.*`, `OCF.HigherGen.*`). 需要重新检查时用

```sh
agda --library-file=<含 stdlib/cubical 路径的文件> -i src -i archive/src -i archive/probes <file>
```
