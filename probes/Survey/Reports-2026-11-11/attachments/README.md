# 附件: 临时目录里的试验文件 (不是成果)

> 这里存的是执行方在临时目录里写的一次性试验, 原样拷贝, 后缀加了 `.txt`, 免得被当成仓库的模块. 它们不在 `probes/OCF` 里, 不被任何模块导入, 不算成果; 留着是因为作者要对 "是否改块" 作裁决, 而临时目录重启后会丢.

| 文件 | 来源 | 内容 | 主审核对 |
|---|---|---|---|
| `YiOmNeg-VariantA.agda.txt` | 第 4 步第一站否定路 (O5) | 块的变体甲: `Pre` 与 `Kid` 在 `lc` 层号上的守卫改成无关 (放进带无关字段的记录). 由执行方的脚本从 `RR5IrrCore` 与 `RR5IrrCheck` §1 改写 | 2026-11-11 在原临时目录里重编, 退出码 0 (纯 `.agda`, 选项同仓库) |
| `YiOmNeg-VariantB.agda.txt` | 同上 | 块的变体乙的最小骨架: ℕ 极限自带相邻项的路径, 守卫只剩路径并处处无关. 没有结点的合法性, `Nested`, 折叠 | 同上, 退出码 0 |

| `Review6-R6Strict.agda.txt` | 第六次独立审查 | `top-branch→lpo-strict : TopBranch → LPO`, 探针换成严格递增的 (不再是最终常值的极限); 记录 `TopBranch` 原样导入 | 2026-11-11 在原临时目录里重编, 退出码 0 |
| `Review6-R6Tail.agda.txt` | 同上 | `TailBranch`: 分支域取目标坐标之上的尾部, 守卫相关; `tail-model` 不要神谕, 满足保留律与折叠律 (只是模型, 不是折叠). `tail-legal`, `tail-first`: 在现在的块里抬高 Ω 结点的下界仍合法, 主干不变 | 同上, 退出码 0 |
| `Review6-R6Diag.agda.txt` | 同上 | 固定对角的闭项: `T⁺ᵈ = closedᵐ (suc (read0 T₃ᵐ)) …` 与再回灌一次的 `T⁺ᵈ₂`, 都合法; 没有值 | 同上, 退出码 0 |
| `Review6-preview.txt` | 同上 | 审查者在读各路结论之前写下的看法 (V1 到 V7), 原样 | 没有编译内容 |

重编的办法: (后三份 `Review6-*.agda.txt` 导入仓库模块, 编译时还要 `-i <仓库>/src -i <仓库>/probes`.) 拷到一个空目录, 去掉 `.txt`, 旁边放一个 `.agda-lib` (依赖标准库, `include: .`, flags 同仓库的 `probes.agda-lib`), 在该目录下跑 agda. 这两份文件的读法与编译事实见 [YiOmNeg](../YiOmNeg.md) 回报原文 §5 与 `probes/LOG.md` 的对应一节.
