# 当前文献依据与适用边界

2026-09-09 核对。当前未确认一篇完成“Mahlo 宇宙规则 → 自动基本列 → 精确 FGH 校准”全链条的文献；未找到不等于不存在。下列资料按它们在本目标中的用途保留。

| 来源 | 使用位置 | 不能直接推出 |
|---|---|---|
| [Setzer, Extending Martin-Löf Type Theory by One Mahlo-Universe](https://csetzer.github.io/articles/mahlo.pdf)，§4–5 | 原始 Mahlo 规则及独立序数分析依据 | 已有从规则自动提取基本列的算法 |
| [Setzer, Universes in Type Theory Part I](https://csetzer.github.io/articles/modeltypetheoryinaccessiblemahlo.pdf)，§2.1、5.3–5.4 | 模型上界与理论版本审计；注意 KPM⁺ 和 LF 范围 | 等强度就是所需有效证明翻译或基本列转换 |
| [Takahashi 2025](https://lmcs.episciences.org/16822/pdf)，§2.1、Example 2.1、Appendix A | 规则的明确呈现、常值重编码；核对额外宇宙与 Acc | 宿主 Agda 的全部能力等于原 MLM；闭包等式就是下降关系 |
| [Dybjer–Setzer, Predicativity of the Mahlo Universe in Type Theory](https://csetzer.github.io/articles/dybjerSetzerWeylVolume2025/dybjerSetzerWeylVolume2025Final.pdf)，§1–2、Appendix B | 内外宇宙与消去权限 | 可把内部 Mahlo 宇宙当普通归纳类型遍历 |

以下为方法候选，尚未接入 K1/K2。保留入口不代表恢复其旧探索路线：

- [Hancock, Ordinals and Interactive Programs](https://www.lfcs.inf.ed.ac.uk/reports/00/ECS-LFCS-00-421/ECS-LFCS-00-421.pdf)：调查交互／可达性结构是否能从宇宙规则生成前驱。必须核查其是否已经要求输入前驱系统。
- [Freund, Computable Aspects of the Bachmann–Howard Principle](https://arxiv.org/pdf/1809.06774)：调查统一坍缩生成所需的输入结构。把宇宙规则变成其输入，以及基本列输出，都是另需证明的桥梁。
- [Kraus–Nordvall Forsberg–Xu, Type-Theoretic Approaches to Ordinals](https://fredriknf.com/papers/ordinals_tcs2023.pdf)：审计无限分支、序数上确界及可判定表示之间的区别。
- [Fernández-Duque–Weiermann, Fundamental sequences and fast-growing hierarchies for the Bachmann–Howard ordinal](https://arxiv.org/pdf/2203.07758)：在基本列已经生成后，参考其正则性与增长认证方法；不作为 Mahlo 基本列输入。

旧证明枚举、原始递归增长和高阶返回类型的论文记录留在归档，不列为当前执行依据。新的文献调查必须说明它补上“宇宙规则到基本列”的哪一箭头。
