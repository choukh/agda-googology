# Mahlo：类型宇宙飞跃研究

**状态：研究中，尚非成品；不参与默认文档发布。**

**当前主线：[从类型宇宙规则统一提取基本列](EXTRACTION-PLAN.md)。** 用户已澄清：研究目标是提取技术本身，不能预先手填 Mahlo 记号和基本列，再把良基证明当作提取。

**当前阶段：文献调查与纸面论证，暂停新增代码。** 见[提取可行性评估](Evidence/EXTRACTION-FEASIBILITY.md)：通用坍缩记号生成有文献先例，但宇宙到其输入的解释、Mahlo 推广及基本列增长认证尚未落实。

最新实验：[Extraction/Countable.agda](Extraction/Countable.agda)。已实现小分支宇宙的树提取、下降保持及可达性证明，并证明不能枚举所有 `Nat → Bool`，排除枚举全部解码元素的朴素方案。尚未从完整宇宙生成序数端点或基本列。

代码分工：`Universe/` 是候选输入与规则实现；`Extraction/` 是当前提取技术实验；`Notation/`、`Fundamental/` 是手写参考系统的校准探针；`Growth/` 是通用输出端。旧反射及良序模块作为潜在证明工具保存。所有部分仍属研究，不是已完成的 Mahlo 强度认证。

旧路线的反射研究见[第二次关键路径审计](Evidence/CRITICAL-AUDIT-2.md)：固定谓词的条件转移已验证，5.6 的小性构造存在需要独立补足的移植步骤。实际反射算子与阶段类型预算见[首次审计](Evidence/CRITICAL-AUDIT-1.md)，这些结论尚未连接统一提取器。

目标是利用类型宇宙的闭包与反射，通往单个 Mahlo 宇宙的证明论序数及其基本列，最终定义 `F_{α_M}`。

从 [EXTRACTION-PLAN.md](EXTRACTION-PLAN.md) 开始；[ROADMAP.md](ROADMAP.md) 保存路线变更与旧计划。历史实验见 [FINDINGS.md](FINDINGS.md) 和 [第五轮记录](FIFTH-ITERATION.md)，不代表当前提取技术已经完成的步骤。

旧的自然数指标迭代路线位于 [probes/OCF/ROADMAP.md](../../probes/OCF/ROADMAP.md)，作为历史探索保存。Lens 探针位于 [probes/Lens](../../probes/Lens/)。两者都不作为本路线已经完成的强度证明。

首轮代码：[Universe/External.agda](Universe/External.agda)。它已构造任意族算子的安全子宇宙及解码相容等式，并实现原文 §5.9 的族重编码。完整 MLM 解释、Mahlo 良序证明与端点仍未完成。

研究审计：[理论与宿主](THEORY.md) · [规则表](RULE-MATRIX.md) · [反射依赖](REFLECTION-PLAN.md) · [端点](ENDPOINT.md) · [基本列方案](FUNDAMENTAL-PLAN.md)。

终点与必证性质：[量级验收契约](CALIBRATION.md)，区分函数增长与具体大数下界。
