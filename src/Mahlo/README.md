# Mahlo：类型宇宙飞跃研究

**状态：研究中，尚非成品；不参与默认文档发布。**

目标是利用类型宇宙的闭包与反射，通往单个 Mahlo 宇宙的证明论序数及其基本列，最终定义 `F_{α_M}`。

从 [ROADMAP.md](ROADMAP.md) 开始；首轮结果见 [FINDINGS.md](FINDINGS.md)，最新进展见 [第五轮记录](FIFTH-ITERATION.md)：已实现有限支撑计算、原始项语法检查及无损表达式转换；真实记号的比较与 OT 正规性仍待完成。主线是宇宙规则实现、Mahlo 良序证明、端点统一化、基本列和 FGH。

旧的自然数指标迭代路线位于 [probes/OCF/ROADMAP.md](../../probes/OCF/ROADMAP.md)，作为历史探索保存。Lens 探针位于 [probes/Lens](../../probes/Lens/)。两者都不作为本路线已经完成的强度证明。

首轮代码：[Universe/External.agda](Universe/External.agda)。它已构造任意族算子的安全子宇宙及解码相容等式，并实现原文 §5.9 的族重编码。完整 MLM 解释、Mahlo 良序证明与端点仍未完成。

研究审计：[理论与宿主](THEORY.md) · [规则表](RULE-MATRIX.md) · [反射依赖](REFLECTION-PLAN.md) · [端点](ENDPOINT.md) · [基本列方案](FUNDAMENTAL-PLAN.md)。

终点与必证性质：[量级验收契约](CALIBRATION.md)，区分函数增长与具体大数下界。
