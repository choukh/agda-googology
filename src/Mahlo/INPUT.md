# 输入：Setzer 的内涵 Mahlo 类型理论

2026-09-09。这里固定被分析的规则系统，不声明其在 Agda 中已有完整实现。

## 1. 对象理论与校准对象

目标 R_M 为 Setzer 的内涵 MLM：基础依赖类型论连同一个 Mahlo 宇宙及其子宇宙规则。以 [Setzer 原文 §4](https://csetzer.github.io/articles/mahlo.pdf)为原始依据，以 [Takahashi §2.1、Appendix A](https://lmcs.episciences.org/16822/pdf)的显式项、判断与推导规则辅助核对。

独立校准目标记作 α_M=ψ_{Ω₁}(Ω_{M+ω})，沿用 Setzer 的符号体系；其中的大写 M 与序数函数符号必须按参考分析解释，不能从普通集合论 Mahlo 基数的名字直接换算。该表达式不输入提取算法。

完整输入含上下文、形成、引入、合法消去、转换与代换规则；基础类型包括有限类型、ℕ、Π、Σ、和、W、内涵等同，以及宇宙代码和解码。实现前仍须完成逐规则抄录及对应审计，本文件是研究规格，不是已经完备的形式化规则表。

不自动加入上层 Tarski 宇宙或一般索引 Acc。文献中的 MLM⁺、MLMacc 与 MLM 不可互换。外部 Mahlo／TTM 和宿主 Agda 可以作为候选元环境，须另证所需解释与强度归属。

## 2. 直接研究的核心规则

用 M 表示 Mahlo 代码类型，T:M→Type 为解码。令

\[
\operatorname{Fam}(M)=\Sigma(a:M)(T(a)\to M).
\]

对对象理论中的合法算子 f:Fam(M)→Fam(M)，有子宇宙 U_f、其到 M 的代码映射 i_f，以及 M 中代表 U_f 的代码 u_f。写 T_f=T∘i_f，满足 T(u_f)=U_f。

对 a:U_f、b:T_f(a)→U_f，有 res₀ᶠ(a,b):U_f；对 c:T_f(res₀ᶠ(a,b))，有 res₁ᶠ(a,b,c):U_f。关键计算方程为

\[
i_f(\mathrm{res}_0^f(a,b))=\pi_1 f(i_f(a),i_f\circ b),
\]
\[
i_f(\mathrm{res}_1^f(a,b,c))=\pi_2 f(i_f(a),i_f\circ b)(c).
\]

研究必须涵盖带上下文的 f、b 及其合法代换，不只选择几个封闭实例。这里的 Type 是纸面类型判断的记法，不是在对象理论中添加 `Type : Type`。

这些方程表达闭包与解码相容，本身没有指定序数比较或基本列。新的核心工作正是推导这条缺失的联系，见 [RESEARCH.md](RESEARCH.md)。

## 3. 提取在什么层面进行

候选提取器分析外部可编码的规则及有限推导。它不能通过对任意 M 元素作未获授权的模式匹配递归来读取整个宇宙。

[Dybjer–Setzer §1、Appendix B](https://csetzer.github.io/articles/dybjerSetzerWeylVolume2025/dybjerSetzerWeylVolume2025Final.pdf)展示特定自然 Mahlo 消去规则导致的不一致。这要求审计消去权限，不排除外部规则语法上的提取。

输入语法可枚举，不等于所有解码元素可枚举；有限推导也不自动提供有限语义支撑、序数秩或共尾模量。
