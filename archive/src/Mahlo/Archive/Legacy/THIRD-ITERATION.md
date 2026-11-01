> **已归档，非当前计划。** 保留历史论证与当时结论；文中的“当前”“下一步”和完成状态均指归档前。当前入口：[Mahlo 研究](../../README.md)。

# 第三轮：强化量级验收，接通 distinguished 归纳接口

日期：2026-09-08。

## 1. 目标对齐已写入计划

[量级验收契约](CALIBRATION.md) 区分指标、函数和具体数值，列出 C1–C7 必证性质。路线图已将 MLM 可证全函数支配列为必做项，新增 U6／G5 验收固定输入的大数下界。迭代次数、基本列、输入 k 与数值基准尚未冻结；本轮不默默作出选择。

独立参考层级校准、有效阈值、证书无关性、定量证明分析及固定输入比较都有单独的证明义务。仅有终止性、序数名称、较低层级支配或渐近量级均不足以宣布完整目标完成。

## 2. 新增形式化结果

[Locality.agda](WellOrder/Locality.agda) 证明生成证书在一个指定区域内的迁移：区域内资格可向目标转换、目标前驱可向来源转换、且目标前驱仍在区域内，即可通过来源归纳取得目标证书。前驱转换方向与资格转换方向相反；代码明确保留了这一点。

[Distinguished.agda](WellOrder/Distinguished.agda) 采用 `A` 是生成集初始段的定义，并证明：如果 A 中真正的序数前驱也是生成规则的前驱，那么 A 支持任意目标宇宙层级的归纳，且能产生 A 上限制次序的可达性证书。

进一步的 `FromClosure` 模块采用如下形式，其中 `Closure x y` 表示 y 属于 C^x(A)：

- M(A)(x) = Valid(x) × Closure(x,x)。
- τ_A(x)(y) = Closure(x,y) × (y < x)。

只要 `A(y)` 与 `y < x` 能给出 `Closure(x,y)`，即可构造所需的前驱完整性；再利用 A 的初始段性质和生成证书，证明 x 属于 A 时 τ_A(x) 的成员都属于 A。两向成员转换接通了生成归纳与 A 上的序数归纳。

这些形式对照 [Setzer 前置论文](https://csetzer.github.io/articles/2papdiss.pdf) Definition 4.5、4.18、Remark 4.20 和 Lemma 4.21(a)。本轮尚未实例化其具体记号及闭包，因而得到的是明确带前提的通用定理，而不是已经完成这些引理的 Mahlo 特例。

## 3. 未跨越的边界

- 没有实现参考系统的合法性、顺序或 C^x(A) 的有限算法；`Closure` 仍是显式输入。
- 局部证书迁移不是具体 M(A)、τ_A 的局部性证明；转换映射仍需由实际闭包性质构造。
- 没有假设“任意严格前缀相同就能在任意点迁移”。参考证明涉及特定截断位置和资格条件，必须保留这些限制。
- 没有证明 distinguished-set 唯一性、Lemma 4.26、Mahlo 反射或端点。
- 本轮代码不构成函数增长率或固定大数数值的证据；C1–C7 仍未整体验收通过。

## 4. 紧接着的任务

下一轮优先落实原记号的有限闭包规则及小性编码，产出具体的资格与前驱关系，再验证其所需截断局部性。只有取得这些实例，才继续唯一性与 4.26；不继续通过增加通用接口来替代这一数学工作。

同时为 C6 建立定量证明分析的来源与缺口表，区分良序下界与可证全函数的计算上界。

## 5. 验证

新增模块启用 `--safe --without-K`，仅依赖内建模块及已有 Mahlo 模块，无 postulate 或取消检查选项。独立检查命令：

```sh
agda --no-libraries -i src src/Mahlo/Archive/Legacy/WellOrder/Locality.agda
agda --no-libraries -i src src/Mahlo/Archive/Legacy/WellOrder/Distinguished.agda
```

Agda 2.8.0 下 `tools/check-src.sh` 全部 23 个 src 模块通过，无警告；文档本地链接及 `git diff --check` 通过。
