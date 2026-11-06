# 极限高度 (五): 层 $L$ 的核实例, 对一切层

> 入口 [MonoPort7](MonoPort7.lagda.md). 不含记号. 由 `probes/Survey/scripts/monoport7/mk_lay.py` 从 [MonoPort6Lay](MonoPort6Lay.lagda.md) 生成. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> 与 `MonoPort6Lay` 只差: 模块 `L` 的层参数就是层本身 (原来是 `hs b` 里的 `b`), 关系与上下文写成 `RelN`, `CxN`, 动作前提写成 `HAKN` (对 `hs b`, `hl f` 定义性地就是 `HAK`). 证明的每一句不变.

