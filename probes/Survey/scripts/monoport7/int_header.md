# 极限高度 (四): 源层带节点的 `Int` 单调, 对一切不含 Ω-极限的层

> 入口 [MonoPort7](MonoPort7.lagda.md). 不含记号. 由 `probes/Survey/scripts/monoport7/mk_int.py` 从 [MonoPort6Int](MonoPort6Int.lagda.md) 生成. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> 与 `MonoPort6Int` 只差: `CxS` 与 `IntMS` 对层 $L$ 写一次 (原来对 `hs b`), 节点从 `ss P` 换成任意 `r`, 子层有限由 `finS r` 给出, 内层 `Int` 的 `NZ` 写成折叠里字面的 `NZ-S r`; `IntMK` 多一句 `hl f`. 证明的每一句不变.

