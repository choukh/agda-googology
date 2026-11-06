# 极限高度 (六): 节点一步与对层的归纳, 对一切不含 Ω-极限的层

> 入口 [MonoPort7](MonoPort7.lagda.md). 不含记号. 由 `probes/Survey/scripts/monoport7/mk_snd.py` 生成: `SemK` 到 `Node` 照 [MonoPort6Snd](MonoPort6Snd.lagda.md) 手写 (对层 `hl` 加一句), `sndS` 的子句逐字取自 `MonoPort6Snd`, 只换节点那一句. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> 与 `MonoPort6Snd` 的差: `Node` 对节点层 $L$ 与任意节点 `r : StH W k L` 写一次 (原来是 `hs b` 与 `ss Pk`); 分支的关系是 `RelN L`; 坐标动作的前提里, 内层 `Int` 在层 $L$ 上的输出经 `toN`/`fromN` 在 `Rel L` 与 `RelN L` 之间换写 (对 `hs`, `hl` 两者定义性相同); `rkRel` 多一句目标 `hl` 的保留; `SemK`, `chainK`, `brnK`, `sndArg` 多一句 `hl f`. `sndS` 对一切 `Fin` 层 (不含 Ω-极限).

