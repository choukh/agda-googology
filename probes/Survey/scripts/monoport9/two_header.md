# Ω-极限高度 (四): 只在不含 Ω-极限的目标上比的两世界互模拟

> 入口 [MonoPort9](MonoPort9.lagda.md). 不含记号. 由 `probes/Survey/scripts/monoport9/mk_two.py` 从 [MonoPort8Sim](MonoPort8Sim.lagda.md) 的 §6–§7 生成 (逐字节可重生成). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> `MonoPort8Sim.Two` 的前提 `fr` 要一切目标层不含 Ω-极限. 实例 $\Lambda=\mathrm{h\Omega}\,g$ 自己就是一个目标层 (`hself`), 所以 `Two` 用不到 $\Lambda=\mathrm{h\Omega}\,g$ 上. `MonoPort8` §3 的判断是 "把 `fr` 放宽成只在不含 Ω-极限的目标上比". 本文照做, 与 `Two` 只差:
>
> - `DfE` 的字段 `at` 多一个前提 `Free t` (目标层不含 Ω-极限); 一切 `dfe`/`at` 把它传下去; `StepE` 与判定一致 `rkT-rel` 用它代替 `fr tm₁ tm₂`.
> - 读状态的另一处是链 `Chn-E` 在节点层 $k$ 上读 (`at (dE hY) … hk₁ hk₂`). 节点层严格低于实例, 用模块参数 `frk : StH W₀ k ly → ly ⊲[ W ] Λ₁ → Free k` 给出 (对 $\mathrm{h\Omega}\,g$, 分支都不含 Ω-极限时成立, 见 [MonoPort9Walk](MonoPort9Walk.lagda.md) 的 `frkΩ`).
>
> 其余每一句与 `MonoPort8Sim` 相同. 本组不比 $\Lambda$ 这一层上的读数: 单世界关系 `MonoPort7Rel.Rel` 在 $\mathrm{h\Omega}\,g$ 层上本来就是 $\top$.

