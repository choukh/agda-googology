# 极限高度 (三): 第 ≥1 层的结构关系推广到 ℕ-极限层

> 入口 [MonoPort7](MonoPort7.lagda.md). 不含记号. 由 `probes/Survey/scripts/monoport7/mk_rel.py` 从 [MonoPort6Rel](MonoPort6Rel.lagda.md) 生成 (逐字节可重生成). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> 与 `MonoPort6Rel` 只差: 层 `hl f` 上的关系不再是 $\top$, 而是同一个结构关系 `RelM (hl f) (LowT (hl f))` (`RelN`), 上下文同理 (`CxN`); `Fin` 收进 `hl` (`Fin (hl f) = ∀ n → Fin (f n)`, 即不含 Ω-极限), 一切输出律对 `hl` 的那一句照抄 `hs` 的那一句. `RelM` 本来就对任意层定义, 节点 `sl n P` 与 `ss P` 走同一个 `ni⊑`. 新增 `rΩ (hl f)`: $\Omega_{\mathrm{hl}\,f} = 1 ⨾ \mathrm{nl}\,(\lambda n.\ \mathrm{ni}\,(\mathrm{sl}\,n\,\mathrm{hself})\,(\lambda\_ \to 1))$ 与自己相关.

