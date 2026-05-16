# Phase 6: Higher.agda 一般化 — umbrella overview

> 工作文件: [HigherIter.lagda.md](HigherIter.lagda.md) (Phase 6.1), [HigherOrdᴰ.lagda.md](HigherOrdᴰ.lagda.md) (Phase 6.2). 单文件实测 + 撞墙诊断已内嵌各文件 (literate Agda 交织风格).
>
> 本文件是 cross-file umbrella overview: 6.1 vs 6.2 对比 / 强度阶梯 / Phase 7 候选 / Mahlo vs Higher 总结教训.

## 0. TL;DR

| Phase | 文件 | LOC | 强度 |
|-------|------|-----|------|
| BTBO 基线 | [../BTBO.lagda.md](../BTBO.lagda.md) | (主线) | ψ(Ω_Ω) |
| Higher.agda | [../Higher.agda](../Higher.agda) | 43 | ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) ≈ ψ(Ω_(Ω+1)) 下方 |
| Mahlo Phase 1-5 (PastBTBO) | ~770 | ≲ Higher.agda (饱和) |
| **Phase 6.1 HigherIter** | [HigherIter.lagda.md](HigherIter.lagda.md) | **~110** | **≈ ψ(Ω_(Ω+4))** |
| **Phase 6.2 HigherOrdᴰ** | [HigherOrdᴰ.lagda.md](HigherOrdᴰ.lagda.md) | **~80** | **≈ ψ(Ω_(Ω+ω)) (α = ω-asᴰ)** |

**Phase 6.1 vs 6.2 关系**: 6.1 用 ℕ-索引手动迭代 4 层 (Higher² 至 Higher⁴), 每层独立 data type. 6.2 推广为单一 `OrdH α` (α : Ordᴰ), transfinite α 给 Higher^ω. 6.1 完全机械化的事实**预示**了 6.2 的可抽象性 — 实际 Plan agent 估算 500-800 LOC, 实测仅 80 LOC, 远超预期.

## 1. 累积强度阶梯

    BTBO = ψ(Ω_Ω)
       < Higher.agda ≈ ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) ≈ Phase 1-5 Mahlo 上限
       < Phase 5B Higher² spike ≈ ψ((Ω_Ω+1)+...) (60 LOC)
       < Phase 6.1 Higher⁴ ≈ ψ(Ω_(Ω+4)) (110 LOC)
       < **Phase 6.2 Higher^ω ≈ ψ(Ω_(Ω+ω))** (80 LOC, 顶级 binding ✓)
       < (Phase 7 推测) Higher^Ω ≈ ψ(Ω_(Ω·2))
       < (Phase 8+ 远期) Veblen / Inaccessibles / Mahlo 真

**Phase 6 比 Phase 1-5 Mahlo 累积工程量小 (190 LOC vs 770 LOC), 强度大幅超过**. 验证了 "Mahlo 路径饱和, Higher 路径无饱和" 的判断 (Mahlo/FINDINGS.md 三路径对比).

## 2. Phase 7 候选方向

Phase 6.2 已落地 Higher^ω. 自然下一步:

### 2.1 路径 X: Higher^Ω-asᴰ (ψ(Ω_(Ω·2)))

定义 `Ω-as-Ordᴰ = ordᴰ BTBO`, 然后 `Higher^Ω = lim (ψⁿ-at Ω-as-Ordᴰ)`. 估算 ψ(Ω_(Ω+Ω)) = ψ(Ω_(Ω·2)). 工程量极小 — 几行额外 binding.

### 2.2 路径 Y: Higher^(Ω·Ω)

层级 α 用 BTBO 的 Ordᴰ-嵌入复合: `α = ordᴰ (Higher^Ω)` 或类似. 给 ψ(Ω_(Ω·Ω)).

### 2.3 路径 Z: Veblen 化, 不动点

定义 φ-function 在 OrdH α 上, 得 ψ(φ_Ω(0)). 概念性研究.

### 2.4 路径 W: 跨 ψ 级 (Inaccessible / Mahlo 真)

引入新的 Ω-级 (类似 ψ_2, ψ_3 in extended Buchholz). 强度突破 ψ(Ω_(Ω^Ω)) 后趋向 ψ(I) 与 ψ(M_Setzer).

**Phase 7 推荐**: 先做 X (低成本高确定性), 然后 Y. Z 与 W 是研究级.

## 3. 关键教训 (Mahlo vs Higher)

1. **Plan agent 估算偏保守**: 500-800 LOC 实测为 80. Higher.agda 模板的"机械化"程度远超预期, IR scheme + 结构归纳自然消化了 transfinite α 的循环依赖.

2. **Mahlo 路径 vs Higher 路径**: Phase 1-5 用 770 LOC 在 Mahlo 上撞墙, Phase 6 用 190 LOC 在 Higher 上大跃进. **结构性突破来自"推广已知 working 模板"** (Higher.agda → OrdH α), 不是"尝试新结构" (IR-Mahlo).

3. **重大遗产**: PastBTBO/Mahlo 770 LOC 不是白费 — 它**验证了 Mahlo 路径的饱和**, 直接推动 Phase 6 转向 Higher 一般化. 没有 Phase 1-5 的 Mahlo 探索, Phase 6 不会有"放弃 Mahlo, 专注 Higher"的判断依据.

## 4. 文件清单

- [HigherIter.lagda.md](HigherIter.lagda.md) — Phase 6.1: Higher² 至 Higher⁴ 机械迭代 + 内嵌实测
- [HigherOrdᴰ.lagda.md](HigherOrdᴰ.lagda.md) — Phase 6.2: 单一 OrdH α + Higher^ω binding + 内嵌 Plan agent 对照
- [FINDINGS.md](FINDINGS.md) — 本 umbrella

全部通过 Agda 2.8.0 + stdlib 2.3 + cubical 0.9 + `--safe --without-K --cubical-compatible --lossy-unification --hidden-argument-puns` 编译.
