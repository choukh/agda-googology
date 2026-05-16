# Mahlo Phase 4: 去 strat + level-indexed ψ_M (诚实负面结果)

> Phase 4 工作文件: [Phase4.lagda.md](Phase4.lagda.md). 上游诊断: [FINDINGS_Phase3.md](FINDINGS_Phase3.md). 计划: [/Users/alsg/.claude/plans/mahlo-hase-cheerful-frog.md](file:///Users/alsg/.claude/plans/mahlo-hase-cheerful-frog.md).
>
> **简短结论**: Phase 4 ψ_M v1/v2 都编译通过, **但实际强度未超过 Higher.agda**. 与 plan 目标 ψ(Ω_(Ω+ω)) 有差距. 原因是结构性 — Sub a 是 Σ-平铺, 索引能力 = ℕ, 不足以驱动 Ord-tree-indexed limit. **诚实记账: Phase 3 + Phase 4 两轮探索都未能超过 Higher.agda. Mahlo 路径在当前 Σ-Sub 设计下已饱和**, 需 Phase 5 走根本性不同方向 (见 §5).

## 0. TL;DR

- ✓ **4a 去 strat**: Phase 4 mahlo 字段 5 → 4 (去 σ). `<ᴹ-dec?` 退回 partial (cross-case `nothing`, 同 Phase 2). monoSub + `<ˢ` + `<ˢ-dec` 全保留. Phase 4 8 层互递归编译通过.
- ✓ **4b `level : Ordᴹ → Ordᴰ`**: 结构归纳, mahlo +1 rank. lim 用 cumsum + cumsum-mono 单调化 (照搬 ordᴰ 模板).
- ✓ **4c-v1 简单 ψ_M**: 直接输出 Ord₀, mahlo 用 `ψ₀ ∘ Ω ∘ ordᴰ` (BTBO ψⁿ pattern). 编译通过. **强度 = BTBO = ψ(Ω_Ω)**, **不超过 Higher.agda**.
- ✓ **4c-v2 level-bumped ψ_M**: mahlo Ω-index 用 `ordᴰ (ψ_M a) + level (mahlo …)`. 强度 ≈ ψ(Ω_(BTBO+ω)) — 比 v1 略增, **仍不超过 Higher.agda** 的 ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))).
- ✗ **4c-v3 Sub-enum b 折入**: 未实现. 即使实现, 结构上仍是 ℕ-cofinal, 不会超过 Higher.agda.

**核心负面结论**: 当前 Mahlo 编码 (Phase 1-4 共用的 8 层互递归骨架) 在 Sub a 是 Σ-flat 的限制下, **ψ_M 无论怎么设计都达不到 Higher.agda 的 ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1)))**, 因为缺失"Ord ℓ-indexed limit"这一关键结构.

## 1. 实施细节

### 1.1 4a — 去 strat

[Phase4.lagda.md §4a](Phase4.lagda.md). mahlo 构造子签名从

```agda
mahlo : Opᴹ → (a : Ordᴹ) → (b : Sub a → Ordᴹ) → monoSub a b → (∀ s → a <ᴹ b s) → Ordᴹ
```

退回到

```agda
mahlo : Opᴹ → (a : Ordᴹ) → (b : Sub a → Ordᴹ) → monoSub a b → Ordᴹ
```

`<ᴹ-dec?` 的 mahlo cross-case `(mahlo-a, mahlo-b)` 与 `(mahlo-b, mahlo-a)` 返 `nothing` (无 strat 桥接). `(mahlo-b s, mahlo-b s')` case 仍用 monoSub + `<ˢ-dec` 闭合.

### 1.2 4b — `level`

```agda
level : Ordᴹ → Ordᴰ
level zero            = zeroᴰ
level (suc a)         = level a
level (lim f _)       = limᴰ (cumsum (level ∘ f)) (cumsum-mono (level ∘ f))
level (mahlo _ a _ _) = sucᴰ (level a)
```

mahlo case +1 rank, 与 ordᴰ 的 `ordᴰ (suc a) = sucᴰ (ordᴰ a)` 模式同构 (但 suc 不增 rank — rank 只跟踪 mahlo 嵌套).

### 1.3 4c-v1 — ψ_M 基线版

```agda
ψ_M : Ordᴹ → Ord₀
ψ_M zero            = Ω zeroᴰ                                  -- ω
ψ_M (suc a)         = lfp ((ψ_M a) +_)
ψ_M (lim f _)       = lim (ψ_M ∘ f)
ψ_M (mahlo _ a _ _) = ψ₀ {ℓ = ordᴰ (ψ_M a)} (Ω (ordᴰ (ψ_M a)))
```

mahlo 输出 ψ(Ω_(ψ_M a)), 是 BTBO `ψⁿ = iter (ψ₀ ∘ Ω ∘ ordᴰ) zero` 的逐项展开. ω-嵌套 mahlo 等价于 ψⁿ 序列, 极限 = BTBO.

### 1.4 4c-v2 — level-bumped Ω-index

```agda
ψ_M-v2 (mahlo _ a _ _) m = ψ₀ {ℓ = ordᴰ (ψ_M a) +ᴰ level m}
                              (Ω (ordᴰ (ψ_M a) +ᴰ level m))
```

mahlo case Ω 的索引加上 level 贡献, 给出 ψ(Ω_(ordᴰ(ψ_M a) + level m)). M^n iterated → ψ(Ω_(ψⁿ(0) + n)). lim n → ψ(Ω_(BTBO + ω)) 量级.

## 2. 强度对比 (核心 deliverable)

| 来源 | 估算 |
|------|------|
| BTBO `BTBO = lim ψⁿ` | ψ(Ω_Ω) |
| **Phase 4 v1** | **≈ ψ(Ω_Ω)** — 与 BTBO 持平 |
| **Phase 4 v2** | **≈ ψ(Ω_(Ω+ω))** — 比 BTBO 多 ω-级, **但**: |
| Higher.agda OrdΩ + limₙ | ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) — 估算 by ggg 社区 |
| Phase 4 v2 vs Higher.agda | **v2 ≲ Higher.agda** (v2 的 Ω-塔仅 ℕ-高, Higher.agda 的 limₙ 是 Ord-tree-高) |

**关键定性差**: Higher.agda 的 limₙ 索引在 `Ord ψᴰ(n)` (一棵带 limᵢ 嵌套的 Brouwer 树), Phase 4 v1/v2 的 ψ_M 索引在 `ℕ` (mahlo 嵌套深度). 二者在 cardinality 上都可数, 但 Ord-tree 的内部 limᵢ 嵌套给 Higher.agda 多出 1 个 "Ω-索引深度", Phase 4 没有.

## 3. 为什么 Phase 4 v3 (Sub-enum) 也不会超过

设计假设的 v3:
```agda
ψ_M-v3 (mahlo _ a b _) = ... + lim (n ↦ ψ_M-v3 (b (enum-Sub a n)))
```

`enum-Sub : (a : Ordᴹ) → ℕ → Maybe (Sub a)` 把 b 折成 ℕ-序列. 即使 Cantor pairing 处理 mahlo 的 Σ-嵌套, 输出仍是 ℕ-cofinal lim. 与 Higher.agda 的 `limₙ ... (Ord ℓ → OrdΩ)` 相比, 缺 Ord-tree 索引层.

**结论**: 在当前 `Sub (mahlo _ a b _) = Σ (Sub a) (Sub ∘ b)` 设计下, Phase 4 任何 ψ_M 变体都不会超过 Higher.agda. **Mahlo 路径的 Sub-Σ 限制是结构性瓶颈**.

## 4. 与 Phase 3 路线的对比

| 维度 | Phase 3 (strat) | Phase 4 v1 | Phase 4 v2 |
|------|-----------------|------------|------------|
| mahlo 字段数 | 5 | 4 | 4 |
| `<ᴹ-dec` | full 4/4 | partial 2/4 | partial 2/4 |
| ψ_M 实现 | 占位待写 | ✓ Ord₀-直输 | ✓ level-bumped |
| 估算强度 | ≲ Higher.agda | ≈ BTBO | ≈ ψ(Ω_(Ω+ω)) |
| 是否超过 Higher.agda? | ✗ | ✗ | ✗ |

**两轮探索都未能超过 Higher.agda**. Phase 3 用 strat 换 full trichotomy, Phase 4 去 strat + level-indexed ψ_M. 都受 Sub 是 Σ-flat 的限制. **Mahlo 路径在当前 Sub-Σ 设计下的强度上限 ≈ Higher.agda, 不会更高**.

## 5. Phase 5 候选路径 (突破 Sub-Σ 瓶颈)

要真正超过 Higher.agda, 必须在某个维度做结构性升级. 三条候选:

### 5.1 路径 A: Sub 升级为 Ord-indexed

把 `Sub (mahlo _ a b _) = Σ (Sub a) (Sub ∘ b)` 改成 `Sub (mahlo _ a b _) = Ord< (level a) _` 或类似 Ord-tree 形. 同步改 b: `b : Ord (level a) → Ordᴹ`. 这让 mahlo 节点拥有 Higher.agda `limₙ`-同级的索引能力. **挑战**: 互递归层数飙升 (Ordᴹ + Ord ℓ + Sub + ...), positivity 风险.

### 5.2 路径 B: 不走 Mahlo, 直接 Higher^n 迭代

放弃 Mahlo 编码, 在 OrdΩ 之上再加 `limₙ'` 层, 形成 Higher² ... Higherω. 每迭代 +1 Ω-级, ω-迭代到 ψ(Ω_(Ω+ω)). **优势**: 简单 (Higher.agda 50 行模板可复用), 预测性强. **劣势**: 不是 Mahlo, 是平铺 Buchholz 扩展.

### 5.3 路径 C: 真 Setzer Mahlo (Opᴹ 语义化)

给 `Opᴹ = op (c : Ordᴹ) (Sub c → Opᴹ)` 一个语义解释 `⟦_⟧ : Opᴹ → Ordᴹ → Ordᴹ`, mahlo 字段 f 真正代表"反射算子". ψ_M 通过 f 的 closure 性质构造 fixed-point. **优势**: 理论可达 ψ(M_真). **劣势**: 研究级, 互递归 + 语义闭合证明数千行.

**建议下一步**: 走路径 B (Higher^n 迭代) 作为 Phase 5 主线 — 工程上最可行, 强度增量明确. 路径 A/C 作为长期目标.

## 6. 重要修正 — Phase 3 + Phase 4 累积代价

| 阶段 | 代码量 | 强度增量 vs 上一步 |
|------|--------|------------------|
| BTBO 基线 | (主线) | ψ(Ω_Ω) |
| Higher.agda | ~50 行 | +1 Ω-级 → ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) |
| Phase 1 (Brouwer-MLQ 骨架) | ~40 行 | 0 (仅结构) |
| Phase 2 (`<ᴹ`, partial `<ᴹ-dec`) | ~140 行 | 0 |
| Phase 3 (Sub`<ˢ` + monoSub + strat) | ~160 行 | ≲ Higher.agda |
| **Phase 4 (去 strat + ψ_M v2)** | **~210 行** | **≲ Higher.agda** |

**Mahlo 路径累积 ~550 行代码, 强度上限 ≲ Higher.agda 的 50 行**. 这是 Phase 1-4 的诚实记账. Mahlo 形式化是**结构性贡献** (探索 IR-Mahlo, Sub Σ-closure, 内禀序 `<ˢ`, monoSub, level rank), **不是强度贡献**.

## 7. 文件清单

- [Phase1.lagda.md](Phase1.lagda.md) — Brouwer-MLQ 骨架
- [Phase2.lagda.md](Phase2.lagda.md) — `<ᴹ` + partial trichotomy
- [Phase3.lagda.md](Phase3.lagda.md) — full trichotomy + strat
- [Phase4.lagda.md](Phase4.lagda.md) — **本次新增**, 去 strat + level-indexed ψ_M
- [FINDINGS.md](FINDINGS.md) — Mahlo 编码主报告
- [FINDINGS_Phase2.md](FINDINGS_Phase2.md), [FINDINGS_Phase3.md](FINDINGS_Phase3.md) — 历史诊断
- [FINDINGS_Phase4.md](FINDINGS_Phase4.md) — 本报告

全部 5 个 `.lagda.md` 文件通过 Agda 2.8.0 + stdlib 2.3 + cubical 0.9 + `--safe --without-K --cubical-compatible --lossy-unification --hidden-argument-puns` 编译. 无 postulate, 无 unsafe.

## 8. 给作者的建议

1. **Mahlo 路径的强度上限是 Higher.agda 级别, 不更高**. 这是 Phase 1-4 的实证结论.
2. **若目标是超过 Higher.agda, 推荐走 Higher^n 迭代 (路径 B)** — 工程上最直接, 强度可量化.
3. **Mahlo 形式化的价值在结构** (IR-Mahlo, Sub 内禀序, monoSub), 不在 ordinal 强度. 可以作为类型论研究素材保留.
4. **真 Setzer Mahlo (路径 C)** 是开放问题, 至少需要 Phase 5+6 两轮研究投入, 不建议短期内尝试.
