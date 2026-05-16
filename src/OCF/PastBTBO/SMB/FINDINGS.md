# Phase 7 SMB-Trees 探针 — 实测报告

> 工作文件: [Core.lagda.md](Core.lagda.md), [Naive.lagda.md](Naive.lagda.md), [Mahlo.lagda.md](Mahlo.lagda.md). 计划: [/Users/alsg/.claude/plans/mahlo-hase-cheerful-frog.md](file:///Users/alsg/.claude/plans/mahlo-hase-cheerful-frog.md).
>
> **TL;DR**: Eremondi 2023 SMB-trees 论文 ([arxiv:2312.06962](https://arxiv.org/abs/2312.06962)) 的方法**不能**绕过 BTBO 框架的 BoundedTrich 障碍. 落地 Phase A (Tree + indMax) 编译通过; Phase B-1 (Naive) 与 B-2 (Mahlo) 都验证为**结构性不可解**. 强度增益 = 0. 但收获明确的负面诊断 — 论文的算律工具不解 BTBO 的决策性问题.

## 0. 出口情景

| 计划情景 | 实际落地 |
|---------|---------|
| **目标** (60-70%): A✓ B-1✓ B-2✗, +ψ(Ω_(Ω·Ω)) | ✗ |
| **保守** (25%): A✓ B-1✗ B-2✗, +0 | ✓ **落点** |
| **意外** (5-10%): A✓ B-1✓ B-2✓, +ψ(M) | ✗ |
| **最坏** (<5%): A✗ | ✗ |

## 1. SMB-trees 论文摘要 ([arxiv:2312.06962](https://arxiv.org/abs/2312.06962))

Joey Eremondi (U. Edinburgh, CPP 2024). **Strictly Monotone Brouwer Trees for Well-founded Recursion Over Multiple Arguments**.

核心贡献:
- `Tree`: 通用 Brouwer 树, `Lim c f` 不带 `f` 单调约束
- `indMax : Tree → Tree → Tree`: 5-case 递归 max, 定义性等式 `indMax (↑ a) (↑ b) ≡ ↑ (indMax a b)`
- `indMax-≤L`, `indMax-≤R`: LUB 弱版本 (≤, 非 idempotent)
- **SMB-tree (sigma-refined)**: `Σ[ t ∈ Tree ] indMax t t ≤ t` — 携带 idempotency 证明, 实现 strictly monotone join
- 算律: `a < b ∧ c < d → max a c < max b d` (strict bicongruence)
- **目标场景**: 多参数 well-founded recursion (例如 `wfRec` over `(t₁, t₂)`)

**论文不涉及**: OCF 折叠, ψ-function, 反射性, Mahlo. 关键引文 [Generalized Decidability via Brouwer Trees (de Jong et al. 2026)](https://arxiv.org/abs/2602.10844) 明确: **Brouwer 树上 `α ≤ β` 与 `α ≡ β` 的无条件决策性是 constructive taboo**.

## 2. Phase A: SMB Core 实测 ([Core.lagda.md](Core.lagda.md))

✅ **编译通过**, ~140 LOC.

落地内容:
- `Tree` 数据类型 (Z, ↑, Lim) — 不带 mono on Lim
- `_≤_` 4-ctor (≤-Z, ≤-sucMono, ≤-cocone, ≤-limiting)
- `_<_ a b := ↑ a ≤ b`
- ≤-refl, ≤-trans, extLim, ≤↑t, <-in-≤, <∘≤, ≤∘<
- `indMax` 5-case (Z-L, Z-R, Suc-Suc, Suc-Lim, Lim-arg)
- `indMax-≤L`, `indMax-≤R` 完整证 (10 case)
- `bound a b := ↑ (indMax a b)`, `a<bound`, `b<bound` ✓

**未落地**:
- `indMax-monoL` / `indMax-monoR` (论文 §3.2 长 case 分析, B-1 不需要)
- SMB-tree sigma 包装 (Eremondi SMBTree.lagda) — 未实施, B-1 不需要
- `toTree-<-inv` 反向桥接 (B-1 路径不依赖, 略过)

**关键技术决策**:
- 简化 universe-of-codes (ℂ, El): 只取 ℕ-索引 (`SmallTree` 等价)
- 跳过 view-type IndMaxView, 直接 5-case (ℕ-simpler, 仍终止)

## 3. Phase B-1: Naive `<-1-dec` 实测 ([Naive.lagda.md](Naive.lagda.md))

❌ **失败** — 但失败模式清晰诊断.

诉求 (回顾 [PastBTBO/Naive/FINDINGS §5.1](../Naive/FINDINGS.md)):
- `<-1-dec (limΩ x p) (limΩ y q)` 需任意 `x, y : Ordᴰ` 上的 trich
- 等价于: 构造 `bound : Ordᴰ → Ordᴰ → Ordᴰ` with `x <ᴰ bound` ∧ `y <ᴰ bound`

SMB 提供:
- `bound : Tree → Tree → Tree` ✓
- `toTree : Ordᴰ → Tree`, `toTree-< : a <ᴰ b → toTree a < toTree b` ✓

**关键障碍**: 要让 `bound-ᴰ x y := fromTree (bound (toTree x) (toTree y))` 在 Ordᴰ 上成立, 需:

> `toTree-≤-implies-Ordᴰ-≤ : toTree x ≤ t → x ≤ᴰ fromTree t`

`limᴰ` 情形 (`≤-limiting`): 需 `limᴰ f' mf' ≤ᴰ fromTree t` 给定 `∀ k → toTree (f' k) ≤ t`.

但 `limᴰ f' mf' ≤ᴰ fromTree t` 在 Ordᴰ 上**结构性**难证 — `_<ᴰ_` 没有 "limᴰ < X" 的直接构造子. 通常 fromTree 用 cumsum 包裹, 而 cumsum 是 `_+_` 累加, **该步退化回 +-lmono**.

**结论**: SMB 的 indMax 在 Tree 上工作, 但**桥接回 Ordᴰ 必撞 +-lmono**. 与 [PastBTBO/Naive/FINDINGS §5.3](../Naive/FINDINGS.md) 一致 — `+_` 的左非单调是 Ordᴰ 上的结构性真相, SMB 不能改变.

### 3.1 局部胜利: bounded Ord-Ord 已存在

[BTBO.lagda.md:836-857](../../BTBO.lagda.md#L836-L857) 的 `Ord-Ord` 模板:

    module _ (ℓ : Ordᴰ) (Ord< : (i : Ordᴰ) (p : i < ℓ) → Set) where
      data Ord₊ where
        ...
        limᵢ : (p : i < ℓ) (f : Ord< i p → Ord₊) → Ord₊

`limᵢ p f` 携带 `p : i < ℓ` — **bound 内嵌**. 这就是 Naive 原文 §5 路径 B 的实现. BTBO 已经做了, 给出 ψ(Ω_Ω). 用 SMB 重做相同结构 = **0 强度增益**.

### 3.2 真正障碍 = 不可解的决策性

要超过 ψ(Ω_Ω), 需让 `limΩ` 真正**无界** (over all Ordᴰ). 这需要 Ordᴰ 上的**无条件 trich**, 而该决策性是 [constructive taboo](https://arxiv.org/abs/2602.10844). **SMB 的算律工具不增强决策**.

## 4. Phase B-2: Mahlo `<ᴹ-dec` 实测 ([Mahlo.lagda.md](Mahlo.lagda.md))

❌ **失败** — 预期内, 失败模式与 Naive 不同.

诉求: `<ᴹ-dec (mahlo-b s p) (mahlo-b s' q)` 需对 `b s, b s' : Ordᴹ` 给出 trich.

SMB 尝试: 定义 `smaxᴹ : Ordᴹ → Ordᴹ → Ordᴹ` 仿 indMax.

**关键障碍**: `smaxᴹ (mahlo f₁ a₁ b₁) (mahlo f₂ a₂ b₂)` 的定义.

mahlo 的"宽度"由 `b : Sub a → Ordᴹ` 提供. 要 dominate 一个 mahlo, 必须 dominate 整个 b 函数的像集.

| 尝试 | 失败原因 |
|------|---------|
| `mahlo ... (smaxᴹ a₁ a₂) (λ s → smaxᴹ (b₁ ?) (b₂ ?))` | 需要 `s : Sub (smaxᴹ a₁ a₂)` 映射到 `(Sub a₁, Sub a₂)` — 无自然构造 |
| `lim seq seq-mono` (降维到 ℕ) | 强度损失 (mahlo 宽度可能不可数) |
| `mahlo ... (λ s → smaxᴹ (b s) <other>)` | 仅对每个 s 算 max, 不真正合并 b₁, b₂ |

**结构性原因**: SMB indMax 依赖**所有递归参数源于子树**. Mahlo `b : Sub a → Ordᴹ` 是**外部函数**, 输出不是 Ordᴹ 结构子项. **indMax-pattern 无法递归通过 b**.

与 [PastBTBO/Mahlo/FINDINGS §3-5](../Mahlo/FINDINGS.md) 撞墙诊断同源 — 跨函数像的决策性是 Brouwer-tree-paradigm 的天花板.

## 5. 三障碍对照表

| 障碍点 | 缺什么 | SMB 给什么 | 实测 |
|--------|--------|----------|------|
| Naive `<-1-dec` limΩ/limΩ | strict 共同上界 (∵ +-lmono 假) | `c = ↑(indMax x y)` 在 Tree 上 ✓ | ❌ Tree → Ordᴰ 桥接需 +-lmono |
| Mahlo `<ᴹ-dec` mahlo-b/mahlo-b | 跨函数像 trich | smax 需结构性递归, b 不是子项 | ❌ indMax 不适用 |
| Higher `OrdH α` 宽度限 ℕ | Ord 索引上的 monotone trich | (未测试) | (Higher 已 working at α≤ω) |

**核心命题**: SMB-trees 解 **算律** (indMax 的代数性), 不解 **决策** (BoundedTrich 障碍). 这是论文目标 (well-founded recursion) 与本仓库目标 (OCF 折叠) 的**根本范式差异**.

## 6. 强度位次更新 (与 ROADMAP 对照)

无变化. ψ-folding 在本仓库的可达上限仍是:

    BTBO = ψ(Ω_Ω)
       < Higher.agda ≈ ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1)))
       < Phase 6 HigherOrdᴰ Higher^ω ≈ ψ(Ω_(Ω+ω))
       ≤ Phase 7 推测 (HigherOrdᴰ², ψ(Ω_(Ω·2))) — 待落地
       ≤ Phase 8-9 推测 (ψ(Ω_(Ω²))) — 待落地
       ≪ ψ(Ω_(Ω^Ω)) — 框架天花板 (Bachmann-Howard ε_(Ω+1) ~ Γ_(Ω+1))
       ≪≪ ψ(M_Setzer) — 跨范式

SMB **不改变**任何位次. 与 Phase 1-5 Mahlo 770 LOC 撞墙的结论**完全一致** — 决策性障碍是 Brouwer-tree-paradigm 的内在限制.

## 7. Phase 8+ 推荐路径

- **路径 R1 (重启 Higher 主线)** 推荐 ✓:
  - 回到 [ROADMAP §3.1](../../ROADMAP.md): Phase 7 HigherOrdᴰ² → ψ(Ω_(Ω·2))
  - 已 90% 可行性, 150 LOC, 机械迭代
- **路径 R2 (Veblen)** 谨慎:
  - [ROADMAP §3.2](../../ROADMAP.md) Phase 10 — 引入 φ_α 函数族
  - 50% 可行性 (Veblen 在 Brouwer-tree paradigm 是否可表达?)
- **路径 R3 (跨范式)** 远期:
  - 接受 postulate (违反 --safe)
  - 换 sized types 框架
  - 换语言 (Coq / Lean)
  - 论文 SMB-trees 不在本路径起作用, 因为它仍是 Brouwer-tree paradigm 内

## 8. 关键教训

1. **范式诊断**: SMB-trees 是 well-founded recursion 工具, 不是 OCF 折叠工具. 阅读时应辨明论文目的与本仓库目的的差异.

2. **决策 vs 算律分离**: BTBO 框架的两大障碍 — Naive 的 +-lmono (算律) 与 Mahlo 的跨函数像 (决策) — **看似不同, 本质都源于 Brouwer-tree-paradigm 上对 `<` 的归纳定义结构**. SMB 的 algebra-on-Tree 不能桥接到 BTBO 的 inductive-`<`.

3. **预测准确性**: ROADMAP §3.3 "Phase 12+ 与 Mahlo 同构的墙" 与本 Phase 7 实测一致. **当前路径的强度天花板就在 ψ(Ω_(Ω^Ω)) 附近**, 突破需要离开 Brouwer-tree paradigm.

4. **价值留存**: Phase A SMB Core (~140 LOC) 不是白费 —
   - 提供 `Tree` + `indMax` + `bound` 的工具集, 可用于未来需要 well-founded recursion over 多参数的场景
   - 论文研读笔记可作为 OCF 文献分析的对照基线

## 9. 文件清单

Phase 7 新增 (本目录):
- [Core.lagda.md](Core.lagda.md) — Tree + indMax + bound (140 LOC, ✓ 编译)
- [Naive.lagda.md](Naive.lagda.md) — Naive 桥接诊断 (75 LOC, ✓ 编译)
- [Mahlo.lagda.md](Mahlo.lagda.md) — Mahlo smaxᴹ 诊断 (70 LOC, ✓ 编译)
- [FINDINGS.md](FINDINGS.md) — 本报告

不动 (mainline 主线):
- BTBO.lagda.md, Higher.agda, HigherIter.lagda.md, HigherOrdᴰ.lagda.md
- ROADMAP.md (Phase 7-12 计划仍有效)
- PastBTBO/* (历史快照)

全部通过 Agda 2.8.0 + stdlib 2.3 + cubical 0.9 + `--safe --without-K --lossy-unification` 编译.
