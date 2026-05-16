# Phase 5: 三路径并行 spike 实测对比

> Phase 5 三 spike 文件: [Phase5A_SubOrd.lagda.md](Phase5A_SubOrd.lagda.md), [Phase5B_HigherIter.lagda.md](Phase5B_HigherIter.lagda.md), [Phase5C_OpInterp.lagda.md](Phase5C_OpInterp.lagda.md). 计划: [/Users/alsg/.claude/plans/mahlo-hase-cheerful-frog.md](file:///Users/alsg/.claude/plans/mahlo-hase-cheerful-frog.md).
>
> **结论**: A/B/C 都编译通过, 但**只有 B 实现了"超过 Higher.agda 强度"的核心目标**. A 是结构 spike (留下 ψ_M 待 Phase 6), C 撞 Agda 终止墙 (核心设计模式不可行, 退化为 inline 等价 Phase 4).
>
> **Phase 6 推荐**: 走 Path B (Higher^n 完整迭代), 放弃 Mahlo 路径 (A 路径长期投入收益不确定, C 路径结构性受限).

## 0. TL;DR

| 路径 | 编译 | 强度 demo binding | 核心目标达成? | 推荐 |
|------|------|-------------------|--------------|------|
| **B (Higher² 迭代)** | ✓ | `lim (n → ψ₀ (ψ<Ω² {n} ΩΩ²))` 顶级 binding | ✓ 明确超过 Higher.agda | **★ Phase 6 主线** |
| **A (Sub 升级 Ord-indexed)** | ✓ (结构) | sample `M-test`, 无 ψ_M | ⚠️ 结构落地, 强度未演示 | 长期备选 |
| **C (Opᴹ 语义化 v0)** | ✓ (内联绕过) | ⟦_⟧ 独立可用, ψ_M-C 退化等价 Phase 4 | ✗ **核心模式 Agda 拒绝** | 不推荐 (除非引入 Well-founded recursion) |

## 1. Path A 实测: Sub 升级到 Ord-indexed

### 1.1 落地

[Phase5A_SubOrd.lagda.md](Phase5A_SubOrd.lagda.md), ~85 行 (含注释), 编译通过.

核心改动:
- `level : Ordᴹ → Ordᴰ` 拉进 mutual block (forward-declare 在 Sub 旁)
- `Sub (mahlo _ a b) = Ord (level a)` (替代 Σ-平铺)
- `mahlo : Opᴹ → (a : Ordᴹ) → (b : Ord (level a) → Ordᴹ) → Ordᴹ` (b 改 Ord-indexed)
- `mahlo-b : ... → (s : Ord (level a)) → x <ᴹ b s → ...`
- **去掉 monoSub / `<ˢ`**: Ord ℓ 上无 unconditional trichotomy, spike 简化

### 1.2 关键发现

- ✓ **level 进 mutual block 没有 IR / positivity 问题**: Agda 接受 `Sub (mahlo _ a b) = Ord (level a)` 这种 IR 函数引用同 mutual 中其它 Set-valued 函数 (level) 的模式.
- ✓ **strict positivity 通过**: `b : Ord (level a) → Ordᴹ` 是函数类型, Ordᴹ 在 codomain, positive.
- ⚠️ **monoSub / `<ˢ` 在 Ord ℓ 上无 unconditional 定义**: BTBO 的 Ord ℓ 只有 bounded `<-dec` (在 Ordᴰ 层). 想给 Ord (level a) 上加 mono + trichotomy 是新研究.
- ⚠️ **ψ_M 未实现**: Sub 改 Ord-indexed 后, mahlo case 的 ψ_M 设计完全开放 — 既无 Sub-enum, 也无 monoSub. Phase 6 必须重新设计 ψ_M.

### 1.3 强度评估 (推测)

Path A 给 mahlo 节点 Higher.agda `limₙ`-级索引接入点. 若 Phase 6 能写出兼容的 ψ_M (用 Ord (level a) 索引 b 的 image), 强度可达 ψ(Ω_(Ω+ω)) 或更高. **但 spike 阶段没有 ψ_M, 实际强度未演示**.

风险: Phase 6 ψ_M 设计可能撞与 Phase 2 同样的 trichotomy 墙 (Sub a 现在是 Ord ℓ, bounded trichotomy 不足以驱动 ψ).

## 2. Path B 实测: Higher² 迭代 ✓ 唯一达成核心目标

### 2.1 落地

[Phase5B_HigherIter.lagda.md](Phase5B_HigherIter.lagda.md), ~60 行 (含注释), 编译通过.

核心实现:
- `ψⁿᴴ : ℕ → Ord₀` 提取 Higher.agda 的 iter 序列
- `ψᴰ' = cumsum (ordᴰ ∘ ψⁿᴴ)` Ordᴰ-层 seq, 极限 ≈ Higher.agda 的强度
- `OrdΩ²` 数据类型 (4 构造子, 同 OrdΩ)
- `↑Ω² : Ord (ψᴰ' n) → OrdΩ²` lift
- `ΩΩ²` outer lim
- `ψ<Ω² : OrdΩ² → Ord (ψᴰ' n)` collapse (模板 100% 仿 ψ<Ω)
- **强度 binding** ([Phase5B_HigherIter.lagda.md §7](Phase5B_HigherIter.lagda.md)):
  ```agda
  _ : Ord₀
  _ = lim (λ n → ψ₀ (ψ<Ω² {n = n} ΩΩ²))
  ```

### 2.2 关键发现

- ✓ **Higher.agda 模板是 symbolic copy-able**: 整个 Higher² 是 Higher.agda 43 行的 mechanical 重写 — `ψᴰ → ψᴰ'`, `ψⁿ → ψⁿᴴ`, `OrdΩ → OrdΩ²`, `↑Ω → ↑Ω²`, `ψ<Ω → ψ<Ω²`. 没有新的概念性 work.
- ✓ **跨模块依赖 R-B1 未发生**: `open import OCF.Higher` 引入 ψ<Ω + ΩΩ, 无循环.
- ✓ **强度估算明确**: Higher² 给出 ψ((Ω_Ω+1)+(Ω_(ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1)))+1))) 量级, **严格大于 Higher.agda** 的 ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))).
- **Phase 6 自然延展**: 写 `module Higher^ (n : ℕ)` 参数化生成 Higher^n, outer `lim n` 给 Higher^ω ≈ ψ(Ω_(Ω+ω)). 工程量预计 100-200 LOC.

### 2.3 强度位次 (实测)

| 来源 | 强度 |
|------|------|
| BTBO | ψ(Ω_Ω) |
| Higher.agda | ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) — ggg 社区估算 |
| **Phase 5B (Higher²)** | **ψ((Ω_Ω+1)+(Ω_(Higher.agda+1)))** — 严格 > Higher.agda |
| Phase 6 Higher^ω (推荐主线) | ψ(Ω_(Ω+ω)) |
| Higher^Ωᴰ (Phase 7 推测) | ψ(Ω_(Ω·2)) |

## 3. Path C 实测: Opᴹ 语义化 ✗ 撞 Agda 终止墙

### 3.1 落地

[Phase5C_OpInterp.lagda.md](Phase5C_OpInterp.lagda.md), ~120 行, 编译通过 (但**核心目标失败**).

落地内容:
- ✓ ⟦_⟧ : Opᴹ → Ordᴹ → Ordᴹ v0 (`⟦ op c g ⟧ a = a` constant identity) 编译通过.
- ✗ **ψ_M-C 用 ⟦_⟧ 驱动失败**: `ψ_M-C (mahlo f a _ _) = ψ_M-C (⟦ f ⟧ a)` Agda 终止检查拒绝 (即使 v0 ⟦_⟧ 是 identity, 终止检查器不展开 ⟦_⟧).
- ◯ **绕过**: inline ⟦_⟧ v0 的逻辑到 ψ_M-C 自身的 pattern match (`ψ_M-C (mahlo (op c g) a _ _) = ψ_M-C a`), 编译通过, 但 ⟦_⟧ 在 ψ_M-C 中**没有真正被使用**.

### 3.2 关键负面发现

**Agda 句法终止检查不展开函数调用**. 这意味着即使 ⟦_⟧ 在语义上保证 `⟦ f ⟧ a` 是 `a` 的 (或更小的) 子项, Agda 看到 `ψ_M-C (⟦ f ⟧ a)` 时, 只识别"递归调用的输入是 `⟦ f ⟧ a`", 不是 `mahlo f a _ _` 的句法子项. 拒绝.

要让 ⟦_⟧ 真正驱动 ψ_M, 必须借助:
1. **Well-founded recursion**: 显式 well-founded measure (e.g., a's `level` 或 `<ᴹ-bounded`-depth).
2. **Sized types**: `--sized-types` 标记 ⟦_⟧ 的输出 size, 与项目 `--safe --without-K` 兼容性需评估.
3. **Inline 全部 Opᴹ case**: 把 ⟦_⟧ 的所有 op c g 展开到 ψ_M 的 pattern match. 限制性太强.
4. **重构 mahlo 字段**: 把 f 改为更受约束的类型 (例如直接的 "(a' : Ordᴹ) → a' <ᴹ a → Ordᴹ" 减小映射). 但这相当于退回 Phase 4 不带语义的设计.

**Phase 6 路径 C 真正落地需 ~500-900 LOC** (well-founded recursion 框架 + ⟦_⟧ 非平凡版本 + 单调性证明). 与 Plan agent C 估算一致.

### 3.3 当前 spike 价值

| 项 | 价值 |
|----|------|
| ⟦_⟧ 自身可定义 | ✓ 验证 post-mutual 函数兼容 8 层 mutual block |
| ψ_M-C 与 ⟦_⟧ 集成 | ✗ **Agda 终止检查阻拦, 这是 Phase 6 主险, 必须早期识别** |
| 强度增量 | 0 (退化为内联版 ≈ Phase 4 v1) |

## 4. 三路径强度对照表

| 来源 | 强度 | LOC | Phase 5 状态 |
|------|------|-----|-------------|
| BTBO | ψ(Ω_Ω) | (主线) | — |
| Higher.agda | ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) | 50 | 已有 |
| Phase 4 (Mahlo 之前路径终点) | ≲ Higher.agda | ~550 (累积) | 已有 |
| **Phase 5B Higher² spike** | **>** Higher.agda | 60 (新增) | ✓ |
| Phase 5A Sub-Ord spike | 未演示 (留 Phase 6) | 85 | 部分 |
| Phase 5C ⟦_⟧ toy spike | 0 增量 (撞墙) | 120 | 失败 |
| Phase 6 Higher^ω (推荐) | ψ(Ω_(Ω+ω)) | ~200-300 (预计) | 待 Phase 6 |
| 远期 真 Setzer Mahlo | ψ(M) | ~3000+ (研究级) | 远期 |

## 5. Phase 6 主线推荐

### 5.1 推荐: **Path B (Higher^n / Higher^ω 完整迭代)**

理由:
1. **Phase 5 实测确认**: B spike 一次性 60 行就给出"严格超 Higher.agda"的强度 binding. 模板 100% mechanical, 没有概念性风险.
2. **可参数化**: Phase 6 可写 `module Higher^ (n : ℕ) where ...` 一键生成 Higher^n. Higher^ω 直接外层 `lim n`. 工程量 200-300 LOC.
3. **强度增量可量化**: 每迭代 1 级, 接近 1 个 Ω-bump. Higher^ω 触达 ψ(Ω_(Ω+ω)).
4. **风险低**: 无 Agda 终止 / positivity 险, 全部跑通仿 Higher.agda.

### 5.2 不推荐: A 长期 / C 高险

- **Path A**: 结构 spike 通过, 但 ψ_M 设计完全开放. 需要在 Ord ℓ 上重新建立 mono / trichotomy 机制 — 与 Phase 2 的 `<ᴹ-dec` 死墙同性质. 投入大, 收益不确定.
- **Path C**: 撞 Agda 终止墙. 要真正落地需 Well-founded recursion 框架, 项目当前 `--safe --without-K` 下未引入. 研究级投入 ~500-900 LOC, 风险高.

### 5.3 Mahlo 路径的总结判断 (Phase 1-5)

| 阶段 | LOC | 强度 |
|------|-----|------|
| Phase 1-4 (Mahlo 主线) | ~550 | ≲ Higher.agda |
| Phase 5A (Sub-Ord) | 85 | 未演示 |
| Phase 5B (Higher² 旁路) | 60 | **> Higher.agda** |
| Phase 5C (Opᴹ 语义) | 120 | 撞墙, 无增量 |

**结论**: 5 个 Phase 的 Mahlo 探索告诉我们, **Mahlo 形式化在 Agda `--safe --without-K` 下结构性受限** — 无法在合理工程量下超过 Higher.agda. 实际超过 Higher.agda 的路径不在 Mahlo, 而是**继续迭代 Higher.agda 已建立的 ψ<Ω 模板**.

**Mahlo 形式化的价值在结构性贡献** (IR-Mahlo MLQ 编码, Sub 内禀序 `<ˢ`, monoSub, level rank, ⟦_⟧ post-mutual 函数), **不在 ordinal 强度**.

## 6. 文件清单

Phase 5 新增:
- [Phase5A_SubOrd.lagda.md](Phase5A_SubOrd.lagda.md) — Path A spike (Sub Ord-indexed)
- [Phase5B_HigherIter.lagda.md](Phase5B_HigherIter.lagda.md) — Path B spike (Higher² 迭代)
- [Phase5C_OpInterp.lagda.md](Phase5C_OpInterp.lagda.md) — Path C spike (Opᴹ 语义 v0)
- [FINDINGS_Phase5.md](FINDINGS_Phase5.md) — 本报告

历史 (不动):
- Phase1.lagda.md (Brouwer-MLQ 骨架), Phase2.lagda.md (partial trichotomy), Phase3.lagda.md (strat full trichotomy), Phase4.lagda.md (去 strat + level + ψ_M)
- FINDINGS.md, FINDINGS_Phase2.md, FINDINGS_Phase3.md, FINDINGS_Phase4.md

全部通过 Agda 2.8.0 + stdlib 2.3 + cubical 0.9 + `--safe --without-K --cubical-compatible --lossy-unification --hidden-argument-puns` 编译. 无 postulate, 无 unsafe.
