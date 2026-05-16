# IR-Mahlo 探索: 诊断报告

> [../Naive/FINDINGS.md](../Naive/FINDINGS.md) 把 IR-Mahlo (Setzer 1998) 标为"研究级数千行但结构上可走". 本次实测验证, 并补关键修正: **Setzer 教科书直译被 Agda positivity 拒, 但 Takahashi 2024 (MLQ 互递归分解) 在我们 flag 下可行**.
>
> 工作基底: [Phase1.lagda.md](Phase1.lagda.md).

## 0. TL;DR

- **失败**: V1 (`mahlo : (Ordᴹ → Ordᴹ) → Ordᴹ`) 与 V3/V3' (Setzer 教科书 IR-Mahlo, `mahlo : ((a:U) → (T a → U) → U) → U`) 全部 Agda positivity 拒.
- **关键发现**: Takahashi 2024 ([arxiv 2402.15074](https://arxiv.org/abs/2402.15074), [code](https://github.com/takahashi-yt/large-universes)) 给出可行编码 —— 引入互递归 `ℚ` universe 代理"𝕄 上的算子", 把 `𝕄 → 𝕄` 改走 `𝕄 ↔ ℚ` 路径. 实测在 `--safe --without-K --cubical-compatible` 下编译.
- **对 FINDINGS.md §6 行 E 的修正**: 不是"Agda 堵死", 而是"研究级数千行 + 必须用 MLQ 风格, 不是 Setzer 直译".

## 1. 隔离测试: IR 本身工作

在临时文件中测经典 Setzer Π-universe (无 Mahlo):

```
mutual
  data U : Set
  T : U → Set
  data U where
    nat : U
    pi  : (a : U) → (T a → U) → U
  T nat = ℕ
  T (pi a b) = (x : T a) → T (b x)
```

通过编译. IR 在项目 flag 下功能完整, 问题不在 IR 本身.

## 2. 失败变体: 朴素 / IR-decoder / Setzer 教科书

### V1: 朴素 — `mahlo : (Ordᴹ → Ordᴹ) → Ordᴹ`

直接被 positivity 拒: `Ordᴹ is not strictly positive, because it occurs to the left of an arrow`.

### V3: IR-Brouwer with decoder — `mahlo : ((α:Ordᴹ) → El α → Ordᴹ) → Ordᴹ`

希望 IR decoder `El` 把负位置"漂白". 不奏效: Agda 报错相同.

### V3': Setzer 1998 教科书 — `mahlo : ((a:U) → (T a → U) → U) → U`

完整 typed-universe, IR + Mahlo. 仍然 `U is not strictly positive`. 这说明问题不是 Brouwer-vs-typed, 是构造子结构性形状.

### V4: 双数据 SubM 替代 El

`(α:Ordᴹ) → SubM α → Ordᴹ` 形状不变. 不另测.

### 失败根源

Agda positivity 允许"`(a : 本类型) → ...`"作 IR 顶层 Pi binder, 但**嵌套在函数参数内**就拒. 而 Mahlo 数学结构强制要求后者: "对任意 universe-函数, sub-universe 闭合". 直译走不通.

## 3. 通过变体

### V2: Ordᴰ-分层 (Higher.agda 同款, 不是 Mahlo)

```
mahlo : (α : Ordᴰ) → (Ord α → Ordᴹ) → Ordᴹ
```

定义域是外部 `Ord α`, 不是整个 `Ordᴹ`. 没有自反性. 强度 < ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))), 远未达 Mahlo cardinal.

### V5: Takahashi MLQ 分解 (真正的 IR-Mahlo)

**关键技巧**: 引入第二个互递归 universe `Opᴹ` 代理"`Ordᴹ` 上的算子". `Ordᴹ → Ordᴹ` 走 `Ordᴹ ↔ Opᴹ` 双向. mahlo 构造子接收 `Opᴹ` (positive in Ordᴹ).

具体代码见 [Phase1.lagda.md](Phase1.lagda.md). 通过我们的 flag 下编译.

这是 Takahashi 称的 "external Mahlo universe", 在 Setzer 意义下 proof-theoretically weaker than 完整内部 MLM, **但结构上是 Mahlo** (有 sub-universe reflection).

### V6: External 参数化 (较弱)

Mahlo 函数 `f` 作 `data 𝕌m (f : ...) : Set` 的 PARAMETER (非 constructor field). 通过编译但 f 固定, 比 V5 弱. 不在工作基底中保留.

## 4. 关键技术对比

| 编码方式 | 例子 | Agda 评判 | 强度 |
|---------|------|---------|------|
| 直接 `(U → U) → U` | V1 朴素 | ✗ positivity | — |
| IR + Set decoder, `((α:U) → El α → U) → U` | V3, V3' | ✗ positivity | — |
| 外部指标 `(α:Ext) → (... → U) → U` | V2, Higher.agda | ✓ | < Mahlo |
| **MLQ 互递归** | V5 (Takahashi) | ✓ | **真 Mahlo (external)** |
| External 参数化 | V6 (Takahashi) | ✓ | 较弱 Mahlo |

**真正的诊断**: Agda positivity 不允许 `(自身 → 自身) → 自身`, 包括 IR decoder 版. 但**可以**用第二个互递归类型代理"函数空间" (MLQ), 或把函数移到 data 外部参数 (External). Mahlo 形式化要"换框架"而非"补构造子".

## 5. 与 FINDINGS.md §6 结论的对比

| 方向 | 难度 | 改原框架 | 终点 | 备注 |
|------|------|--------|------|------|
| A. `Ordᴰ` 加 `_⊔_` | 高 | 是 | 不一定通 | 同 `<-dec` 死循环 |
| B. `limΩ` 加上界存在性参数 | 中 | 是 | 调用方负担 | 改 lim 语义 |
| C. 改 `<` 定义 | 高 | 是 | 不确定 | 推翻基础 |
| D. 不依赖三歧的 ψ-1 | 极高 | 否 | 可能不行 | OCF 普遍依赖三歧 |
| **E. IR-Mahlo (Takahashi MLQ 风格)** | **极高 (研究级)** | 是 | **可达 ψ(M_ext)** | **本次确证可行** |
| F. IR-Mahlo (Setzer 直译) | 不可 | — | positivity 拒 | 本报告 §2 验证 |
| G. 换 Coq/Lean | 极高 | 重写 | 可能更易 | 离开 Agda 生态 |

E ≠ F: E 是 MLQ 风格 (本次找到), F 是教科书直译 (本次否定).

## 6. Phase 2 路线 (~2000-3000 LOC 估)

工作基底 [Phase1.lagda.md](Phase1.lagda.md) 已搭好 Brouwer-MLQ 骨架. Phase 2:

1. **填 `Sub (mahlo f a b)`** 非平凡定义. Takahashi paper §2.1 的 reflection rule.
2. **加 `_<ᴹ_`** 跨 `Ordᴹ`/`Opᴹ` 互递归.
3. **加 mono 条件** 到 lim/mahlo. 互递归层数从 3 涨到 6.
4. **Bounded trichotomy** 尝试. 预期最大墙 (函数外延性在 mahlo 节点比较时浮现).
5. **ψ_M collapser** 仿 [Higher.agda:31-38](../../Higher.agda#L31-L38).

Step 1-2 大概率通 (Takahashi 示范过). Step 3-4 是真正研究. Step 5 取决于 4. (术语: "Step N" 指本节列出的 5 个子步; "Phase N" 指项目阶段, 见 [Phase2.lagda.md](Phase2.lagda.md) 顶部.)

### 6.1 Phase 2 实测 (2026-05-11)

实施于 [Phase2.lagda.md](Phase2.lagda.md), 诊断报告 [Phase2.lagda.md](Phase2.lagda.md).

- ✓ Step 1-2 通过 (Takahashi 示范一致).
- ⚠️ Step 3 部分通过 (lim 带 monoᴺ, mahlo 未带 monoSub — `Sub a` 内禀序构造循环依赖).
- ⚠️ Step 4 结构性卡死: mahlo 4 子 case 中 3 blocked, 退回 Maybe-partial. 与 Naive `+-lmono` 死墙同构.
- ✗ Step 5 跳过 (Step 4 partial → collapser 不可定).

修正原估算 "Step 3-4 真正研究" → **Step 4 在当前 mahlo 字段形状下不可证, 需先扩 Sub-内禀序 + monoSub (项目 Phase 3, Takahashi 2024 未覆盖)**.

### 6.2 Phase 3 实测 (2026-05-11)

实施于 [Phase3.lagda.md](Phase3.lagda.md), 诊断报告 [Phase3.lagda.md](Phase3.lagda.md).

3a (Sub 内禀序 + monoSub) + 3b (strat 字段) 一并落地. 互递归扩到 8 层. `<ˢ` 用 IR 函数版本 (与 Sub 同构), 不需要 fallback 到 data 版.

- ✓ 3a `<ˢ`: IR-recursive on `a`, mahlo case 字典序 + subst. **计划风险 #1 (终止性) 未触发** — Agda 接受, 与 Sub 同结构.
- ✓ 3a monoSub 字段: `∀ {s s'} → s <ˢ s' → b s <ᴹ b s'` 烤进 mahlo.
- ✓ 3b strat 字段: `∀ s → a <ᴹ b s` 桥接 mahlo-a/mahlo-b cross-case.
- ✓ `<ˢ-dec`: 无条件三歧, 结构归纳 a.
- ✓ Step 4 `<ᴹ-dec` 全函数 (4/4 mahlo 子 case 全通, 无 Maybe).
- ⏸ Step 5 ψ_M: 占位, 待下一轮 commit.

**语义代价 (重要)**: strat 字段强制 `a < b s` 对所有 s, 把"真 Mahlo"弱化为 stratified Σ-reflect, 强度 ≲ Higher.agda 的 ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))), 远小于 ψ(M_真). Setzer 1998 不要求此条件; 这是 Phase 3 用强度换操作的妥协, 标识为"弱 Mahlo OCF". 详 [Phase3.lagda.md "3b strat 字段的语义代价"](Phase3.lagda.md).

### 6.4 Phase 5 三路径 spike (2026-05-12)

并行探索 [Phase5A_SubOrd.lagda.md](Phase5A_SubOrd.lagda.md), [Phase5B_HigherIter.lagda.md](Phase5B_HigherIter.lagda.md), [Phase5C_OpInterp.lagda.md](Phase5C_OpInterp.lagda.md). 各 spike 文件内置个体实测.

- ✓ **B (Higher² 迭代)** 60 LOC spike **明确超过 Higher.agda** — Phase 6 主线推荐.
- ◯ **A (Sub Ord-indexed)** 85 LOC, 结构通, ψ_M 留 Phase 6, 强度未演示.
- ✗ **C (Opᴹ 语义化)** 120 LOC, 撞 Agda 终止检查 — `ψ_M-C (mahlo f a _ _) = ψ_M-C (⟦ f ⟧ a)` 即使 v0 ⟦_⟧ 是 identity, Agda 不展开. Path C 需 Well-founded recursion 框架 (500-900 LOC Phase 6+).

**Mahlo 路径总结判断**: 5 个 Phase ~770 LOC 后, 唯一明确超过 Higher.agda 的是 **Phase 5B 旁路** (不走 Mahlo, 复用 Higher.agda 模板迭代). Phase 6 推荐放弃 Mahlo 主线, 走 Higher^n / Higher^ω.

#### Phase 5 三路径对比表 (cross-file 结论)

| 路径 | 编译 | 强度 demo binding | 核心目标达成? | 推荐 |
|------|------|-------------------|--------------|------|
| **B (Higher² 迭代)** | ✓ | `lim (n → ψ₀ (ψ<Ω² {n} ΩΩ²))` 顶级 binding | ✓ 明确超过 Higher.agda | **★ Phase 6 主线** |
| **A (Sub 升级 Ord-indexed)** | ✓ (结构) | sample `M-test`, 无 ψ_M | ⚠️ 结构落地, 强度未演示 | 长期备选 |
| **C (Opᴹ 语义化 v0)** | ✓ (内联绕过) | ⟦_⟧ 独立可用, ψ_M-C 退化等价 Phase 4 | ✗ **核心模式 Agda 拒绝** | 不推荐 (除非引入 Well-founded recursion) |

#### 三路径强度位次对照

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

#### Phase 6 主线推荐: Path B (Higher^n / Higher^ω 完整迭代)

理由:

1. **Phase 5 实测确认**: B spike 一次性 60 行就给出"严格超 Higher.agda"的强度 binding. 模板 100% mechanical, 没有概念性风险.
2. **可参数化**: Phase 6 可写 `module Higher^ (n : ℕ) where ...` 一键生成 Higher^n. Higher^ω 直接外层 `lim n`. 工程量 200-300 LOC.
3. **强度增量可量化**: 每迭代 1 级, 接近 1 个 Ω-bump. Higher^ω 触达 ψ(Ω_(Ω+ω)).
4. **风险低**: 无 Agda 终止 / positivity 险, 全部跑通仿 Higher.agda.

#### 不推荐: A 长期 / C 高险

- **Path A**: 结构 spike 通过, 但 ψ_M 设计完全开放. 需要在 Ord ℓ 上重新建立 mono / trichotomy 机制 — 与 Phase 2 的 `<ᴹ-dec` 死墙同性质. 投入大, 收益不确定.
- **Path C**: 撞 Agda 终止墙. 要真正落地需 Well-founded recursion 框架, 项目当前 `--safe --without-K` 下未引入. 研究级投入 ~500-900 LOC, 风险高.

#### Mahlo 路径的总结判断 (Phase 1-5)

| 阶段 | LOC | 强度 |
|------|-----|------|
| Phase 1-4 (Mahlo 主线) | ~550 | ≲ Higher.agda |
| Phase 5A (Sub-Ord) | 85 | 未演示 |
| Phase 5B (Higher² 旁路) | 60 | **> Higher.agda** |
| Phase 5C (Opᴹ 语义) | 120 | 撞墙, 无增量 |

**结论**: 5 个 Phase 的 Mahlo 探索告诉我们, **Mahlo 形式化在 Agda `--safe --without-K` 下结构性受限** — 无法在合理工程量下超过 Higher.agda. 实际超过 Higher.agda 的路径不在 Mahlo, 而是**继续迭代 Higher.agda 已建立的 ψ<Ω 模板**.

**Mahlo 形式化的价值在结构性贡献** (IR-Mahlo MLQ 编码, Sub 内禀序 `<ˢ`, monoSub, level rank, ⟦_⟧ post-mutual 函数), **不在 ordinal 强度**.

### 6.3 Phase 4 实测 (2026-05-12) — 诚实负面结果

实施于 [Phase4.lagda.md](Phase4.lagda.md), 诊断 inline 在该文件.

Phase 4 转向: **去 strat**, 接受 `<ᴹ-dec` partial. 引入 `level : Ordᴹ → Ordᴰ` rank 函数 + ψ_M (v1 简单版 / v2 level-bumped 版) 直接输出到 Ord₀.

- ✓ 4a 去 strat: mahlo 5 → 4 字段. `<ᴹ-dec?` mahlo cross-case 退回 `nothing`. monoSub + `<ˢ` 保留.
- ✓ 4b `level`: 结构归纳, mahlo +1 rank, lim cumsum 单调化.
- ✓ 4c-v1 ψ_M: 用 `ψ₀ ∘ Ω ∘ ordᴰ` 模板 (与 BTBO `ψⁿ` 同), 强度 ≈ BTBO.
- ✓ 4c-v2 ψ_M: mahlo Ω-index 加 level 贡献, 强度 ≈ ψ(Ω_(BTBO + ω)).
- ✗ 4c-v3 Sub-enum: 未实现, 但结构上仍是 ℕ-cofinal, 不会超过 Higher.agda.

**核心负面结论**: Phase 4 v1/v2 编译通过, **但实际强度 ≲ Higher.agda**. 与 plan 目标 ψ(Ω_(Ω+ω)) 有差距. 原因结构性 — `Sub a = Σ ...` 是 Σ-平铺, 索引能力 = ℕ, 不足以驱动 Ord-tree-indexed limit. 

**累积代价**: Phase 1-4 共 ~550 LOC, 强度上限 ≲ Higher.agda 的 50 行. **Mahlo 路径在当前 Sub-Σ 设计下饱和**, Phase 5 需结构性改向 (Higher^n 迭代 / Sub 升级 / Opᴹ 语义化). 详 [Phase4.lagda.md "Phase 5 候选路径"](Phase4.lagda.md).

## 7. 对作者的建议

1. **更新 [../Naive/FINDINGS.md](../Naive/FINDINGS.md) §6 行 E**. 标"研究级数千行 + 必须 Takahashi 2024 MLQ 风格 (不能 Setzer 1998 直译)".
2. **Phase 2 起步参考 [Phase1.lagda.md](Phase1.lagda.md)** 的骨架, 与 Takahashi paper §2.1 的 reflection 部分对照阅读.
3. **风险**: Step 4 (bounded trich on mahlo 节点) 是预期撞墙位置; 即使 Takahashi 2024 也未做这部分 (他做的是类型论解释, 不需 bounded trich).
4. **保守 fallback**: 若决定不走 Mahlo, V2 同类的"逐级加外部指标" ([Higher.agda](../../Higher.agda) 套路) 可继续推, 强度增益有限但累积可观.

## 8. 文件清单

- [Phase1.lagda.md](Phase1.lagda.md): Phase 1 工作基底, Brouwer-MLQ 骨架, 编译通过.
- [Phase2.lagda.md](Phase2.lagda.md): Phase 2 升级 (Sub Σ-closure, `<ᴹ`/`<ᴼ`, lim monoᴺ, partial trichotomy), 编译通过.
- [Phase3.lagda.md](Phase3.lagda.md): Phase 3 突破 (Sub 内禀序 `<ˢ` + monoSub + strat, full `<ᴹ-dec`), 编译通过. 弱化为 stratified Mahlo.
- [Phase4.lagda.md](Phase4.lagda.md): Phase 4 去 strat + level + ψ_M v1/v2 直接到 Ord₀, 编译通过. **强度 ≲ Higher.agda — 诚实负面结果**.
- [Phase5A_SubOrd.lagda.md](Phase5A_SubOrd.lagda.md): Phase 5 Path A spike, Sub 升级到 Ord-indexed, 85 LOC, 结构通无 ψ_M.
- [Phase5B_HigherIter.lagda.md](Phase5B_HigherIter.lagda.md): Phase 5 Path B spike, Higher² 迭代, 60 LOC, **超过 Higher.agda**.
- [Phase5C_OpInterp.lagda.md](Phase5C_OpInterp.lagda.md): Phase 5 Path C spike, Opᴹ 语义 v0, 120 LOC, 撞 Agda 终止检查.
- [Phase2.lagda.md](Phase2.lagda.md): Phase 2 实施日志 + Step 4 死墙诊断.
- [Phase3.lagda.md](Phase3.lagda.md): Phase 3 实施日志 + 语义代价分析.
- 本报告.

无 `postulate`, 无 `--unsafe`, 通过 Agda 类型检查.

## 9. 文献

- **Takahashi 2024**: "Interpretation of Inaccessible Sets in Martin-Löf Type Theory with One Mahlo Universe". arxiv [2402.15074](https://arxiv.org/abs/2402.15074). LMCS Vol. 21 Issue 4, 2025. Agda 代码: [takahashi-yt/large-universes](https://github.com/takahashi-yt/large-universes).
- **Setzer 1998**: "Extending Martin-Löf type theory by one Mahlo-universe".
- **Dybjer-Setzer 2003**: "Indexed Induction-Recursion".
- **Rathjen 1991**: "Proof-Theoretic Analysis of KPM".

## 副作用

未修改 BTBO/Higher 等主线模块. `agda-googology.agda-lib` 的 stdlib 2.2→2.3 / cubical 0.8→0.9 是 FINDINGS.md 阶段做的, 是否回滚由作者决定.
