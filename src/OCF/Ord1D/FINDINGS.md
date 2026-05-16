# Ord₁ᴰ 探索 — Phase A 五版本 spike umbrella

类比 BTBO 中 `Ord₀ + monotonic = Ordᴰ` (满足 BoundedTrich, ψ(Ω_Ω) 强度), 探索给 [`Ord₁`](../BTBO.lagda.md#L91) 添加结构使其满足 BoundedTrich, 命名为 **Ord₁ᴰ**. 强度目标: ψ(Ω_Ω_2) (用户论证: 在 Ord₁ᴰ 上重做 Ord-Ord 模块).

## Phase A 五版本对照表

| Spike | 设计核心 | 编译 | BoundedTrich | 强度可达 | 状态 |
|-------|---------|------|------------|---------|------|
| [A₁](SpikeA1.lagda.md) | mono on Ord₀ | ✓ | ✗ Maybe-wrap | — | 历史撞墙重验证 → Ord₀ 不可决策 |
| [A₂](SpikeA2.lagda.md) | mono on Ordᴰ, 无 γ-bound | ✓ | ✗ Maybe-wrap | — | 历史撞墙重验证 → 无上界证据 |
| [A₃](SpikeA3.lagda.md) | γ-bounded + mono + PI | ✓ | **✓ 全函数** | **ψ(Ω_Ω_2)** | **主推方向** |
| [β](Spikebeta.lagda.md) | IR Ord₁ᴰ ⇄ ψ₁ | ✓ | ≈ (ψ-诱导,弱) | Ordᴰ (坍缩) | 双重撞墙 (强度+关系不真) |
| [ε](Spikeepsilon.lagda.md) | Witness as field | ✓ | ✓ 形式上 | 同 A₃ if 可构造 | witness 构造层等价 A₃ |

## 关键 findings

### 1. A₁/A₂ 历史撞墙的精确诊断

- **A₁**: Ord₀ 上根本无 < 决策器. 这是 Brouwer-tree paradigm 的基础限制 — BTBO 设计 Ordᴰ 而非给 Ord₀ 加 mono, 就是因为 Ord₀ 不可救.
- **A₂**: Ordᴰ 上有 BoundedTrich (`<-dec`), 但是 conditional — 需共同上界 γ. lim₁ 节点局部不提供 γ.
- **区分**: A₁ 是"无决策器", A₂ 是"决策器存在但无条件证据". 与 [Mahlo Phase 2](../PastBTBO/Mahlo/Phase2.lagda.md#L115) (Sub α 无序) **不同**:
  - Mahlo: 索引空间结构上无序
  - A₂: 索引空间有 BoundedTrich, 缺局部上界
  - 这意味着 A₂ 的修复路径 (注入 γ 上界 = A₃) 与 Mahlo 不同, 不能套用 Mahlo 的"已死"结论

### 2. A₃ 走通的关键设计

```agda
data Ord₁ᴰ where
  ...
  lim₁ : (γ : Ordᴰ) (f : (α : Ordᴰ) → α < γ → Ord₁ᴰ)
         (mono₁ : Mono₁ᵧ γ f) (pi₁ : PIᵧ γ f) → Ord₁ᴰ
```

三个字段共同支撑 BoundedTrich:
- **γ**: 共同上界, 修复 A₂ 的"无上界"撞墙
- **mono₁**: Ordᴰ 索引内 `α < β` 推 Ord₁ᴰ 上 `f α pα <₁ f β pβ`
- **pi₁** (proof-irrelevance): 处理 `<-dec pα pβ` 的 `injᶜ refl` case, 即 α ≡ β 但 pα ≠ pβ 时, `f α pα ≡ f α pβ`

实测 [`<₁-dec`](SpikeA3.lagda.md) 全函数通过, 无 Maybe-wrap / partial / TERMINATING. 这是 Ord₁ᴰ 的工程可行方案.

### 3. β/ε 真正全新方向的内在限制

**β (IR Ord₁ᴰ ⇄ ψ₁)**: 用 ψ₁ 折叠 image 诱导 _<₁_. 撞两堵墙:
- 强度坍缩: ψ₁ (lim₁ f m) 不能输出 Ord₀-索引信息到 Ordᴰ (Ordᴰ 只有 ℕ-索引 lim). 取 `ψ₁ (f zero)` 等坍缩方案 → 强度降为 Ordᴰ.
- 关系不真: ψ₁ 非单射, 诱导 _<₁_ 上 BoundedTrich 的 `a ≡ b` 分支退化为 `ψ₁ a ≡ ψ₁ b`, 不能区分 distinct 项.

**修复方向**: 如果 ψ₁ 输出参数化 (像 [Higher.agda](../Higher.agda) 的 ψ<Ω), 撞墙消失 — 但这就是 Higher.agda 的复刻, 不是 Ord₁ᴰ 设计.

**ε (Witness as field)**: BoundedTrich 形式上证 (witness 直接给 image trichotomy), 但 witness 的构造性撞墙:
- 任意 `f : Ord₀ → Ord₁ᴰ` 的 `Witness₁ f` 不可构造 (等价于 Ord₀ trichotomy, 违 Brouwer paradigm)
- 只能从 γ-bounded f 推 witness, 退化到 A₃

### 4. 强度阶梯 (Phase A 后修订)

| 阶梯 | 实现 | 强度 |
|------|------|------|
| BTBO | Ordᴰ + Ord-Ord | ψ(Ω_Ω) = ψ(Ω_(Ω_1)) |
| Higher.agda | OrdΩ + ψᴰ 单一序列 | ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) ≈ ψ(Ω_(Ω+1)) |
| HigherOrdᴰ | OrdH α 参数化 | ψ(Ω_(Ω+ω)) |
| **Ord₁ᴰ A₃** (Phase C 目标) | γ-bounded + Ord-Ord-on-Ord₁ᴰ | **ψ(Ω_Ω_2) = ψ(Ω_(Ω_2))** |

Ord₁ᴰ 在新的强度轴上: **ψ(Ω_(Ω_α))** (而 HigherOrdᴰ 是 ψ(Ω_(Ω+α))).

## Phase B/C 路线

- Phase B: 完整 [BoundedTrich.lagda.md](BoundedTrich.lagda.md) — A₃ 设计 + 完整辅助引理 (f<l₀, f<l₁, _+_ 等)
- Phase C: [OrdOrd.lagda.md](OrdOrd.lagda.md) — 把 [BTBO Ord-Ord 模块](../BTBO.lagda.md#L836-L944) 在 Ord₁ᴰ-A₃ 上重做, ψ₁ 折叠链 → 强度突破 ψ(Ω_Ω_2)

Phase D-F (Ord_n ᴰ 机械迭代 / Ord_ω ᴰ 参数化) 延后, 视 Phase C 结果决定.
