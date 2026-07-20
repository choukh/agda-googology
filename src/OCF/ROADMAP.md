# OCF 强度路线图: 从 BTBO 到 ψ(Ω_Ω_Ω) (以及为什么走不到)

> 本文是基于 Phase 1-6 实测 (Phase 1-5 PastBTBO Mahlo 探索 + Phase 6 HigherOrdᴰ 一般化) 的**结构性洞察 + 未来路线图**.
>
> **⚡ 2026-07-20 重大更新**: 本文的全部"不可达"结论只对 **范式 A (Brouwer 树)** 成立.
> [Notation/](Notation/) (范式 B, 有限项表记系统) 已实测: §3.3 的"终极目标" ψ(Ω_Ω_Ω) 在范式 B 中是一个
> 具体的项, Mahlo 级三歧性是 ~60 行可判定函数, 真 Mahlo 语法/序/对角折叠全部编译通过. 详见 §9 与
> [Notation/FINDINGS.md](Notation/FINDINGS.md). 本文其余部分保留为范式 A 的边界定理记录.
>
> 核心命题: Agda `--safe --without-K` 下, OCF 强度的可达性**结构性受限于"trichotomy 是否能降维到一个全序索引集"**. Higher.agda 路线避开了 Mahlo 撞过的 BoundedTrich 屏障, 但**会在 Veblen / 不动点级别重新撞同样的墙**, 大致在 ψ(Ω_(Ω^Ω)) 附近.

## 1. 核心洞察: 为什么 Higher 走得通, Mahlo 走不通

### 1.1 BoundedTrich 屏障的本质

BTBO 的 `<-dec : ∀ {a b c} → a < c → b < c → a < b ⊎ b < a ⊎ a ≡ b` 是 **bounded**: 必须有共同上界 c. 这是 Brouwer 树 ψ-OCF 形式化的核心 dispatch 机制.

**屏障触发条件**: 当 ψ-collapse 在某个构造子上需要比较两个 witness `p : a <ᴹ c` 与 `q : b <ᴹ c'`, 而 c ≠ c' 且无自然共同上界时.

### 1.2 Mahlo 撞墙路径

Mahlo `mahlo : Opᴹ → (a : Ordᴹ) → (b : Sub a → Ordᴹ) → ...` 的 `<ᴹ-dec` 4 子 case:

| sub-case | bound 1 | bound 2 | 同根? |
|----------|---------|---------|-------|
| (mahlo-a, mahlo-a) | a₀ | a₀ | ✓ |
| (mahlo-a, mahlo-b s) | a₀ | b s | ✗ **跨家族** |
| (mahlo-b s, mahlo-b s') | b s | b s' | ✗ **s ≠ s' 跨函数像** |

`b : Sub a → Ordᴹ` 是**任意函数**, 像点之间无序. **不可解** without 添加约束 (Phase 3 strat 即此, 代价是弱化 Mahlo 语义).

### 1.3 Higher 绕过路径

Higher.agda 的 `limₙ : (p : ℓ < ψᴰ n) (f : Ord ℓ → OrdΩ) → OrdΩ`:

- `ψᴰ : ℕ → Ordᴰ` 是**单一 ℕ-monotone 序列**, 不是任意函数
- 两个 `limₙ {m} p f` 与 `limₙ {m'} p' f'` 的 bound 都是 `ψᴰ` 在不同 ℕ 点的取值
- `ψ<Ω` dispatch 用 `<ᴺ-dec m m'` — **ℕ 上 unconditional trichotomy**

**关键技巧**: 把"宽度"全部压缩进**单一 ℕ-monotone 序列**, trichotomy 降维到 ℕ. 即使 BTBO 的 Ord ℓ 是 bounded-trich, 它的层级 ψᴰ 是 ℕ-indexed, ℕ 上有 unconditional trich, 屏障被绕开.

### 1.4 结构对比表

| 框架 | 宽度索引来源 | trichotomy 所在域 | 屏障状态 |
|------|------------|------------------|---------|
| **Naive (PastBTBO/Naive Phase 1)** | `limΩ x` 中 x : Ordᴰ 任意 | Ordᴰ (bounded only) | ✗ 撞墙: +-lmono 不真 |
| **Mahlo (PastBTBO/Mahlo Phase 2-4)** | `b : Sub a → Ordᴹ` 任意函数 | Sub a (unconditional <ˢ-dec) 但跨 a/b 家族无解 | ✗ 撞墙: 跨家族 |
| **Higher.agda** | `ψᴰ : ℕ → Ordᴰ` 单调 | ℕ (unconditional <ᴺ-dec) | ✓ 通过 |
| **HigherOrdᴰ (Phase 6.2)** | `ψᴰ-at α : ℕ → Ordᴰ` (α-参数化单调) | ℕ (unconditional) | ✓ 通过 (α 是参数, 不参与 dispatch) |

**核心定律**: ψ-collapse 的 limₙ-style 构造子可行 ⟺ **bound 域是带 unconditional trichotomy 的全序集** (典型: ℕ). 一旦 bound 域是任意函数像 (Mahlo) 或非全序的 (任意 Ord), 屏障重现.

## 2. 当前可达点 (Phase 6.2)

```
Phase 6.2 HigherOrdᴰ: OrdH α 单一数据类型, α : Ordᴰ 参数化
  顶级 binding: Higher^ω = lim (ψⁿ-at ω-asᴰ)
  估算强度: ψ(Ω_(Ω+ω))
  实际可推到: Higher^BTBO ≈ ψ(Ω_(Ω+BTBO)) = ψ(Ω_(Ω + ψ(Ω_Ω)))
  上限: ψ(Ω·2) 之下 (α 在 Ordᴰ 内部无法达到 Ω)
```

## 3. 未来路线图

### 3.0 已尝试的"跨范式" 探针: SMB-trees (✗ 不解)

**Phase 7 (SMB)** 已实测 ([SMB/FINDINGS.md](PastBTBO/SMB/FINDINGS.md)): 把 [Eremondi 2023 SMB-trees](https://arxiv.org/abs/2312.06962) 移植入本仓库, 检验能否绕过 BoundedTrich 障碍. **结论: 不解**.

- ✅ Phase A: Tree + indMax + bound on Tree 落地 ([SMB/Core.lagda.md](PastBTBO/SMB/Core.lagda.md), 140 LOC)
- ❌ Phase B-1: Naive 桥接 Ordᴰ ↔ Tree 需 +-lmono 退化 ([SMB/Naive.lagda.md](PastBTBO/SMB/Naive.lagda.md))
- ❌ Phase B-2: Mahlo `smaxᴹ` 不能递归通过 `b : Sub a → Ordᴹ` ([SMB/Mahlo.lagda.md](PastBTBO/SMB/Mahlo.lagda.md))

**核心诊断**: SMB-trees 解 **算律** (`indMax` 的代数), 不解 **决策** (BoundedTrich). 决策性是 Brouwer-tree-paradigm 的内在限制 (constructive taboo 于 de Jong et al. 2026).

强度增益 = 0. 路线图主线 (Phase 7+) 仍按下方推进.

### 3.1 安全区: Phase 7-9 (ψ(Ω_(Ω·2)) → ψ(Ω_(Ω²)))

**保证不撞屏障**, 因为每一阶仍是"加一层单调 ℕ-indexed 序列".

#### Phase 7: HigherOrdᴰ² — ψ(Ω_(Ω·2))

定义 `Ordᴰ² = OrdH (ω-asᴰ)` (HigherOrdᴰ 在 ω 层级的输出, 取它作新基础). 然后 `HigherOrdᴰ²` 在 Ordᴰ² 上跑 OrdH α' 构造.

- LOC: ~150
- 风险: 低 (机械迭代, 模式 100% 仿 Phase 5B → Phase 6 转换)
- 强度: ψ(Ω_(Ω·2))

#### Phase 8: ω-iter — ψ(Ω_(Ω·ω))

迭代 Phase 7 的"自我应用" ω 次. 用 `Ordᴰⁿ` 的 ℕ-参数化 (类比 Phase 6.1 HigherIter 的 Higher² ... Higher⁴).

- LOC: ~200
- 风险: 中 (命名爆炸, 但每层机械)
- 强度: ψ(Ω_(Ω·ω))

#### Phase 9: 对角化 — ψ(Ω_(Ω²))

合并 Phase 7-8 到单一 `OrdH² α β` 双参数化数据类型. α 是"外层迭代深度", β 是"内层 OrdH 参数". 对角化取 α = β.

- LOC: ~250
- 风险: 中高 (双参数 IR scheme, 互递归层数翻倍)
- 强度: ψ(Ω_(Ω·Ω)) = ψ(Ω_(Ω²))

### 3.2 边界区: Phase 10-11 (Veblen 进入)

**第一次接近屏障**. 需要引入 Veblen φ-函数族, 概念跳跃.

#### Phase 10: Veblen 一级 φ_α — ψ(Ω_(Ω^Ω))

在 Ord 上定义 Veblen φ_α(β):
```agda
φ : Ord-level → Ord-level → Ord-level
-- φ 0 β = ω^β
-- φ (α+1) β = (α+1)-th fixed point of φ α
-- φ (lim f) β = sup_n φ (f n) β
```

需要 `φ-node : (α β : ...) → Ord-V`, 比较两个 φ-node 时, **如果 α, α' 都来自单调 ℕ-序列**, 仍可用 ℕ-trichotomy. **如果 α, α' 可以是任意 Ord 值**, 撞 Mahlo 同构墙.

- LOC: ~400
- 风险: **50%** — 取决于 Veblen 是否能被构造为"分层 monotone"形式
- 强度: ψ(Ω_(Ω^Ω))

#### Phase 11: Veblen 二级 / Bachmann 不动点 — ψ(Ω_(ε_(Ω+1)))

Bachmann 序数 ε_(Ω+1) 是 Veblen 的"自身指数"不动点. 这开始涉及 Ord 上的不动点构造, 类比 Setzer Mahlo 的"对操作子闭合"思想.

- LOC: ~700
- 风险: **30%** (开始触及 Mahlo 同构结构)
- 强度: ψ(Ω_(ε_(Ω+1)))

### 3.3 撞墙区: Phase 12+ (与 Mahlo 同构的墙)

#### Phase 12: 多变量 Veblen Γ_α — ψ(Ω_(Γ_(Ω+1)))

二变量 Veblen `Γ : (α β : Ord) → Ord` 是 Bachmann 的下一级. 此处 `Γ α β` 与 `Γ α' β'` 比较需**先比 α, α'**, 两个**任意 Ord 值**, **与 Mahlo `b s` vs `b s'` 同构**.

- LOC: ~800+
- 风险: **20%** — 大概率撞墙, 与 Phase 2 Mahlo 同构
- 强度: ψ(Ω_(Γ_(Ω+1)))

#### Phase 13+: Π_2-reflection / Inaccessibles / Mahlo 真

ψ(Ω_(...)) 接近 inaccessible 与 Mahlo 强度时, OCF 框架本身需要 reflection 结构, 这是 Setzer Mahlo 的核心. **Agda `--safe --without-K` 已实测无法形式化** (Phase 1-5 770 LOC).

- 风险: **5%** — 几乎必撞 Phase 1-5 同样的墙
- 强度: ψ(I), ψ(M_Setzer), ...

#### 终极目标: ψ(Ω_Ω_Ω) = ψ(ω_(ω_(ω_1)))

**需要的结构性能力**: Ω 索引嵌套到 Ω_Ω 级, 即"ω_1-级 fixed-point on Ω-hierarchy". 这等价于 Π_2-reflection 强度, 与 Mahlo 同级.

**当前框架下不可达**. 需要彻底脱离 Brouwer-tree + bounded-trich 范式, 例如:
- 引入 Set-IR-Mahlo 通过 sized types 或 well-founded recursion 框架
- 或换 Coq / Lean 用 universe polymorphism
- 或接受 postulate (违反项目原则)

## 4. 量化路线图总结

| Phase | 目标 | LOC | 风险 | 关键挑战 |
|-------|------|-----|------|---------|
| 6.2 (✓ 已完成) | ψ(Ω_(Ω+ω)) | 100 | 0% | 已完成 |
| **7** | ψ(Ω_(Ω·2)) | 150 | 10% | 机械迭代 |
| **8** | ψ(Ω_(Ω·ω)) | 200 | 30% | 命名爆炸 |
| **9** | ψ(Ω_(Ω²)) | 250 | 50% | 双参数 IR |
| **10** | ψ(Ω_(Ω^Ω)) | 400 | 50% | Veblen 化, 概念跳跃 |
| 11 | ψ(Ω_(ε_(Ω+1))) | 700 | 70% | 不动点, 接近屏障 |
| 12 | ψ(Ω_(Γ_(Ω+1))) | 800+ | 80% | 多变量 Veblen 同构 Mahlo |
| 13+ | Π_2-reflection / Mahlo 真 | 数千+ | 95% | 完全等价 Mahlo barrier |
| **终极** | **ψ(Ω_Ω_Ω)** | 不可估 | **~100% 撞墙** | **需要 Setzer Mahlo 强度** |

**风险列**: 撞 BoundedTrich / Mahlo 墙的概率.

## 5. 实操建议

### 5.1 短期 (Phase 7-9): 高确定性扩张

机械迭代 + 双参数对角化, 把强度推到 ψ(Ω_(Ω²)). 工程量 ~600 LOC, 90% 把握. 推荐**优先做**.

### 5.2 中期 (Phase 10-11): 研究级 Veblen

引入 Veblen φ_α 到 Brouwer 树框架. 需要的工程模式:
- φ_α(β) 用**单调 ℕ-序列驱动**的 α (不允许任意 Ord)
- φ-iter 通过 `cumsum (ordᴰ ∘ ...)` 类比 ψᴰ 构造

**关键风险**: Veblen 在 Ord 上的标准定义是"fixpoint over α", 我们的 Brouwer 树框架可能无法干净表达**对任意 α 的 fixpoint**. 必须限到**monotone-trajectory α**.

50% 把握, 工程量 ~1000 LOC.

### 5.3 长期 (Phase 12+): 必撞墙的现实

Bachmann 不动点 Γ_(Ω+1) 与以上**结构性等价 Mahlo**. Phase 1-5 已实测 Agda `--safe --without-K` 下 Mahlo 不可形式化, **Phase 12+ 同样不可达**.

**唯一突破口** (违反项目原则):
- `--postulate` reflection 公理 (不安全)
- 引入 sized types 框架 (改动大)
- 换语言 (离开 Agda 生态)

### 5.4 诚实终点

**Agda `--safe --without-K` + Brouwer 树 OCF 的强度上限大致是 ψ(Ω_(Ω^Ω))**, 与 Bachmann-Howard 一族相当. **ψ(Ω_Ω_Ω) 不可达 in this framework**.

这与 OCF 文献的已知结果一致: 标准 Buchholz 系统的形式化天花板就在 ε_(Ω+1) ~ Γ_(Ω+1) 之间, 突破需要 Mahlo / KPM 反射, 而那是另一个范式.

## 6. 与 Phase 1-5 的对照

Phase 1-5 PastBTBO/Mahlo 770 LOC 撞墙的发现, 现在看来**是对路线图的精确预言**:

> 当 Phase 12+ 需要"多变量 Veblen on Ord" 时, 撞的墙与 Phase 2 Mahlo `<ᴹ-dec` 撞的墙是同一个 — 跨任意 Ord 索引的 trichotomy 不可得.

PastBTBO/Mahlo 770 LOC 不是浪费, 它**提前在 ψ(Ω_(Ω+α)) 级别遭遇了本应在 ψ(Ω_(Ω^Ω))+ 级别才遇到的屏障**, 因为 Mahlo 的结构性"早熟"地触发了任意函数索引的需求. 反过来, Higher 路线把屏障**延后**到结构上必须引入多变量函数空间的时候.

## 7. 相关文件

- [BTBO.lagda.md](BTBO.lagda.md) — 基线 ψ(Ω_Ω)
- [Higher.agda](Higher.agda) — ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1)))
- [HigherGen/HigherIter.lagda.md](HigherGen/HigherIter.lagda.md) — Phase 6.1 机械迭代 (内嵌实测)
- [HigherGen/HigherOrdᴰ.lagda.md](HigherGen/HigherOrdᴰ.lagda.md) — Phase 6.2 单一 OrdH α (内嵌实测)
- [HigherGen/FINDINGS.md](HigherGen/FINDINGS.md) — Phase 6 umbrella overview
- [PastBTBO/Mahlo/FINDINGS.md](PastBTBO/Mahlo/FINDINGS.md) — Mahlo 探索 umbrella (Phase 2-5 细节内嵌各 .lagda.md)
- [PastBTBO/Naive/FINDINGS.md](PastBTBO/Naive/FINDINGS.md) — `+-lmono` 不真 (最早的 BoundedTrich 屏障实证)
- [PastBTBO/SMB/FINDINGS.md](PastBTBO/SMB/FINDINGS.md) — Phase 7 SMB-trees 失败诊断 umbrella
- [Notation/FINDINGS.md](Notation/FINDINGS.md) — **范式 B umbrella (2026-07-20 起主线)**
- [Notation/EBO.lagda.md](Notation/EBO.lagda.md) — 范式 B Phase N-1: extended Buchholz 表记全管线
- [Notation/Mahlo.lagda.md](Notation/Mahlo.lagda.md) — 范式 B Phase N-2: 真 Mahlo 级项系统 + M 对角

## 8. 一句话总结

**Higher 与 Mahlo 不是两条独立路径, 而是同一座山的两条登山线 — Mahlo 在山脚就撞了崖, Higher 在半山腰才撞**. 半山腰是 ψ(Ω_(Ω^Ω)) 附近. 山顶 ψ(Ω_Ω_Ω) 需要换一座山 (新语言 / 新范式).

## 9. 范式 B: 换山实录 (2026-07-20)

§8 说"需要换一座山" — [Notation/](Notation/) 就是那座山, 且**不需要换语言**:

- **山的名字**: 有限项 notation system (Buchholz T / Rathjen T(M) 的真实数学结构).
  项是有限语法树, 比较是结构递归全函数 — **范式 A 的 taboo (语义树无条件三歧性) 在语法树上不存在**.
- **实测** (全部 `--safe --without-K` 无公理编译):
  - [Notation/EBO.lagda.md](Notation/EBO.lagda.md): extended Buchholz 全管线 (~330 LOC).
    表记极限 EBO = ψ₀(Λ) ≫ ψ(Ω_(Ω^Ω)) (范式 A 天花板); §3.3 "终极目标" ψ(Ω_Ω_Ω) = 具体项 `ψΩΩΩ`,
    基本列 6 规则逐值带 `<` 证书, FGH 沿 Acc 递归 (停机检查器认可).
  - [Notation/Mahlo.lagda.md](Notation/Mahlo.lagda.md): 真 Mahlo 级项系统 (~600 LOC).
    χ_M(0) 等 M-构建度数是合法项且参与可判定比较 (`refl` 直接算出 χ_M(0) < M);
    M-共尾折叠的 γ-链实现 Mahlo 对角 (度数由被折叠参数驱动); ψ₀(M) 的 FGH 管线就位.
- **新墙 (被隔离为单一义务)**: 语法序在标准形子集上的良基性 WF(NF). 这不是 taboo 而是可证明性问题;
  三条进攻路线 (直接归纳 / **Takahashi-𝕄 语义靶反射** (范式 A 遗产!) / 分段交付) 见
  [Notation/FINDINGS.md §3](Notation/FINDINGS.md).
- **修正后的结论**: 不可形式化的是"Brouwer 范式内的 Mahlo", 不是 Mahlo. 范式 A 的 ~1000 LOC 负向
  结果的价值 = 划定范式边界并留下 WF 语义靶; 强度竞赛的主线自此转移到范式 B.
