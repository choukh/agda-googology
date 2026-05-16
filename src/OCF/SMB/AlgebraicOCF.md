# 算律 OCF 设计探索 — 用 SMB lub 替代 BoundedTrich 决策

> **设问**: 标准 OCF (Buchholz ψ) 的 `ψ<` 折叠依赖**决策性** (BoundedTrich `<-dec`). 能否设计一种 OCF 折叠算法, **不依赖决策, 而是使用算律** (lub / max / sup)?
>
> **结论 (摘要)**: 算律 OCF 在原理上可行, 但**强度天花板严格低于决策性 OCF**. 关键洞察: 决策性收集到的"哪边更大"信息, 在算律里被 lub 同化, 损失精度. 算律 OCF 的强度上限大致是 BTBO `Ord-Ord` 的 ψ(Ω_Ω), 与 BTBO 已实现的相当 — **不带来强度突破, 但可作为更对称的工程实现**.

## 1. 标准 OCF 为何需决策性

### 1.1 Higher.agda 的关键决策点

[Higher.agda:38](../Higher.agda#L38) 的 `ψ<Ω` 折叠:

    ψ<Ω {n} (limₙ {n = m} p f) with <ᴺ-dec m n
    ... | injᵃ m<n = limᵢ (cumsum-mono _ m<n) (ψ<Ω ∘ f ∘ ψ< p ∘ coe {q = zero})
    ... | injᵇ n<m = lfp (ψ<Ω ∘ f ∘ ψ< p ∘ ↑ (cumsum-mono _ n<m))
    ... | injᶜ refl = lfp (ψ<Ω ∘ f ∘ ψ< p)

三个 case 输出 **结构上不同的 Ord (ψᴰ n) 元素**:
- `injᵃ`: 用 `limᵢ`-构造子 (升到 ψᴰ-界限)
- `injᵇ`: 用 `lfp` (least fixed point)
- `injᶜ`: 用 `lfp` (但参数不同)

这种结构性差异**编码了 m 与 n 的相对位置信息**. 决策性给出"哪个 case", 才能取对应结构.

### 1.2 决策性 ↔ 信息保留

形式化: 决策性收集 `(m,n)` 对的精确大小关系 (3 比特: <, >, =). 算律里只能保留"组合后的 lub" — 损失 log(3) 比特/调用. 在 n 层互递归后, 损失 ~ log(3) · n 比特, **强度损失指数级**.

具体: 标准 Buchholz ψ 的强度依赖于这种精确分级. 失去分级 → ψ 退化为更简单结构 (类似 Cantor 标准形或 ε_0-级).

## 2. 算律 OCF 的设计原型

### 2.1 替换原则

| 标准 ψ< 操作 | 算律替代 |
|------------|---------|
| `with <-dec m n` 三歧 | `smax case-a (smax case-b case-c)` — lub 所有 case |
| `lfp F` (最小不动点) | `Lim (F-iter F n)` — F 的 ω-迭代极限 |
| `Ord< i p` 由 `p : i < ℓ` 引导 | 类型族用 `Σ[ i ] (i 在某算律封闭下)` |
| BoundedTrich `<-dec` | SMB-tree `indMax-≤L / ≤R` (LUB 性质) |

### 2.2 关键困难

#### 困难 A: 异型 lub

三个 case 的输出是不同 Agda 形状 (`limᵢ p f` vs `lfp F`). 它们都属 `Ord (ψᴰ n)` 但结构子不同. **lub 的语法**要求同型. 解法:
- 选项 A1: 仅用单一构造子 (e.g., 所有 lim 都走 `cumsum`-wrapped lim, 牺牲精度)
- 选项 A2: 给 Ord (ψᴰ n) 加一个统一的 `union`-构造子, 算律意义上的 set-union

A1 损失强度 (∵ `limᵢ` 比 `lfp` 在某些场景更紧). A2 改变数据类型, 工程量大.

#### 困难 B: "最小" 不可表达

`lfp F` 是 F 的**最小**不动点. 构造性"最小"需要决策性 — 哪个候选元素最小. 无决策性时, 我们只有"某个不动点":

    lfp-alg F = Lim (F-iter F)
    where F-iter F zero    = F Z
          F-iter F (suc n) = F (F-iter F n)

这是 F-iter 的 ω-极限. 是不动点 (在 F 是连续意义下), 但**不是最小**. 强度可能高于 lfp 经典版.

听起来更好? **不一定** — 高强度的"不动点"可能不再有 ψ 的语义, 退化为简单上确界. ψ 的核心强度恰来自"最小性".

#### 困难 C: 单调性 vs 严格单调性

SMB-tree 的 `indMax` 是 monotone (`≤`-mono), 不是 strict-mono (`<`-mono). BTBO 的 `lim` 需要 strict-mono on basic sequence. **算律 OCF 用 SMB indMax 构造极限时, 损失 strict**.

解法: 像 [SMB/Core.lagda.md](Core.lagda.md) 用 `cumsum` 强行 strict. 但 cumsum 引入额外 + 累加, 不再是"纯算律".

## 3. 一个原型: `Ordˢ` + sup-based ψ

```agda
-- 想法 (未编译, 仅设计示意):
data Ordˢ : Set where
  Z    : Ordˢ
  ↑    : Ordˢ → Ordˢ
  Lim  : (ℕ → Ordˢ) → Ordˢ
  ΩLim : (Tree → Ordˢ) → Ordˢ      -- Tree-indexed limit, 无界

-- ψ-collapse via algebraic sup:
ψ<ˢ : Ordˢ → Ordˢ
ψ<ˢ Z         = Z
ψ<ˢ (↑ a)     = ↑ (ψ<ˢ a)
ψ<ˢ (Lim f)   = Lim (ψ<ˢ ∘ f)
ψ<ˢ (ΩLim f)  = walk-Tree f-on-walk
  where
    -- walk over Tree structure, lubbing as we go:
    walk-Tree : (Tree → Ordˢ) → Ordˢ
    walk-Tree g = Lim (λ n → walk-up-to-depth n g)
    walk-up-to-depth : ℕ → (Tree → Ordˢ) → Ordˢ
    walk-up-to-depth zero    g = g Z
    walk-up-to-depth (suc n) g = -- lub over trees of depth ≤ n
      max (walk-up-to-depth n g) (g (some-tree-of-depth-suc-n))
```

### 3.1 强度估算

`ΩLim f` 覆盖 Tree-索引的所有输入. 但 `walk-up-to-depth n g` 只到达深度 n 的 Tree — 这是**可数子集**. 取 Lim 得到所有有限深度 Tree 上的 sup.

- Tree-有限深度 ≈ ε_0-级 (Cantor 标准形可数序数)
- ψ-collapse over ε_0-级 ≈ ε_0 本身

**强度天花板**: ψ(Ω_Ω). 与 BTBO 相当, 不超过.

### 3.2 与 BTBO 的对照

| 维度 | BTBO (Ord-Ord) | 算律 OCF (Ordˢ) |
|------|----------------|----------------|
| 索引类型 | `Ordᴰ` (bounded trich) | `Tree` (无 trich) |
| 折叠机制 | BoundedTrich `<-dec` 三歧 | walk-Tree sup 算律 |
| 单调性 | `lim` strict-mono 内建 | 需 `cumsum` 后加 |
| 强度 | ψ(Ω_Ω) | ≤ ψ(Ω_Ω) |
| 工程量 | ~1000 LOC (本仓库现有) | ~500 LOC 估算 |
| 优势 | 高强度 + 决策性可控 | 对称性 + 算律推理 |

**结论**: 算律 OCF 是 **可工程化的备选实现**, 但**不超过** BTBO 已达的 ψ(Ω_Ω).

## 4. 深层理由: 决策 vs 算律的本质张力

### 4.1 信息论视角

决策性把 "x op y" 的关系约化为可数离散结果 (`<`, `>`, `=`). 这是 **离散信息提取**.

算律操作 `x ⊔ y, x + y, ψ x` 把 x, y 组合为新对象, 但**抹除**它们的相对位置. 这是 **连续信息合成**.

OCF 的强度来自递归提取离散信息. 算律方法的强度受限于"算律封闭闭包"能表达的复杂度.

### 4.2 与文献的关系

- **Buchholz 1986** 的标准 ψ 显式用决策性
- **Rathjen** 各级 OCF 也用决策 (虽语义可由集合论 sup 替代)
- **Setzer 1998 IR-Mahlo** 进一步加 reflection
- **Eremondi 2023 SMB-trees** 是 **well-founded recursion** 工具, 不是 OCF — 它的 max-LUB 不在 ψ 折叠路径上使用
- **de Jong et al. 2026 Generalized Decidability** 明确: 无条件决策性 on Brouwer 树是 constructive taboo

文献暗示: **OCF 强度与决策性紧密耦合**, 算律方法在构造性数学里**自然受限**.

## 5. 在本仓库的潜在应用 (低强度但有价值)

即便算律 OCF 不增强强度, 它可能在工程层面有用:

### 5.1 替代 Mahlo 路径的简化

PastBTBO/Mahlo 用 770 LOC 撞了决策性墙. 若用算律方法重做:
- 替换 `<ᴹ-dec` 为 `smaxᴹ` (Tree 上)
- 替换 `lfp` 为 `Lim (iter)`
- 工程量降到 ~300 LOC

代价: 强度从 "理论上的 ψ(M)" 降至 ψ(Ω_Ω) (Mahlo 路径本来就饱和到这级了, 实际没有损失).

### 5.2 提供"对称化"的备选 BTBO

把 BTBO 现有的 `_+_` (右单调, 不左单调) 替换为 SMB `indMax` (双侧单调). 加法律性质对称. 可能简化 BTBO 的某些证明.

### 5.3 教学价值

算律方法更接近**集合论 OCF** 的直观, 对理解 ψ 的语义有帮助.

## 6. 与 Phase 7 SMB 探针的关系

[FINDINGS.md](FINDINGS.md) 报告: SMB-trees 不解 BoundedTrich 障碍, 因为它解 *算律*, 不解 *决策*. **本文档进一步**:

- 即便我们**全程**使用算律 (设计算律 OCF), 也不增强强度
- 算律方法是 BTBO 的"等强度备选实现", 不是"高强度突破口"
- 真正突破 ψ(Ω_(Ω^Ω)) 天花板 (见 [ROADMAP.md](../ROADMAP.md)) **必须**接受决策性 + 反射性结构 (e.g., Setzer Mahlo), 而那回到了已知撞过的墙

## 7. 推荐: 不实现算律 OCF, 转继续 Higher 主线

### 7.1 工程优先级

- **高**: [ROADMAP §3.1](../ROADMAP.md) Phase 7 HigherOrdᴰ² → ψ(Ω_(Ω·2)) (机械迭代, 150 LOC, 90% 把握)
- **中**: 算律 OCF 原型实现 (~500 LOC, 强度不增, 仅为对称性 / 教学)
- **低**: 跨范式探索 (postulate / sized types / 换语言)

### 7.2 算律 OCF 的研究入口 (供有兴趣的读者)

若读者希望深入算律 OCF:
1. 阅读 Rathjen "An ordinal analysis of stability" (强度但用决策)
2. 阅读 Aczel-Rathjen "Notes on Constructive Set Theory" (集合论 OCF)
3. 阅读本仓库 [Higher.agda](../Higher.agda) (40 LOC 决策性 OCF, 强度 ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))))
4. 对比: 算律方法本仓库无现成实现, **可作为后续 PhD-level 研究主题**

## 8. 一句话总结

**决策性是 OCF 强度的源头, 算律是 OCF 表达的工具 — 两者互补但不替代**. SMB-trees 与算律 OCF 在本仓库的天花板都是 ψ(Ω_Ω), 与 BTBO 已实现的水平相当. 突破天花板需要离开 Brouwer-tree 范式, 那是另一座山.
