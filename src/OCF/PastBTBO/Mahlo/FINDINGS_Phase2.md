# Mahlo Phase 2: 实施日志 + 撞墙诊断

> Phase 1 骨架: [Phase1.lagda.md](Phase1.lagda.md). Phase 2 工作文件: [Phase2.lagda.md](Phase2.lagda.md). 路线源: [FINDINGS.md §6](FINDINGS.md#6-phase-2-路线-2000-3000-loc-估).
>
> 五步路线攻击结果: **1-3 通, 4 partial (3/4 mahlo 子 case 撞墙), 5 跳过**. 与 [Naive/FINDINGS.md §5](../Naive/FINDINGS.md) `+-lmono` 死墙结构同构.
>
> **术语约定**: "Step N" 指 Phase 2 内的 5 个子步 (1 = Sub reflection, 2 = `<ᴹ`+`<ᴼ`, 3 = mono, 4 = bounded trichotomy, 5 = ψ_M). "Phase N" 指项目级阶段 (1 = 骨架, 2 = 本次 5-step 攻击, 3 = Sub 内禀序 + b-mono, 未来). 两套编号互不重合.

## 0. TL;DR

- ✓ **Step 1 Sub reflection**: `Sub (mahlo _ a b) = Σ (Sub a) (Sub ∘ b)`. Setzer "(a:U)(b:T a → U) → U" 闭合的 Brouwer 化.
- ✓ **Step 2 `<ᴹ` + `<ᴼ`**: 5 个 `<ᴹ` 构造子 (zero, suc, lim, mahlo-a, mahlo-b) + 1 个 `<ᴼ` 构造子 (op-c). `<ᴹ-trans` 5 case 平凡递归通过.
- ✓ **Step 3 mono on lim**: `monoᴺ : (ℕ → Ordᴹ) → Set` 烤进 `lim`, 互递归 5 层 (Ordᴹ + Opᴹ + Sub + <ᴹ + <ᴼ) + 1 个 monoᴺ. mahlo 未加 monoSub (需 Sub 内禀序, 见 §3).
- ⚠️ **Step 4 bounded trichotomy**: 非 mahlo case 全通, mahlo 4 子 case 中 1 个通 (mahlo-a, mahlo-a), 3 个 blocked. 退回到 partial `<ᴹ-dec? : … → Maybe (Tri a b)`.
- ✗ **Step 5 ψ_M**: 跳过. trichotomy partial 阻断 collapser.

## 1. Step 1 实施细节

Takahashi 2024 §2.1 reflection 的 Brouwer-MLQ 形为:

```agda
Sub (mahlo _ a b) = Σ (Sub a) (λ x → Sub (b x))
```

读法: mahlo 编码的 sub-universe 元素 = 一对 `(x : Sub a, y : Sub (b x))`. 对应 Setzer `mahlo : ((a:U) → (T a → U) → U) → U` 的 "T a × T(b applied to T a)" 闭合.

注: `f : Opᴹ` 字段在此版本中**未参与** `Sub` 的反射定义. 完整 Takahashi 反射需要 `Opᴹ` 与 `Ordᴹ` 双向交互, 涉及更深的 mutual 结构. 当前 Σ-closure 是最小可行版.

## 2. Step 2 设计选择: `<ᴹ` 跨 mahlo 两条进路

`mahlo f a b` 上的 `<ᴹ` 构造子有两个:

```agda
mahlo-a : ∀ {f a b x} → x <ᴹ a → x <ᴹ mahlo f a b
mahlo-b : ∀ {f a b x} → (s : Sub a) → x <ᴹ b s → x <ᴹ mahlo f a b
```

形状对应 Step 1 `Sub (mahlo _ a b) = Σ (Sub a) (Sub ∘ b)` 的两个分量. 任何小于 mahlo 的 x 必然或者 (a) 小于 mahlo 的 "code 头" a, 或者 (b) 小于某个 b-分支 `b s`. 这就是 Setzer Σ-closure 的逆向反射.

`<ᴼ` 只保留 op-c (头比较), 不展开 op 的 `Sub c → Opᴹ` 分支. 够用于未来 `mahlo` cross-Opᴹ 比较, 不过度复杂化.

## 3. Step 3 设计妥协: mahlo 未加 monoSub

完整 6 层互递归 (FINDINGS §6 设想) 应包括 `monoSub : (a : Ordᴹ) → (Sub a → Ordᴹ) → Set`. 实现障碍:

- `monoSub a b = ∀ {s s'} → s <ˢ s' → b s <ᴹ b s'` 需要 `Sub a` 上的 `<ˢ` 关系.
- `<ˢ` 必须**按 a 的结构定义**:
  - `Sub zero = ⊥`: 无序
  - `Sub (suc _) = ⊤`: 单点平凡序
  - `Sub (lim _ _) = ℕ`: 用 `<ᴺ`
  - `Sub (mahlo _ a b) = Σ (Sub a) (Sub ∘ b)`: 递归字典序, 互递归向下
- 这会让互递归扩张到 7+ 层, 且 dictionary order 在 `Σ` 上的 mono 证明需要 `b` 自身的 mono — 循环依赖.

**决策**: Phase 2 不加 monoSub. mahlo 字段仍用 `b : Sub a → Ordᴹ` 无约束函数. Phase 3 之后再考虑独立的 `Sub-Order.lagda.md` 模块.

## 4. Step 4 死墙: bounded trichotomy on mahlo

目标 (在非 mahlo 上工作版本):

```
<ᴹ-dec : ∀ {a b c} → a <ᴹ c → b <ᴹ c → a <ᴹ b ⊎ b <ᴹ a ⊎ a ≡ b
```

当 c = `mahlo f a₀ b₀`, p/q 的构造子组合形成 4 个子 case:

| sub-case | 类型展开 | 死墙根源 |
|----------|--------|----------|
| (mahlo-a p, mahlo-a q) | p : a <ᴹ a₀, q : b <ᴹ a₀ | ✓ 递归 `<ᴹ-dec p q` |
| (mahlo-a p, mahlo-b s q) | p : a <ᴹ a₀, q : b <ᴹ b₀ s | a₀ 与 b₀ s 之间无序关系 |
| (mahlo-b s p, mahlo-a q) | p : a <ᴹ b₀ s, q : b <ᴹ a₀ | 对称 |
| (mahlo-b s p, mahlo-b s' q) | p : a <ᴹ b₀ s, q : b <ᴹ b₀ s' | `Sub a₀` 无序 + `b₀` 无 mono |

### 4.1 与 Naive `+-lmono` 反例的同构

Naive Phase1 的死墙: `+-lmono : a < b → a + c < b + c` 不真. 反例 `0 + ω ≡ 1 + ω ∧ 0 < 1`. 后果: limΩ case 找不到自然共同上界.

Mahlo 节点的对应反例: 设 `b₀ : Sub a₀ → Ordᴹ` 非单射, 存在 `s ≠ s' : Sub a₀` 使 `b₀ s ≡ b₀ s'`. 此时 (mahlo-b s p, mahlo-b s' q) 在结构上不可区分, 但 `s, s'` 本身需要 `Sub a₀` 上的内禀序才能进一步分析 — 与 §3 的 monoSub 缺失互锁.

更深一层: 即使 `b₀` 单射, 跨 mahlo-a/mahlo-b 的 case 需要比较 `a₀` 与 `b₀ s` (两个独立的 Ordᴹ), 没有外部的"共同上界"提供. 类比 limΩ 的 `f a, f b : Ordᴰ-1` 跨 Ordᴰ-索引比较 — Naive 已经验证为不通.

### 4.2 缓解: Maybe-wrapped partial

```agda
<ᴹ-dec? : ∀ {a b c} → a <ᴹ c → b <ᴹ c → Maybe (Tri a b)
<ᴹ-dec? (mahlo-a p) (mahlo-a q) = <ᴹ-dec? p q
<ᴹ-dec? (mahlo-a _) (mahlo-b _ _) = nothing
<ᴹ-dec? (mahlo-b _ _) (mahlo-a _) = nothing
<ᴹ-dec? (mahlo-b _ _) (mahlo-b _ _) = nothing
```

3 个 mahlo 子 case 显式 `nothing`. 非 mahlo case (zero/suc/lim) 走完整 trichotomy. 全函数无 postulate.

## 5. Step 5: 为何 ψ_M 必然被阻断

ψ_M 仿 [Higher.agda:31–38](../../Higher.agda) `ψ<Ω`:

```agda
ψ_M (mahlo … p f) with <ᴹ-dec p (some upper bound)
... | injᵃ … = limᵢ …
... | injᵇ … = lfp …
... | injᶜ … = lfp …
```

`<ᴹ-dec?` 在 mahlo 输入上 3/4 几率 return `nothing` → `ψ_M` 在那些 case 上无法选择 limᵢ/lfp/lfp 分支. 用 Maybe-monad 把 `ψ_M : Ordᴹ → Maybe (Ord …)` 化亦无意义 — collapser 必须给出确定 Ord 值.

结论: ψ_M 至少要等 Phase 3 (Sub-序 + b-mono → 全函数 `<ᴹ-dec`) 后才有意义.

## 6. 修正 FINDINGS.md §6 估算

原估 (重写为本文档术语): "Step 1-2 大概率通 (Takahashi 示范过). Step 3-4 是真正研究. Step 5 取决于 4."

实测修正:
- Step 1-3 通过 (与 Takahashi 示范一致).
- **Step 4 在 mahlo 节点上结构性卡死, 同 Naive `limΩ` 死墙**. 不是"难证而是不可证".
- Step 5 同步阻塞.

升级路径: 必须先做 Phase 3 (Sub 内禀序 + b mono). 这相当于把 Takahashi MLQ 扩成"index-ordered MLQ", 是 Takahashi 2024 paper 未做的部分.

## 7. 与 Naive FINDINGS §6 的统一结论

| 死墙位置 | Naive 框架 | Mahlo 框架 | 同构关键 |
|---------|----------|----------|---------|
| 跨索引比较 | `limΩ f x` vs `limΩ f y` 跨 Ordᴰ x, y | `mahlo-b s` vs `mahlo-b s'` 跨 Sub a₀ s, s' | 索引类型无三歧 |
| 共同上界 | `x + suc y` 中 `+-lmono` 不真 | `b₀` 无 mono → 不存在自然桥接 | 函数空间内的单调性公理 |
| 修复路径 | 加 mono 到 Ordᴰ-1 的 limΩ + 改 ⊔ 算子 | 加 monoSub 到 mahlo + Sub 内禀序 | 烤入函数空间的内禀结构 |

两条路径都需要"在不可数索引空间上加内禀序+单调性", 这是 OCF Mahlo-级形式化的核心未解问题.

## 8. 文件清单

- [Phase1.lagda.md](Phase1.lagda.md): Phase 1 骨架 (无 `<ᴹ`, 无 mono, Sub 占位 ⊤). 编译通过.
- [Phase2.lagda.md](Phase2.lagda.md): Phase 2 升级版 (Sub Σ-closure, `<ᴹ`, `<ᴼ`, lim monoᴺ, partial trichotomy). 编译通过.
- [FINDINGS.md](FINDINGS.md): Mahlo 编码选型诊断, V1-V6 失败/成功记录.
- 本报告.

无 postulate, 无 `--unsafe`, 通过 Agda 2.8.0 + stdlib 2.3 + cubical 0.9 + `--cubical-compatible` 类型检查.
