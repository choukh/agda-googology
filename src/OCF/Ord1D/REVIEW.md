# 审稿报告 — Ord₁ᴰ 路线 "ψ(Ω_Ω_2)" 强度声明

> 数学期刊审稿人视角的批判性审阅. 寻找当前 Ord₁ᴰ 路线宣称的 ψ(Ω_Ω_2) 强度声明中的漏洞与不稳断言.

## 总评

形式化层面真实进展: 五版本 spike 对比 + γ-bounded `<₁-dec` + Ord-Ord-on-Ord₁ᴰ 结构 + ψ-folding 框架在 Agda `--safe --without-K` 下编译通过. 这是结构性贡献.

**强度层面声明 "ψ(Ω_Ω_2)" 严重高估**. 具体的 `final-strength-witness : Ord-Basic.Ord₀` 项的实际序数值大约 **ψ(Ω_Ω)** (BTBO baseline), 而非 ψ(Ω_Ω_2). 没有任何编译通过的证据支持比 BTBO 更高的强度.

下列七个核心漏洞.

---

## 漏洞 1 — sup(Ord₁ᴰ) ≠ Ω_2 的论证

用户的核心论证 ([ROADMAP §2.2](../ROADMAP.md) 复述): "sup(Ord₁) = sup(Brw₄) = Ω_2, 所以 Ord₁ᴰ 阶等价于 Ω_2".

**审稿人发现的逻辑跳跃**:

[BTBO.lagda.md:91-95](../BTBO.lagda.md#L91-L95) 的裸 `Ord₁` 的 lim₁ 索引域确实是 `Ord₀` (即 Brw₃), 这才对应 Brw₄ 阶 sup = Ω_2.

但是 [BoundedTrich.lagda.md:38-39](BoundedTrich.lagda.md#L38) 中 Ord₁ᴰ 的 `lim₁` 是:

```agda
lim₁ : (γ : Ordᴰ) (f : (α : Ordᴰ) → α < γ → Ord₁ᴰ) ...
```

**索引域是 Ordᴰ-切片 `{α : Ordᴰ | α < γ}`, 不是 `Ord₀` (Brw₃) 整体**.

对**任何具体 γ : Ordᴰ**, sup of (Ordᴰ-切片 below γ) ≤ γ ≤ sup(Ordᴰ) ≈ Ω_1. 单个 lim₁ 节点的宽度 < Ω_1. 通过 lim₀ 包装可达 Ω_1 的 ω-序列, 但**无法跳到 Ω_1-级宽度**.

**结论**: Ord₁ᴰ 实际 sup ≤ Ω_1, 不是 Ω_2. Ord-Ord-on-Ord₁ᴰ 的强度 ≤ ψ(Ω_(Ω_1)) = ψ(Ω_Ω) = BTBO baseline.

要真正达到 Ω_2, 需要 lim₁ 索引域是 Brw₃ = Ord₀ (不带 mono / γ-bound 的全集). 但这正是 Phase A 的 A₁/A₂ 撞墙方向.

---

## 漏洞 2 — Ω₁-partial 在 lim₁ case 退化为 zero

[OrdOrd.lagda.md:116](OrdOrd.lagda.md):

```agda
Ω₁-partial (lim₁ γ f m π)  = zero
```

这意味着对任何 lim₁ 形态的 `ℓ : Ord₁ᴰ`, `Ω₁-partial ℓ : Ord₁ ℓ` 是 `zero` (即 Ord₊₁ 的 zero 构造子), **不是真正的 Ω 数**.

后续 [Collapse.lagda.md](Collapse.lagda.md):

```agda
ψ<₁ p zero = Ω₁-partial _
```

`ψ<₁` 在 `Ord₁ ℓ` 上的 zero case 调用 Ω₁-partial. 当 i₁ (输出层级) 是 lim₁ 形态时, 输出 zero, **不是 Ω**.

进一步:

```agda
ψ₀-on-1ᴰ {ℓ₁ = lim₁ γ f m π} a = lim₁-collapse a
where lim₁-collapse _ = zero
```

`ψ₀-on-1ᴰ` 在 ℓ 为 lim₁ 形态时**完全退化**, 不真正折叠.

**审稿人结论**: 整个 ψ-folding 链在 lim₁ 形态 ℓ 上断裂, 任何依赖 lim₁ 的强度估算无效.

---

## 漏洞 3 — `final-strength-witness` 实际不触发 lim₁ case

[Collapse.lagda.md §6](Collapse.lagda.md):

```agda
ψᴰ-stream : ℕ → Ord₁ᴰ
ψᴰ-stream n = embedᴰ (cumsum (ordᴰ ∘ ψⁿ) n)

ΩΩ-ℓ : Ord₁ᴰ
ΩΩ-ℓ = lim₀ ψᴰ-stream ψᴰ-stream-mono   -- ← lim₀, 不是 lim₁

strength-witness₂ : Ord₁ zero
strength-witness₂ = ψ₀-on-1ᴰ (Ω₁-partial ΩΩ-ℓ)
```

**关键审视**:

- `embedᴰ : Ordᴰ → Ord₁ᴰ` 的输出是 `zero/suc/lim₀` 形态, 永远不产生 `lim₁` ([BoundedTrich.lagda.md §5](BoundedTrich.lagda.md))
- `ΩΩ-ℓ` 用 `lim₀` 包装, 不是 `lim₁`
- 整个 `strength-witness₂` 的求值路径**完全不触发 lim₁ case**

`ΩΩ-ℓ` 的实际强度 = sup of ψᴰ-stream = sup of {embedᴰ (ψᴰ n)} for n ∈ ℕ = sup of ψᴰ 在 Ordᴰ 中 = BTBO 的 sup ≈ ψ(Ω_Ω) (因为 ψᴰ 序列的 sup 就是 BTBO).

**Ord₁ᴰ 的 lim₁ 创新构造子在 final-strength-witness 中根本未被使用**. 这个项的强度与 Higher.agda 同级 (≈ ψ(Ω_(Ω+1))) 或更低 (没用 OrdΩ 派发).

**审稿人结论**: 声明的 ψ(Ω_Ω_2) 强度的具体见证项实际上是 BTBO baseline 项的简单 wrapping. **没有任何形式化证据支持比 BTBO 更高的强度**.

---

## 漏洞 4 — mono 约束的语义代价被忽视

Brw₄ 的 sup = Ω_2 论证依赖 `lim₃ : (Brw₃ → Brw₄) → Brw₄` **接受任意函数** (无 mono 约束).

Ord₁ᴰ 的 lim₁ 索引域不仅是 Ordᴰ-切片 (漏洞 1), 还**强制要求 mono + PI**:

```agda
Mono₁ᵧ γ f = ∀ {α β} (pα : α < γ) (pβ : β < γ) → α < β → f α pα <₁ f β pβ
PIᵧ γ f = ∀ {α} (pα pα' : α < γ) → f α pα ≡ f α pα'
```

这两个约束让 lim₁ 索引函数被驯化为"严格保序 + 证明无关嵌入". 严格弱于 Brw₄ 的任意 `Ord₀ → Brw₄` 函数.

**类比参照**: BTBO 中 Ordᴰ 加 mono 后 sup 不损失 (`sup(Ordᴰ) ≈ sup(Brw₃) = Ω_1`) — 这是因为 ℕ 上单调函数与任意函数表达力**同 sup** (任何 ω-极限可以单调化).

但 Brw₄ 的 sup ω_2 来自不可数索引 (Brw₃ = Ord₀ 不可数). **不可数集上单调函数表达力严格弱于任意函数** (单调函数有 cofinality 约束, 任意函数没有). 加 mono 损失 ω_1-cofinality 的极限.

**审稿人结论**: 论证 "Ord₁ᴰ 阶 = Brw₄ 阶 = ω_2" 忽略了 mono + PI 在不可数索引上的语义代价. 加约束后的实际阶可能 ≤ Ord₀ + ω_1 步骤 ≈ ω_1 + 一些后效, **远低于 ω_2**.

---

## 漏洞 5 — sup-by-bound 同级嵌入的"假突破"

[OrdOrd.lagda.md §5](OrdOrd.lagda.md):

```agda
sup-by-bound : Ordᴰ → Ord₁ᴰ
sup-by-bound γ = lim₁ γ (λ α _ → embedᴰ α) ...
```

声称这是"形式化 γ-索引极限 → 触及 Ω_Ω 级".

**审稿人分析**:

`sup-by-bound γ` 是 lim₁ γ 节点, f 字段是 `λ α _ → embedᴰ α`. f-image 在 Ordᴰ 中 = γ 之下的 Ordᴰ-切片 (恒等嵌入).

sup of `sup-by-bound γ` = sup of f-image = γ.

但 `embedᴰ γ : Ord₁ᴰ` 本身的 sup = γ (因为 embedᴰ 是保序嵌入).

**`sup-by-bound γ` 与 `embedᴰ γ` 同 sup**. lim₁ 节点没有提升强度, 只是另一种"装载"形式. 实际上, `sup-by-bound γ` 的存在不给出比直接 `embedᴰ γ` 更高的序数值.

**这是 [OrdOrd.lagda.md §6 工程剩余](OrdOrd.lagda.md) 中提到的"同级嵌入" 现象**: 强度估算建立在错觉之上, lim₁ 节点的"宽度" 与单个 embedᴰ 等价.

---

## 漏洞 6 — 形式化 vs 元数学声明的分离不清

Agda 编译通过仅意味着**类型正确**, 不意味着具体项的"序数值"达到声明的强度.

`final-strength-witness : Ord-Basic.Ord₀` 是个 well-typed 项 — 它可以用 BTBO 的 `FGH` 算出某个具体自然数 (理论上). 但**这个具体序数值是多少, 没有外部证据**.

类比: 任何 `Ord-Basic.Ord₀` 项都可以"声称达到 ψ(Ω_Ω_Ω)", 只要类型对. 但实际表示的序数值是其语法结构决定的.

**审稿人要求**: 提供一个**外部的 informal 证明**, 证明 `final-strength-witness` 的语法结构对应的序数值是 ψ(Ω_Ω_2). 当前文档中没有这个证明 — 只有"类比 BTBO 用 sup(Ord₀) = Ω_1 给 ψ(Ω_Ω), 类比给 ψ(Ω_Ω_2)" 的类比论证, 而这个类比基础就是漏洞 1.

---

## 漏洞 7 — Phase A FINDINGS 误导性总结

[FINDINGS.md](FINDINGS.md) A₂ 描述声称:

> "A₂ 实际是 '决策性 + 缺上界证据' 的撞墙, 而 Mahlo 是 '决策性根本不存在'. 区分这两者后, A₃ γ-bounded 设计是 A₂ 撞墙的**自然修复**(注入上界), 而非'同构于已失败的 Mahlo 路径'."

**审稿人质疑**: 这个区分是有效的, 但 A₃ 修复 A₂ 撞墙的代价 (γ-bound 限制了 lim₁ 索引域到 Ordᴰ-切片) **正是漏洞 1 的根源**. A₃ 的撞墙修复不是免费的 — 它把"无限制宽度"换成"Ordᴰ-bounded 宽度", 这是 sup 阶级损失.

A₃ "走通 BoundedTrich" 是真的, 但这个走通的代价是 **Ord₁ᴰ 实际 sup ≈ Ω_1, 不是 Ω_2**. 用户的强度论证基于"Ord₁ᴰ 阶等同 Brw₄", 这个基础在 A₃ 设计中就不成立.

---

## 综合判定

| 声明 | 实际状态 |
|------|---------|
| BoundedTrich on Ord₁ᴰ (A₃) | ✓ 真实达成 |
| Ord-Ord-on-Ord₁ᴰ 结构 (Phase C) | ✓ 真实达成 (结构性) |
| ψ-folding 基础设施 (Phase D) | ⚠ 部分达成 (lim₁ case 退化) |
| **"ψ(Ω_Ω_2) 强度突破"** | ✗ **未达成**, 实际强度 ≈ ψ(Ω_Ω) |
| `final-strength-witness` 见证 ψ(Ω_Ω_2) | ✗ 实际见证 BTBO baseline |

**核心问题诊断**:

用户的 ψ(Ω_Ω_2) 洞察对应的**结构性条件** ("Ord₁ᴰ 阶 ≈ Brw₄ 阶 ω_2") 在 A₃ γ-bounded 设计下**不成立**. 这是个根本性的设计 ↔ 强度 不匹配:

- 用户想要 Brw₄ 阶 (≈ ω_2 sup) 的 Ord₁ᴰ
- A₃ 实现的 Ord₁ᴰ 是 Brw₃ 阶 (≈ ω_1 sup) + Ordᴰ-切片包装 + mono/PI 约束 = 实际上仍是 Brw₃ 阶或略高
- A₃ 走通 BoundedTrich 的代价就是阶级损失

要真正达到 ψ(Ω_Ω_2), 需要让 lim₁ 索引域是 Ord₀ (Brw₃) 而非 Ordᴰ-切片, 但这撞回 A₁ 的 "Ord₀ 不可决策" 死墙.

## 建议修正

1. **修订强度声明**: 在 [FINDINGS](FINDINGS.md), [ROADMAP](../ROADMAP.md), commit 信息中, 把 "ψ(Ω_Ω_2) 强度突破" 改为 "Ord₁ᴰ 形式化框架 + BoundedTrich + Ord-Ord 重做 (结构性达成), 实际强度 ≈ BTBO baseline".

2. **Phase E 重新定义**: 真正的 Phase E 不是"修复 lim₁ 严格 Ω₁", 而是**重新评估 Ord₁ᴰ 的实际 sup**. 计算 `final-strength-witness` 通过 `FGH` 给出的具体大数, 与 BTBO 同款 `FGH BTBO` 比较 — 看是否真的更大.

3. **诚实回归**: [ROADMAP §5.4](../ROADMAP.md) 的判断 "BTBO 框架天花板 ≈ ψ(Ω_(Ω^Ω))" 可能仍然成立. Ord₁ᴰ 不是天花板突破, 而是 BTBO 同级的另一种形式化.

4. **保留的价值**: A₂ vs Mahlo 撞墙的区分 (decision 缺 vs decision 缺 evidence) 是有价值的诊断. β/ε 的双重撞墙诊断有教学价值. 这些不该被强度声明的不实拉低.

---

**审稿人最终判断**: 当前 Ord₁ᴰ 路线作为"BTBO 框架内的另一种形式化" 是有价值的工作, 但作为"ψ(Ω_Ω_2) 强度突破" 的声明**不能接受**. 建议大幅修订强度部分, 接受 Phase A-D 的结构性贡献, 撤回强度突破的主张.
