# AlphaDec — cubical + α-decidable 突破 ψ(Ω_Ω_2) 路径 FINDINGS

> 总判定: **ψ(Ω_Ω_2) 突破未达成**. cubical + α-decidable 框架内形式化撞墙诊断完整.
>
> 本探索是 [DM Path α](../DM/FINDINGS.md) 的姊妹路径, 由用户授权 cubical 后启动 (2026-05-17). 计划在 [src-ocf-memoized-sparrow.md](../../../../.claude/plans/src-ocf-memoized-sparrow.md).

## 总判定

**未达成 ψ(Ω_Ω_2)**. 形式化交付:
- ✓ Spike S1: cubical 文件成功 import BTBO, 命题截断 + α-dec 接口可用
- ✓ Spike S2: 类型层判定 α-decidable 不动构造子, 强度突破必须依赖新数据类型
- ✓ Phase R3-alt: mutual data Ord₁ᴰ + _<₁_ + lim₁ via Ord₀ typecheck 通过
- ✗ Phase R4: `<₁-dec` 撞 Ord₀ 不可决性墙, α-decidable 框架不适用 trichotomy
- ⛔ Phase R5-R6: 按 R4 判定不启动 (注定与 DM 同形撞墙)

## 形式化撞墙地图

| Phase | 设计 | 实测 | 撞墙根源 |
|-------|------|-----|----------|
| [S1](../../AlphaDec/Base.lagda.md) | cubical α-dec 基础定义 | ✓ 编译, ≤ᴰ + ≤ᴰ-trans + α-dec | 无 (基础设施 OK) |
| [S2](../../AlphaDec/StrengthSpike.lagda.md) | α-dec 在 Ordᴰ 上能否增强度? | ✗ Ordᴰ closed type, α-dec 不动构造子 | 类型层判定 |
| [R3-alt](IR.lagda.md) | mutual data Ord₁ᴰ + lim₁ via Ord₀ | ✓ typecheck, sup 原则可达 Ω_2 | 无 (数据层 ready) |
| [R4](BoundedTrich.lagda.md) | `<₁-dec` 与 α-dec 软化版 | ✗ Ord₀ trichotomy 不可决, α-dec 不适用 | constructive taboo |

## 三重审视

### 1. cubical 工具的真实角色

cubical (HIT, 命题截断, Path/transport, univalence) 在本探索中:
- **可用**: cubical 文件成功 import BTBO `--without-K` 模块 (实测 Probe 与 Base 双重验证)
- **工程价值**: ∥-∥₁ 让"存在性"在命题层表达, encode-decode 给 isSet 推导
- **强度无关**: 不修改 Brouwer-tree paradigm 的构造子设计, 也不创造 Ord₀ 上的决策性

这与 [Plan B 审稿](../../../../.claude/plans/src-ocf-memoized-sparrow.md#关键风险预诊断) "cubical 是工程简化不是强度突破启用器" 的判断**形式化一致**.

### 2. α-decidable 的真实范围

de Jong-Kraus-Mohammadzadeh-Forsberg 2026 ([arXiv 2602.10844](https://arxiv.org/abs/2602.10844)) 的 α-decidable:

- **定义**: `α-dec z P = ∥ Σ y. P ↔ z ≤ y ∥₁` (Brouwer-ordinal-indexed)
- **核心定理**: 论文 Thm 23, ω²-decidable for countable conjunctions of semi-decidable
- **适用范围**: **单调命题** (P 真值随 y 单调变化)
- **不适用**: trichotomy 类**非单调命题** (truth value 三分支)

R4 形式化此局限: 即使把"strict trichotomy"弱化为"∥-∥₁ 截断 trichotomy", Ord₀ 仍不可决 — 命题截断只隐藏决策的"哪个", 不创造决策本身.

### 3. R3-alt 数据层 vs R4 关系层

R3-alt 的 mutual data Ord₁ᴰ + _<₁_ + lim₁ via Ord₀ **typecheck 通过**, 这意味着:
- 数据层 Ord₁ᴰ 原则上 sup = Ω_2 (Brw₄)
- 但 `<₁-dec` 不可证, 阻塞 Phase R5 的 ψ<₁ 三歧 dispatch
- 因此**没有 ψ<₁ 折叠 → 没有 ψ(Ω_Ω_2) 强度见证**

这是新的撞墙形态: 数据层够强, 关系层弱化. 与历史 γ-bounded (数据层弱化, 关系层强) 互补.

## 三条已撞墙路径的对照

| 路径 | lim₁ 索引 | <₁-dec | sup | 强度 | 撞墙形态 |
|------|----------|--------|-----|------|---------|
| [Ord1D γ-bounded Phase A-D](../FINDINGS.md) | γ-bounded Ordᴰ | ✓ (BTBO <-dec) | ≤ Ω_1 | ψ(Ω_Ω) | 数据层弱化 |
| [DM Path α IIR ψ-image](../DM/FINDINGS.md) | Ord₀ via ψ-down | ψ-image only | ≤ Ω_1 | ψ(Ω_Ω) | ψ-down 嫁接到 Ordᴰ |
| **AlphaDec R3-alt + R4** | Ord₀ direct | ✗ (taboo) | (Brw₄ 可达但无 <-dec) | n/a | **关系层不可决** |

三条路径在 Agda --safe (含 cubical) 内**共同闭合** ψ(Ω_Ω_2) 不可达的形式化诊断, 完整对应 de Jong-Eremondi-Forsberg 2026 "constructive taboo".

## de Jong-Eremondi-Forsberg 2026 taboo 的本仓库实证

论文 taboo 命题: "Brouwer trees + total trichotomy 不可同时实现".

本仓库三条路径形式化验证 taboo 的所有降维形态:
- **γ-bounded**: 限制 Brw 阶 (lim₁ → Ordᴰ-bounded), 保 trich
- **DM ψ-image**: 限制 trich (ψ-image only), 保 Brw₄ 语法
- **AlphaDec R3-alt**: 限制 trich 可证性 (∥-∥₁ 也不证), 保 Brw₄ 语法 + 直接 _<₁_

任何降维都损失 ψ(Ω_Ω_2) 的某个必需要素. cubical 工具 + α-decidable 框架不改变 taboo 边界.

## 学术诚实交付

本探索的核心交付物**不是** ψ(Ω_Ω_2) 突破, 而是:

1. **形式化撞墙地图扩展**: 在 cubical + α-decidable 框架内具体撞墙位置形式化 (S2 + R4)
2. **α-decidable 局限的形式化分析**: 论文工具的"单调命题"范围明确 + Ord₀ trichotomy 不在其适用域 (R4 §3)
3. **plan B 审稿的形式化实证**: "α-decidable 不动构造子" 与 "cubical 是工程简化不是强度突破"
4. **taboo 的三重表现实证**: 三条路径共同闭合 ψ(Ω_Ω_2) 不可达

## 进一步突破 ψ(Ω_Ω_2) 的真出路 (本框架外)

- **类型论范式突破**: 需要超越 Brouwer-tree paradigm, 例如 well-ordering 公理 (TypeTopology) 或 inductive-inductive types 上的 truly higher-stratum recursion
- **HoTT ordinal representation 换路** (Kraus-Forsberg-Xu 2021 arXiv 2104.02549): 用 well-foundedness + extensionality + transitivity 的 QIIT 替代 Brouwer trees. 这需要重做整个 BTBO 基线, 不是 plan 范围内的"嫁接"
- **接受 postulate** (用户不授权)
- **换语言** (出本项目范围)

这些都不在本探索范围. AlphaDec 是 Brouwer-tree paradigm + cubical 内的形式化天花板实证.

## 与 [ROADMAP](../../ROADMAP.md) §5.4 的关系

ROADMAP §5.4 "诚实终点":
> Agda `--safe --without-K` + Brouwer 树 OCF 的强度上限大致是 ψ(Ω_(Ω^Ω)), ψ(Ω_Ω_Ω) 不可达.

本探索把这个结论扩展到 `--safe --cubical`: cubical 工具不改变 Brouwer-tree paradigm 内的强度上限. 即使加上 α-decidable 框架, ψ(Ω_Ω_2) 仍不可达 (实际上 BTBO baseline 周围才是上限).

ROADMAP §5.4 的 ψ(Ω_(Ω^Ω)) 上限是**理论估计**, 本探索给出更接近 ψ(Ω_Ω) 的**实测下界** (因为 R3-alt 数据层达 Brw₄ 但 R4 关系层失败, 实际可达性仍是 ψ(Ω_Ω) = BTBO baseline).

## 最终判定

**AlphaDec 路径**: ψ(Ω_Ω_2) **未达成**, 但**形式化诚实交付完整**:

- cubical + α-decidable 框架在本仓库内的**强度天花板实测** = BTBO baseline ψ(Ω_Ω)
- 与 DM Path α 形式化共同闭合 Brouwer-tree paradigm 内的 ψ(Ω_Ω_2) 不可达
- 学术价值: 在 cubical Agda + α-decidable 框架内**形式化验证** de Jong-Eremondi-Forsberg 2026 的 taboo 的精确边界

**与 Plan A vs Plan B 审稿对照**:
- ✓ Plan B 审稿核心论证 (α-decidable 不增强度) 形式化 confirmed
- ✓ Plan A 工程视角的 R3-alt 设计虽 typecheck 通过, 但 R4 关系层撞墙
- 结合两者: **plan 的 spike-first 策略正确**, 在 ~500 LOC 内得到形式化撞墙诊断, 避免投入 R5-R6 注定失败的 ~400 LOC

**总成本**: ~500 LOC over 4 phases (S1 + S2 + R3-alt + R4). 远低于 plan 原估算的 1320 LOC (因 spike-first 策略提前止损).
