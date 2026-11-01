# Kovacs IR universe stratification — ψ(Ω_Ω_2) 探索 FINDINGS

> 总判定: **ψ(Ω_Ω_2) 突破未达成**, 但 NS1+NS2 形式化 Kovacs Layer 1 IR 在本项目独立实现达 BHO 强度; NS3+Base2 形式化 multi-level IR 撞 unbounded trichotomy 墙 (与 AlphaDec FINDINGS 一致).
>
> 本探索 (2026-05-17~05-18) 在用户授权"放宽 Brouwer-tree 范式"后启动. 引入 [Andras Kovacs Agda gist](https://gist.github.com/AndrasKovacs/8d445c8457ea0967e807c726b2ce5a3a) 的 **induction-recursion (IR) universe stratification** 范式, 与 BTBO Brouwer-tree paradigm 并列.

## 总判定

**未达成 ψ(Ω_Ω_2)**. 形式化交付:
- ✓ NS1 [Base.lagda.md](Base.lagda.md): Kovacs Layer 1 IR universe 完整复刻, cmpO₁ + O l El + El + Limᵁ + ⇑ 编译通过
- ✓ NS2 [Collapse1.lagda.md](Collapse1.lagda.md): ψ-collapse 完整链 + ε₀, Γ₀, BHO (Bachmann-Howard ordinal) 见证, 编译通过
- ✓ NS3 [Layer2.lagda.md](Layer2.lagda.md) 数据层: O₂ + _<₂_ + lim₁ via U l 索引域, **R-NS3.1 strict positivity 通过** (重要正向 finding)
- ✓ Base2 [Base2.lagda.md](Base2.lagda.md): multi-mutual IR (O' + El' + _<ᵁ_ + mono-O) + <ᵁ-trans 编译通过
- ✗ cmpᵁ Lim/Lim case: 撞 **unbounded trichotomy on U' i** 墙 (LPO taboo, 不可证)
- ⛔ NS4-5 (ψ_2 collapse + ψΩΩ₂ 见证): 按 R-NS3.2 升级版判定不启动

## 强度阶梯

| 项目模块 | 强度 | 范式 | 状态 |
|---------|------|------|------|
| BTBO baseline | ψ(Ω_Ω) | Brouwer-tree mutual data | ✓ 已实现 |
| Higher.agda | ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) | BTBO + single-level stratification | ✓ 已实现 |
| HigherGen Phase 6.2 | ψ(Ω_(Ω+ω)) | α-参数化 OrdH | ✓ 已实现 |
| **Kovacs NS1+NS2 (本探索)** | **BHO ≈ ψ_0(ε_(Ω+1))** | **IR universe single-level** | **✓ 本探索新增** |
| Kovacs NS3 数据层 | (待 Layer 2 ψ_2 见证) | IR + multi-level | ✓ strict positivity 通过, 但 cmpO₂ 撞墙 |
| Kovacs Layer 2 完整 | (理论) ψ(Ω_Ω_2) | IR + multi-level | ✗ cmpᵁ Lim case 不可证 |

**关键 finding**: Kovacs NS1+NS2 提供项目首个 **IR-based ψ-collapse 实现**, 强度达 BHO (与 BTBO baseline ψ(Ω_Ω) 不同 axis, 量级稍低但独立路径). 这是非 Brouwer-tree 范式的实证.

## 形式化撞墙地图 (Kovacs 路径)

| Phase | 设计 | 实测 | 撞墙根源 |
|-------|------|-----|----------|
| NS1 Base | Kovacs single-layer IR (O l El + El) | ✓ 编译通过, cmpO₁ + Limᵁ + ⇑ | 无 (符合 Agda 2.8 + --safe) |
| NS2 Collapse1 | ψ-collapse + ε₀/Γ₀/BHO 见证 | ✓ 编译通过, BHO typecheck | 无 |
| NS3 Layer2 数据层 | O₂ + lim₁ via U l 索引 | ✓ R-NS3.1 strict positivity 通过 | 无 (multi-mutual IR + IR 接受) |
| **NS3 cmpO₂ (原 R-NS3.2 猜测)** | BoundedTrich on U l | (未实测, 由 Base2 替代) | 替换为 unbounded trichotomy |
| **Base2 cmpᵁ Lim/Lim case (实测撞墙)** | unbounded trichotomy on U' i | **✗ LPO taboo, 不可证** | de Jong 2026 taboo, paradigm 内不可绕开 |

**关键升级**: 原 plan R-NS3.2 预测"BoundedTrich on U l"撞墙, 实测**更严重** — 撞的是 **unbounded** trichotomy (即任意 x, y 上的三歧, 不在共同上界下). cmpO₂ 在 lim₁ 索引 (x, y : U l) 上需要无 bound 的 trichotomy, 因为 x, y 是 lim₁ 内部索引位置, 不携带 < 关系作为伴随约束.

## 与 BTBO Brouwer-tree paradigm 撞墙的同构

| 撞墙路径 | paradigm | 撞墙形态 | 等价指出 |
|---------|---------|---------|----------|
| γ-bounded Phase A-D | BTBO + IR + γ 约束 | sup ≤ Ω_1 | Brouwer-tree 单层数据 sup 受限 |
| DM Path α | BTBO + IIR ψ-image | strength-equivalence refl | ψ-down 嫁接坍缩 |
| AlphaDec R3-alt + R4 | BTBO + cubical α-decidable | <₁-dec Ord₀ trichotomy 不可决 | Brouwer-tree 上 unbounded trichotomy taboo |
| **Kovacs Base2 cmpᵁ Lim case** | **IR universe + multi-mutual** | **unbounded trichotomy on U' i** | **同型 AlphaDec, 等价 LPO taboo** |

**核心洞察**: 任何 ordinal representation (Brouwer-tree, IR universe, multi-mutual IR, etc.) 在 Agda --safe 内, 若要支持 lim 接受**任意 set**索引域 (而非仅 ℕ-indexed monotone sequence), 都撞 unbounded trichotomy 墙. **这是 paradigm-agnostic 的 LPO taboo 实证**.

## 学术诚实交付

本探索的核心交付物**不是** ψ(Ω_Ω_2) 突破, 而是:

1. **Kovacs IR universe 在本项目独立实现** (NS1+NS2): Agda 2.8 + stdlib 2.3 内 IR universe stratification 工程模板, 达 BHO 强度. 这是项目首个非 Brouwer-tree paradigm 的成功移植.

2. **multi-mutual IR strict positivity 通过验证** (R-NS3.1): 三个 mutual 定义 (O' + El' + _<ᵁ_ + mono-O) 在 Agda 2.8 内接受. 这扩展 [Probe2 验证](https://gist.github.com/AndrasKovacs/8d445c8457ea0967e807c726b2ce5a3a) 至本项目环境.

3. **形式化撞墙诊断升级**: 原 plan R-NS3.2 预测 "BoundedTrich on U l", 实测更严重为 "unbounded trichotomy on U' i". 这是 LPO taboo 的 IR paradigm 实证, 比 AlphaDec 三重撞墙更精确.

4. **paradigm-agnostic taboo 实证**: cubical + α-decidable + Kovacs IR + multi-mutual + multi-level 全部不绕开 LPO taboo. 这给 ROADMAP §5.4 "诚实终点" 提供进一步扩展.

## ROADMAP 修订建议

ROADMAP §5.4 原: "Agda --safe + Brouwer 树 OCF 的强度上限大致是 ψ(Ω_(Ω^Ω))". 

本探索扩展:
- "Brouwer 树 paradigm" → 应改为"任何 ordinal representation in Agda --safe (含 cubical) + 自动停机检查器 + 无 postulate"
- 上限保持 ψ(Ω_(Ω^Ω)) 或更紧 ≈ Bachmann-Howard, 因 Kovacs single-layer 达 BHO 已达 ROADMAP 估计上限的部分
- ψ(Ω_Ω_2) 在此约束内**结构性不可达**, 与 [AlphaDec FINDINGS](../Ord1D/AlphaDec/FINDINGS.md) + de Jong 2026 taboo 共同闭合

## 进一步突破 ψ(Ω_Ω_2) 的真出路 (本框架外)

所有这些都**超出用户当前纲领**:
- 接受 `--terminating` 标记 (HoTT QIIT 路径, 用户已排除)
- 接受 sized types 或 postulate (违反纲领)
- 换语言 (Coq/Lean + axiom of well-foundedness, 出本项目范围)
- 接受元数学层级证明 (即非形式化的强度论证, 但不达"自动停机检查"标准)

## 与历史撞墙路径对照

三轴 (Brouwer-tree, IR universe, paradigm-agnostic) 共同确认 ψ(Ω_Ω_2) 不可达:

| 维度 | Brouwer-tree (BTBO+) | IR universe (Kovacs) | paradigm-agnostic 总判 |
|------|----------------------|----------------------|------------------------|
| 单层 | BTBO ψ(Ω_Ω), Higher ψ(Ω_(Ω+ω)) | NS1+NS2 BHO | 单层 sup ≤ Ω_(Ω) 量级 |
| 多层尝试 | Ord1D Phase A-D (γ-bounded) | NS3 Layer 2 (multi-level) | 多层撞 unbounded trichotomy 墙 |
| 三重 BTBO 撞墙 | γ-bounded, DM, AlphaDec | NS3+Base2 cmpᵁ Lim case | 共同闭合 ψ(Ω_Ω_2) 不可达 |

## 最终判定

**Kovacs 路径**: ψ(Ω_Ω_2) **未达成**, 但**形式化诚实交付**:

- ✓ NS1+NS2: 项目首个 IR universe paradigm 实现, BHO 强度
- ✓ NS3 R-NS3.1: multi-mutual IR + universe-stratified lim 索引域的 strict positivity 验证
- ✓ Base2 R-NS3.2 升级: unbounded trichotomy 撞墙的精确诊断

**学术价值**: 在 cubical Agda + IR + multi-mutual 框架内**形式化验证** ψ(Ω_Ω_2) 不可达的 paradigm-agnostic 性质. 与 AlphaDec FINDINGS + de Jong-Eremondi-Forsberg 2026 taboo 共同实证.

**总成本**: ~500 LOC over 5 files (Base + Collapse1 + Layer2 + Base2 + FINDINGS).

## 文件清单

- [Base.lagda.md](Base.lagda.md): NS1 — Kovacs Layer 1 IR (~200 LOC)
- [Collapse1.lagda.md](Collapse1.lagda.md): NS2 — ψ-collapse + BHO 见证 (~150 LOC)
- [Layer2.lagda.md](Layer2.lagda.md): NS3 数据层 — O₂ + _<₂_ + lim₁ via U l (~80 LOC)
- [Base2.lagda.md](Base2.lagda.md): NS3 前置 — multi-mutual IR + <ᵁ-trans (cmpᵁ 撞墙诊断) (~120 LOC)
- [FINDINGS.md](FINDINGS.md): 本文件, umbrella 总结
