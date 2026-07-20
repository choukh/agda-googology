# 范式 B (有限项表记系统) — umbrella overview

> 工作文件: [EBO.lagda.md](EBO.lagda.md) (Phase N-1), [Mahlo.lagda.md](Mahlo.lagda.md) (Phase N-2).
> 单文件实测与诚实评估已内嵌各文件 (literate 交织风格). 本文是 cross-file umbrella:
> 范式论证 / 成果位次 / 与范式 A 对照 / WF 义务 / Phase N-3+ 路线.

## 0. TL;DR

**Mahlo 探索重启 (2026-07-20), 方向: 范式转移而非范式内工程.**

| 模块 | LOC (约) | 状态 | 表记级强度 |
|------|----------|------|-----------|
| [EBO.lagda.md](EBO.lagda.md) | ~330 | ✅ 编译 (--safe 无公理) | **EBO = ψ₀(Λ)**, 含 ROADMAP "终极目标" ψ(Ω_Ω_Ω) 为具体项 |
| [Mahlo.lagda.md](Mahlo.lagda.md) | ~600 | ✅ 编译 (--safe 无公理) | 语法+序: Rathjen T(M) 骨架段位 (χ_M(0) 等 M-度数项); fs 实际驱动段位见该文件 §8 |

**一次会话越过了范式 A 路线图 (Phase 7-12) 的全部预定强度**, 并把"真 Mahlo 不可形式化"的
结论修正为: **不可形式化的是"Brouwer 树范式内的 Mahlo", 不是 Mahlo 本身**.

## 1. 范式论证

### 1.1 范式 A 的墙是定理, 不是工程债

范式 A (Brouwer 树) 的全部撞墙记录 ([../PastBTBO/](../PastBTBO/), [../ROADMAP.md](../ROADMAP.md))
归结为一个事实: ψ-折叠需要对 lim-见证做序判定, 而 **语义树上的无条件三歧性是 constructive taboo**
([de Jong et al. 2026](https://arxiv.org/abs/2602.10844)). 有界三歧 (BoundedTrich) 只在"共同屋顶"下可用;
结构分析进一步表明: 可判定脊柱的序型被 Ω 封顶 (脊柱 > ω 的 sup 只能取真段, 真段不抬高 sup),
反馈 bootstrap 的下标封顶在 ε_(Ω+1) 附近 — 与 ROADMAP §5.4 的实测天花板 ψ(Ω_(Ω^Ω)) 一致.
**在这个范式内, 真 Mahlo 无路可走 — 这是 Phase 1-7 (~1000 LOC) 负向结果的正面价值: 它证明了范式边界.**

### 1.2 范式 B 免疫 taboo

序数分析的真实数学结构从来不是语义树, 而是**有限项 notation system** (Buchholz 的 T, Rathjen 的 T(M)):

- 项 = 有限语法树, "不可数宽度"只存在于指称语义中 — **语法上没有函数极限**;
- 比较 = 结构递归全函数 ⇒ **无条件三歧性免费** (taboo 的前提消失);
- 基本列 = 结构递归全函数;
- FGH = 沿 `Acc` 递归 — `Acc` 是归纳类型, Acc-递归就是**停机检查器认可的**超限递归.

**纲领相容性**: 项目三纲领 (序数先行 / 无公理可运行 / 停机检查器保证停机) 从未要求 Brouwer 树.
范式 B 全部满足 — 唯一代价是停机保证从"结构自动"变为"结构自动 + 一次性 WF 证明义务" (§3).

### 1.3 对照表: 同一堵墙在两个范式中的形态

| | 范式 A (Brouwer) | 范式 B (notation) |
|---|---|---|
| Mahlo 级三歧性 | `<ᴹ-dec` 4-子case 死墙, 770 LOC 无解 | [Mahlo.lagda.md](Mahlo.lagda.md) §2, ~60 行, `χ_M(0) < M` 由 `refl` 算出 |
| ψ(Ω_Ω_Ω) | "当前框架下不可达" (ROADMAP §3.3) | `ψΩΩΩ` 一个具体项 ([EBO.lagda.md](EBO.lagda.md) §7.1) |
| 停机保证 | 结构递归免费 | Acc-递归, 需一次性 WF(NF) 证明 |
| 墙的性质 | constructive taboo (不可能) | 可证明性问题 (--safe Agda 强度 ≫ EBO; Mahlo 级 = 研究前沿) |

## 2. 实测成果

### 2.1 EBO 模块 (Phase N-1) — 全管线闭环

项系统 (Maksudov extended Buchholz, ψ_ν 下标任意项) / 归纳序 + 无条件可判定 `cmpᵀ` /
cof 分类 / 基本列全 6 规则 (**构造即证明**: 每个 fs 值自带 `<ᵀ` 证书, `Below` record) /
`γ↓`-链 (规则 6) / Acc-FGH / 底段 Acc 证明 + 数值 demo (f₃(2)=2048 by refl) /
`EBO-number : (∀ n → Acc (EBOψ n)) → ℕ → ℕ` — 大数 modulo 单一 WF 证书.

### 2.2 Mahlo 模块 (Phase N-2) — 真 Mahlo 语法与判定

- 层级项: `I d b` (度数-d 不可达层级枚举, **度数可含 M**: `I [M] []` = χ_M(0) 合法), `M`;
- 12 条跨构造子序规则 + 全 with-free 可判定比较;
- 三族基本列代换 (Ω_{μ+1} / I_d(b) / M 刻度) + 三种 γ-链, 其中 **M-链即 Mahlo 对角**:
  `γ_{k+1} = I (a[γ_k]) (a[γ_k])` — 度数由被折叠参数驱动 (Rathjen "M-共尾经 χ-度数反射" 的表记形态);
- `ψ₀(M)` 为合法项, 其基本列实测展开为 `ψ₀(I_{I₀}(I₀))` 等对角塔 (refl demo);
- `Mahlo-number : Acc ψ₀M → ℕ → ℕ`.

### 2.3 诚实边界 (两模块共享, 细节见各文件 §8)

1. **WF 义务**: 语法序在全项集上非良基 (`ω > 1+ω > 1+1+ω > ...` 反例), 良基性必须限制在
   NF 子集: NF 谓词 + fs 保 NF + WF(NF). 未证.
2. **fs 共尾性** (仅 Mahlo 模块): I/M-链逐值递减有证书, 但高层链未证在项序中共尾
   (M-链只对角 M-free 度数塔). 停机性与合法性不受影响; 顶层 FGH 增长率被低估.
3. **枚举偏移约定**: I-枚举在不动点索引处的 eq→gt/lt 分支是本仓库约定, 待与 Rathjen χ 精确对齐.
4. Maksudov 的 I/M 完整 fs 规则原文获取失败 (fandom 402 / cantorsattic 403 / Google Sites JS),
   本次按 Buchholz 规则 6 的统一模式 + Rathjen χ 机制重建, 语义保真度标注为待核.

## 3. 新墙: WF(NF) 的精确形状与三条进攻路线

义务: `∀ t ∈ NF → Acc _<ᵀ_ t` (限制在 NF 子集). 强度: EBO 级 ≈ 取一次 Ω-不动点之下的 TI;
Mahlo 级 = KPM 的证明论序数 — **机器验证的 WF(T(M)) 是公开研究前沿, 无先例**.

- **路线 W-a (直接归纳)**: Buchholz/Rathjen 式分层 TI, 参照 ccz181078 的 Coq Buchholz-WF 先例.
  EBO 级可行性高 (研究级工程, 数千行); Mahlo 级未知.
- **路线 W-b (语义靶反射)**: 把 NF 项解释进 **Takahashi-MLQ Mahlo universe**
  ([../PastBTBO/Mahlo/Phase1.lagda.md](../PastBTBO/Mahlo/Phase1.lagda.md), 已在 --safe 下编译,
  结构上真 Mahlo) — **范式 A 的"失败"资产恰好是范式 B 的 WF 证明所需语义靶**.
  这是把两个范式接成闭环的路线, 也最有研究价值.
- **路线 W-c (分段交付)**: 先证 WF 到 ε₀ / Γ₀ / BO 段位, FGH 大数逐段解锁, 逐段超越 BTBO 主线.

## 4. Phase N-3+ 路线图

| Phase | 内容 | 工程量估 | 风险 |
|-------|------|---------|------|
| N-3 | NF 谓词 + fs 保 NF (EBO) | ~500 LOC | 低-中 (机械但繁) |
| N-4 | WF(NF) 到 BO/EBO 段 (路线 W-a/W-c) | 数千 LOC | 中 (有 Coq 先例) |
| N-5 | Mahlo fs 共尾性修复 (Maksudov I/M 规则移植, 需先取到原文) | ~300 LOC | 中 |
| N-6 | WF via Takahashi-𝕄 (路线 W-b) | 研究级 | 高 (无先例, 值得发表级) |

## 5. 工程 lessons (Agda 2.8.0, --safe --without-K --cubical-compatible)

1. **定义里的 `with` 是证明毒药**: with-lifting 生成不透明辅助函数, 证明侧无法归约.
   凡需被推理的函数 (cof 等) 一律用一等辅助函数组合定义 (`cofψ0`/`cofA`/`route`), 证明用
   显式等式参数 helper (`go : ∀ c → cof u ≡ c → ...` + 调用处 `go (cof u) refl`).
2. **终止检查三连** (实测于 cmp 的互递归):
   (a) 不要重新包装 (`cmpᵀ u (p ∷ [])` → 专门函数 `cmpT1 u p`);
   (b) 重建的构造子应用是 unknown, 整参数用 @-模式绑定;
   (c) **嵌套 with 摧毁 size-change 分析** — 分派用急切组合子 (`lexc`/`iic`), 彻底 with-free.
3. **构造即证明** (`Below a = Σ T (_<ᵀ a)`): 基本列直接返回带证书的值, 避免"先定义再重放
   with-结构补证"的双倍成本. 每个证书都是一行构造子.
4. 递归经 where-helper 会丢 size-change 信息: 顶层互递归 + 子项整体传参 (严格∘相等=严格).

## 6. 文件清单

- [EBO.lagda.md](EBO.lagda.md) — Phase N-1: extended Buchholz 全管线 (~330 LOC, ✅)
- [Mahlo.lagda.md](Mahlo.lagda.md) — Phase N-2: I/M 项系统 + Mahlo 对角 (~600 LOC, ✅)
- 本文件 — umbrella

副作用: `agda-googology.agda-lib` depend 更新为本机安装名 (`standard-library` (2.4) / `cubical` (0.9));
BTBO / Higher / HigherOrdᴰ / HigherIter 在 stdlib 2.4 下全部重验编译通过.

## 7. 文献

- Buchholz 1986, *A new system of proof-theoretic ordinal functions*
- D. Maksudov, extended Buchholz + fundamental sequences; *collapsing weakly Mahlo* (googology; 原文本次未能抓取)
- Rathjen 1990, *Ordinal notations based on a weakly Mahlo cardinal* (T(M), χ/ψ)
- de Jong–Kraus–Nordvall Forsberg–Xu 2026, *Generalized Decidability via Brouwer Trees* ([arxiv 2602.10844](https://arxiv.org/abs/2602.10844))
- Takahashi 2024, *Interpretation of Inaccessible Sets in MLTT with One Mahlo Universe* ([arxiv 2402.15074](https://arxiv.org/abs/2402.15074)) — 路线 W-b 语义靶
- ccz181078, Coq Buchholz WF 先例 ([googology repo](https://github.com/ccz181078/googology))

## 8. 一句话总结

**范式 A 用 ~1000 LOC 证明了"此路不通"是定理; 范式 B 用 ~930 LOC 证明了"换条路, Mahlo 的语法、
序、判定、对角折叠全部落地", 剩下一堵可证明性的墙 (WF), 而墙的钥匙可能恰好是范式 A 留下的
Takahashi-𝕄 (它结构上就是一个真 Mahlo universe).**
