# Agda 的证明论强度: 文献核对

> 状态日 2026-11-03. Agda: 本机 2.8.0.2, 文档与源码读 tag `v2.8.0`. 只读调查: 没跑 Agda, issue 的复现代码也没跑. 手册 ([OrdinalNotationsGuide](OrdinalNotationsGuide.md), [CodeGuide](CodeGuide.md)) 已有的不重复.
>
> **档.** [原文] 读过一手来源, 写明出处; [转述] 只见摘要或二手; [推断] 本文的推理; [代码] 读过代码 (都没重新编译).

## 1. 结论

**可操作的一句话.** 可当定理引用的只有纸面理论的结果 (IR ≥ |KPM|, |MLM| = |KPM⁺|, |ML₁W| = |KPI⁺|, Setzer Lemma 4.3); "|Agda| ≥ |KPM|" 是定理加一步未形式化的嵌入, 只能当强判断; Agda 的精确强度与证明论上界、"记号无关的树到得了 EBO / I / M" 都只能当判断.

**没有人给出 Agda 或其片段的证明论序数或一致性强度.** 检索范围内最接近的是 Kovács 2026 §5.3: IR "the exact proof-theoretic strength is unknown" [原文]. 这是"没找到", 检索范围见 §8.

| 目标 | Agda 强度够吗 | 记号引导的闭合树 (`Acc` → 树) | 纲领内的树 (记号无关, 树上 FGH) |
|---|---|---|---|
| (a) EBO = ψ₀(Λ) | **够.** \|MLT₁W\| = \|KPi\| 已在其上 [原文 + 推断] | 差两步未写: EBO→OT_I 的保序 (只有测试), `Acc`→树 [推断] | 未到. 最高证书 ψ₀(Ω_{Ω·ω}) ([README](../README.md), 其定理档, 本次未复核). 无否定定理. 开放 |
| (b) 不可达层, 到 ψ_{Ω₁}Ω_{I+n} | **够.** \|ML₁W\| = ψ_{Ω₁}Ω_{I+ω} [原文], Agda 含 ML₁W [推断] | 记号一侧已有 `Acc-endpt` 与沿证书的 `Fₙ` [代码]; 转成树未写 | 未知. `ver` 的树已判错, 证实的判决只有有限层 (README). 开放 |
| (c) \|KPM\| = ψ_{Ω₁}(ε_{M+1}) | **强判断: 够.** IR ≥ \|KPM\| 是定理 [原文], Agda 含外部 Mahlo [原文 + 代码], 整体嵌入未形式化 | 未写; Mahlo 层良序证明无 Agda 版 (路线 C 未走通) | 未知. 必要条件: 定义要动用 IR 级资源 [推断, §5.4] |
| (d) 更高 | **判断: 很可能够到 \|KPM⁺\| 及以上, 无定理.** 没有数值 | 无 | 未知 |

**分清三件事.** "Agda 强度够" 只说存在某个闭项. 这个闭项可以经由记号的良序证明得到, 那就违反纲领第 4 条. 纲领内的树能否到, 文献不回答; 目前既无定理说能, 也无定理说不能.

## 2. 别混

**两种量.**

| 量 | 是什么 | 例 |
|---|---|---|
| 证明论序数 \|T\| | T 可证超限归纳的原始递归良序的上确界 (Setzer 2004 §2). 可数 | \|KPM\| = ψ_{Ω₁}(ε_{M+1}) |
| 一致性上界 (模型) | 大基数理论证 Con(T). 不给序数 | IR 的模型在 ZF + AC + GCH + 一个 Mahlo 基数 |
| 证明论上界 | 模型建在序数已知的理论里, 才得 \|T\| ≤ 该序数 | 内部 Mahlo 的模型在 KPM⁺, 得 \|MLM\| ≤ \|KPM⁺\| |
| 集合论语义 | 类型在模型中的解释 | 模型里 `Ord` (ℕ 分支树) 含全部可数序数的秩; 闭项只有递归秩 [推断, 需典范性] |

"模型在 ZF + Mahlo" 对证明论序数几乎没有信息: 作者自称 "far too big" (Setzer 2004 §7) [原文]. ZF 本身也没有序数分析.

**同名.**

- **M.** 模型里是 Mahlo **基数**; ψ 与 KPM 里是第一个**递归** Mahlo 序数, 可数 (DS 2003 §6.1, Setzer 2004 §6) [原文].
- **Mahlo 宇宙.** *内部*: `M : Set` 是一个集合, 含所有 U_f, f : Fam M → Fam M (Setzer 2000), 超出 IR 理论. *外部*: `Set` 本身扮演 Mahlo, 对每个 f : Fam Set → Fam Set 有 IR 定义的 U_f (DS 2003 §6.3). *扩展谓词式*: 先对无类型项建, 超出 IIRD (DS 2024). *Coquand 2026*: Russell 式, 无 W-type.
- **KPM / KPM⁺ / KPm⁰.** KPM⁺ 多有限个容许序数 (DS 2003 §6.4 说 "ω admissibles above"; Setzer 2004 §6 说有限个常量, 上确界相同). KPm⁰ 限制了归纳, 同一标准模型 L_μ, 序数只有 φω00 (Coquand 注记 5.6, 作者注明未细查).
- **"MLTT + W + 一个宇宙".** Setzer 的 ML₁W 允许 W 建在宇宙之上, = |KPI⁺|. Rathjen 的 MLT₁W(V) 限 W 用于 U₀ 的族, = |KPi|. 差的正是 "W on top" (DS 1999 §7) [原文].
- **Λ.** DS 1999 §6 的 Λ 是 M 之上第一个非正则 ℵ-不动点, 真基数; EBO 的 Λ 是 Ω_α = α 的序数. 形状同, 对象不同.
- **`set` / `type`.** DS 的 `type` 上没有 W; Agda 的 `Set₁` 有. 见 §5.3.

## 3. `--safe --without-K` 下实际可用什么 (2.8.0)

来源: `doc/user-manual/language/safe-agda`, `tools/command-line-options`, `Interaction/Options/Base.hs:896-918` (`unsafePragmaOptions`) [原文].

| 特性 | 状态 | 说明 |
|---|---|---|
| `Set ℓ`, `Level` 多态 | 可用 | |
| `Setω`, `Setωᵢ` | 可用 | 不能对 i 多态, 可在其中定义数据 (`sort-system`) |
| 互归纳, 归纳-归纳 | 可用 | `--forced-argument-recursion` 默认开. 我方 `Ordᴵ` 与 `_⊑ᴵ_` 就是 ([Level](../OCF/Free/Level.lagda.md):35-61) [代码] |
| 归纳-递归, 索引 IR | 可用 | `data` 加函数, 没有固定模式 (`mutual-recursion`). 比 IIRD 宽: DS 2024 的模型超出 IIRD 仍过 Agda [原文]. 非严格正的被拒 (Coquand 注记 5.5 [原文]; SOURCES §122 实验) |
| 大索引 | 受限 | `--large-indices` 与 `--without-K` 同用不 safe, 已知不一致. 索引类型须放得进数据的 sort |
| `--guardedness` | safe | 默认关. 闭合树用不到 [推断] |
| `--sized-types` | **不 safe** | 源码列入 unsafe. `∞ < ∞` 一族 issue 未关 (#1201, #2820, #3026, #6002, #7178). 同文档 `--safe` 词条只说 "防两者同开", 已过时, 以源码为准 |
| `--prop` | safe, 实验性 | 传染性选项. 基于 Gilbert 等 POPL 2019 |
| `--cubical` | safe | 开 `--without-K`. **#8572 未关**: 2.8.0 上经 Cubical 与终止检查得 ⊥ (未复现). 我方 `src/WellFormed/*`, `src/Veblen/*`, `probes/Audit/Veblen` 用它 |
| `--lossy-unification` | safe | 手册: "sound but not complete", 通过的也应在不开时通过 |
| 被 `--safe` 排除 | | postulate, `--rewriting`, `--cumulativity`, `--type-in-type`, `--omega-in-omega`, `--experimental-irrelevance`, `--injective-type-constructors`, 各停机与正性编译指示 |

**对应的已知理论: 没有完全对上的.** 最近的是 Kovács POPL 2026 的理论: 可数宇宙层级, 每层支持 IIR [原文, 摘要]. 模型方面 §4.1.2 说可把 DS 2006 改成可数个 Mahlo 基数加其上两个不可达, 只说 "reasonable to expect" [原文]. 该文讲典范性, 不算强度; 其余特性 (II, `Setω`, 终止检查) 不在其中 [推断].

**终止检查.** 基于 Abel-Altenkirch 与 Lee-Jones-Ben-Amram (`Termination/Termination.hs` 文件头), 调用矩阵查幂等环 [代码]. `--without-K` 只在结果落在 data 或 `Size` 的参数上记结构下降 (手册 `without-k`; `TermCheck.hs:490-494, 580`) [原文 + 代码].

比 W 或消去子更强吗? 分两层:

- **逻辑上: 是, 有实例.** #5910 (标 `without-K`, `safe`, `false`, 未关) 的 `noo` 被接受, 把 `iso` 改成假设就得到一个否定命题: `WOne` 与 `FOne` 不相等. 但 MLTT + UA 有模型 (Rathjen Cor 6.7), 消去子证不出它. 所以检查器接受消去子导不出的东西 [推断, 依 issue 代码, 未复现].
- **序数上: 没有证据.** 尺寸变化原理本身有直觉主义证明, 走 almost-full 而不用 Ramsey (Vytiniotis-Coquand-Wahlstedt 2012) [转述]. 判断: 它不抬高序数. 对 Agda 实际检查器到消去子的翻译, 没查到文献.

## 4. 已知强度结果

| 理论 | 结果 | 档与出处 |
|---|---|---|
| MLTT⁻ (无 W, 带宇宙) | ATR₀, Γ₀; 加 UA 不变 | [原文] Rathjen 2016 Cor 7.2 |
| W + atom, 无真宇宙 | 下界 ψ_{ℵ₁}(ℵ_ω), 上界用 KPl 的模型 | [原文] Setzer 2004 §4 |
| Palmgren 超宇宙 MLS, 无 W | Γ₀ < \|MLS\| < BHO | [转述] Rathjen 2000/2001 摘要; 全文付费 |
| 超宇宙带 W | 模型在 KP + 递归超不可达, 上界 | [原文] Setzer Part I 摘要 |
| MLT₁W(V), W 限在 U₀ | = \|KPi\| = \|(Δ¹₂-CA)+BI\| = \|CZF+REA\| | [原文] Rathjen 2016 Thm 5.2 |
| ML₁W, W 可在宇宙之上 | = \|KPI⁺\| = ψ_{Ω₁}Ω_{I+ω}; 只靠元归纳逐 n 到达 | [原文] Setzer 2004 §5; DS 1999 §7 |
| MLTₙW(V) | = KPi + n 个递归不可达; **序数分析与良序证明都未发表** | [原文] Rathjen 2016 Thm 6.4 与其证明 |
| MLTT, 全部 n, 及 MLTT + UA | 同强度 | [原文] Rathjen 2016 Cor 6.7, 依 Bezem-Coquand-Huber |
| 内部 Mahlo MLM | = \|KPM⁺\| = ψ_{Ω₁}Ω_{M+ω} | [原文] SOURCES §115 (Setzer 2000) 与 DS 2003 §6.4 |
| 外部 Mahlo 加 W, 无 U_f 消去 | ≥ \|KPM\| = ψ_{Ω₁}(ε_{M+1}) | [原文] DS 2003 **Thm 6.4.1**, 见下 |
| IR | ≥ \|KPM\|; **上界未证** | [原文] DS 2003 **Cor 6.4.2**; DS 2024 脚注 2 |
| IIRD | 模型: `set` 为 V_M, `type` 为 V_Λ, Λ 是 M 之上第一个不可达; 作者说 "the ωth admissible above a recursive Mahlo" 应当够, 未做 | [原文] DS 2006 §8 |
| 归纳-归纳 | 与索引归纳定义同强度 | [转述] Nordvall Forsberg 2010 报告摘要 |
| Palmgren 高阶宇宙 | 猜想到 KPM | [原文] DS 2003 §1, DS 2006 (都写 conjectured) |
| CZF_π | 解释进 MLM + `Acc`; 主体在 Agda 用外部 Mahlo 模拟 | [原文] Takahashi LMCS 2025 |
| Kovács CSL 2022 的 IR 层级 | 层号外给, 不算强度 (FS §12 已记) | [转述, 手册已有] |
| Kovács POPL 2026 | 可数层 IIR 的典范性; "IR 精确强度未知" | [原文] 摘要, §5.3 |
| Coquand Mahlo 元理论 | 不动点是假设; 无 W, 判断在 BHO 之下 | [原文] 注记 5.6, 作者注明未细查 |

**"IR ≥ KPM, 模型在 ZFC + Mahlo" 的核对.** 读了原文, 两半来自不同论文:

- **下界.** DS 2003 §6.4 Thm 6.4.1 (归于 Setzer): 理论 T 有标准类型构造, 含 W, 消去到所有类型, 对每对 f, g 有 U_{fg}, 且 U_{fg} 无消去. T 的强度至少是 KPM. Cor 6.4.2 把它用到 IR. 证明是改编内部 Mahlo 的良序证明: 对每个 n 得 ψ_{Ω₁}(ω_n(M+1)) 的超限归纳, 极限是 ψ_{Ω₁}(ε_{M+1}) (印刷页 34-35, 读图). **n 是元归纳**, T 内没有 ∀n. 同一结论 Setzer 2004 附录 D 另述一次. 这是纸面证明, 未机检.
- **一致性上界.** 不在 DS 2003, 在 DS 1999 §6 Thm 1: ZF 加 AC 与 GCH 加一个 Mahlo 基数, `set` 解释为 V_M, 类型落在 V_Λ. 不用 GCH 时改强 Mahlo (脚注 7). 这只是一致性.
- **证明论上界.** 未做. DS 1999 §7 "should be easy", Setzer 2004 §7 "not yet spelled out", DS 2024 脚注 2 "has not been worked out yet". 期望区间 [|KPM|, |KPM⁺|], 精确值取决于 `OP_D` 是否贡献强度 [原文].

**这条上界管不到 Agda.** 上述 IR 只有 `set` 与 `type` 两层, 而 Agda 的每一层都能做 IR. Kovács 的说法是可数个 Mahlo [原文, 见 §3].

**DS 2024 到底给了什么.** 外部版的扩展谓词 Mahlo 用超出 IIRD 的索引 IR 形式化, Agda 检查过其模型构造; 意义是谓词性辩护. 它**没有**证 Agda 到 |KPM⁺|: 受限版 "likely to be meta-predicative"; 加归纳生成后才可嵌入, 且以 |CZFM⁺| = |KPM⁺| 这条 "plausible result" 为条件 (§5 末) [原文]. 代码未取得, 选项未知.

## 5. 目标问题的论证

**5.1 通道: 证明能转成树.** 若 T 有闭项给 `Acc a` (≺ 可判定, 项可枚举), 对 `Acc` 递归定义 `tree a (acc h) = lim (λ k → 若 enum k ≺ a 则 tree (enum k) (h …) 否则 0)`, 得闭树, 秩 ≥ a 的序型 [推断, 仓库未写]. 所以闭树秩的上确界 ≥ T 可证的段.

**5.2 反向与封顶, 都是判断.** 闭树秩 < |T| 是民间结论, 没有找到对 Agda 的证明 [推断]. 若有典范性, 闭树是递归树, 秩 < ω₁^CK [推断]. Agda 实现本身没有规范化证明; Kovács POPL 2026 证了一个核心理论的典范性: 可数宇宙层级, 每层有 IIR, 计算规则与 Agda 原生 IIR 相同 [原文, 摘要]; 其元理论本身带 IIR. 它不覆盖 Agda 的模式匹配与终止检查 [推断]. 任何一族 `ℕ → Ord` 的闭项都能再取 `lim`, 所以**上确界取不到**, 任何固定定义都会停在某处 [推断].

**5.3 Agda 比纸面 IR 多什么.** 改编证明卡在 "W(W) 不可定义, 因为不许对 type 作 W" (DS 2003 §6.4, 印刷页 34); Setzer 2004 附录 D: "cannot form the nth admissible set above W"; DS 1999 §7: 缺的是 "having the W-type on top". 而 Agda 在 `Set₁` 上就有 W, 且每层都能做 IR. 所以内部 Mahlo 的原证明大概可以照搬一层 [推断, 无人证明]. DS 2024 脚注 2 说在 Mahlo 上加宇宙能超过 IR 的猜想上界 [原文]; Agda 正有这些宇宙. 这是 (c) 判 "够" 与 (d) 判 "很可能" 的理由.

另一旁证: 我方归档 `Acc-endpt` 的类型是**内部** ∀n, 而 ML₁W 只能靠元归纳 [代码, 未重编; 证明如何绕过未读]. 若成立, Agda 这一片段已超过每个 ψ_{Ω₁}Ω_{I+n} 的逐条结果, 能写一棵秩 ≥ ψ_{Ω₁}Ω_{I+ω} 的单棵树 [推断].

**内部 Mahlo 不能写成 Agda `data`.** 正性检查拒绝 (SOURCES §122, Coquand 注记 5.5); 而 Agda 的 `data` 自带模式匹配, 一般消去规则又不一致 (Palmgren Thm 6.1, 经 DS 2024 §4) [原文]. 外部版 [代码]: `czf-in-mahlo/src/ExternalMahlo.agda`, 头 `--cubical-compatible --safe`, 对参数 f 定义 `𝕌 f`, 带 `codeW`.

**5.4 写法的必要条件: 定义用多少资源, 就封顶在多少.** 闭树秩不超过所用片段的强度 [推断]. 由此:

- 只用嵌套 W, 无真宇宙: 下界 ψ_{ℵ₁}(ℵ_ω), 上界用 KPl (Setzer 2004 §4). 我方主线已超过这个量级, 靠的是大消去 (`Uˢ`, `Ordˢ`, [Prefix](../OCF/Free/Prefix.lagda.md):50-57) [代码].
- 不用 IR 而只用归纳族、II 与 `Set ℓ`: 封顶在 MLTT 加 `Setω` 尾巴 (判断量级: 有限至 ω·2 个递归不可达, 远低于 |KPM|). `Setω` 这部分无文献 [推断]. **若此判断成立, (c) 不能只靠归纳族加大消去.** Setzer 的良序证明的力量在 "ℕ → Set 上的 distinguished sets" 与 U_f, 树只是输出.
- 证书主线底层 (`Free/Level`, `Free/Prefix`) 是 II 加大消去, 没见 IR; `Lv` 系列用 IR ([EBOTopIR](../OCF/Align/EBOTopIR.lagda.md):49) [代码, 只读这几处]. 到 (a)(b) 不用 IR 不是障碍 [推断].
- 用了 IR 也不等于到 Mahlo: `Lv` 是不带算子参数的 IR 宇宙, 而 Thm 6.4.1 的力量在 "对每个 f 有 U_f" [推断].

**5.5 Setzer 的 from-below 不封顶.** 重读原文 (p.7-10, 读图). Def 3.6: OT 是**原始递归**的记号系统, 带 Below 1-3. Lemma 4.3(b): 若 T 证 ℕ 上归纳、能解释 PRA、能定义 `Acc(OT, ≺)`, 则 T 证 OT 的超限归纳. p.10: "no ordinal notation system from below suffices to denote the proof-theoretic ordinal of a theory, in which we can define the accessible part". p.9: 这类系统序型 < BHO (Cor 5.8(b), 该推论本身未读). 同页提到 Feferman, Howard, Aczel 用超限类型指称序数的路子 "not directly comparable" [原文]. 读法 [推断]:

- 布劳威尔树不是这个定义的对象, 定理不给树任何上界.
- (a)-(d) 全在 BHO 之上, 所以不能指望 "写成从下面来, 良基自动得证".
- Agda 能定义 `Acc`, 所以任何从下面来系统的超限归纳都可证; 但它们太小, 帮不上这四个目标.

**5.6 壁垒不是强度界.** `Barrier` 推出的是 LPO, 这是构造性禁忌, 不是强度. 旁证: CZF + REA + RDC 加 LPO 强度不变 (Rathjen 2016 Thm 5.2(xiii)) [原文]; 对 Agda 的类比是 [推断]. 所以壁垒封的是**写法** (派发机制), 不是序数高度. 它和 §5.5 都是元层结论, 合不成 "不可超越" 定理.

**5.7 秩不等于增长率.** 通道造出的树, 基本列是枚举序, 不单调, 也不带 Bachmann 性质 (仓库归档的 `Fₙ` 用范数列, 候选表完整性未证). 秩够了, FGH 的值未必有相应增长 [推断]. 而大数按纲领是树上 FGH 的值, 所以 "强度够" 对目标是必要条件, 不充分.

**5.8 Coquand 注记 5.6 的 "countable Brouwer ordinals do not suffice".** 说的是: 在他的 PER 模型里, 构造 Mahlo 不动点的**阶段**走 ω 迭代到不了闭包点, 要分支在 `Set` 上的序数. 不是说闭合树的秩不够. 注记标 informal [原文].

## 6. 与已有记录的冲突

| 记录 | 说法 | 核对后 |
|---|---|---|
| `archive/src/Mahlo/SOURCES.md:255` | DS 2024 "旁证标准 IR 到不了 Mahlo" | **层次错了.** 内部 Mahlo 的**定义**超出 IR, 但**强度**上 DS 2024 脚注 2 明说 "leaves open the possibility that IR and IIRD reaches the strength of type theory with one Mahlo universe" |
| `SOURCES.md:261` | "模型在 ZFC＋Mahlo (＋0-不可达)", 归于 DS 2003, 仅摘要 | 下界确在 DS 2003. 模型在 DS 1999 §6: ZF + AC + GCH + Mahlo, 类型落在 M 之上第一个非正则 ℵ-不动点 V_Λ, 标准模型 V_{M⁺}. 原文无 "0-不可达" 字样. DS 2024 概括为 "a Mahlo cardinal and an inaccessible above it". 证明论上界是另一件事, 未做 |
| [code/WellOrderProofs.md](code/WellOrderProofs.md):277 | MLTT + W + 一个宇宙 "KPi 级, 未核" | 两个系统同名, 见 §2. "不存在强度壁垒" 的结论不变 |
| [OrdinalNotationsFS.md](OrdinalNotationsFS.md):470 | Coquand Mahlo 是 "强有力的类型论方基础" | 他的理论无 W, 判断在 BHO 之下 (注记 5.6). 同文引言说强度是 KPM, 指带 W 的 Setzer 宇宙. 不能作强度旁证 |
| FS:468-469, 手册 §9 | Takahashi 2024, arXiv | 已发表: LMCS 21(4), 2025. 内容无冲突 |
| 记忆 `from-below-notations-theorem` 的 How to apply | "能到的强度 < 任何含 W 的理论" | 与同文 2026-11-01 精确化矛盾. 那句话只对 Def 3.6 的系统成立, 不对树 (§5.5). 本次未改记忆 |
| Kovács 2026 §5.3 | "Setzer [2000] calculated the strength of ... one **external** Mahlo universe" | 文献内冲突: Setzer 2000 是内部版, 外部版只有 DS 2003 的下界. 以 DS 2003 为准 |
| DS 2006 引言 | IIRD 与 W 加 Mahlo "equal proof-theoretic strength" | 文献内冲突: 顺带一句, 无证明. DS 2024 脚注 2 (更晚) 说上界未做. 以后者为准 |
| Agda 手册 `--safe` 词条 | 只防 sized 与 guardedness 同开 | `safe-agda` 页与源码: `--sized-types` 单独就 unsafe. 以源码为准 |

## 7. 待核

| 项 | 状态 |
|---|---|
| MLTₙW 的序数值 | Rathjen 2016 说细节见其 [63], 未发表 |
| Rathjen, 超宇宙 Part I, II (AML 2000/2001) | **未取得**, 付费; 只有摘要 |
| Griffor-Rathjen 1994; Rathjen 2003 (CZFM); Rathjen-Griffor-Palmgren 1998 | **未取得** |
| DS 2024 的 Agda 代码 (`gitlab.com/setzer/...`) | **未取得**; 选项与是否 `--safe` 未知 (CodeGuide 已记) |
| Setzer, 宇宙 Part II (自主 Mahlo, Π₃-反射宇宙) | `modelautomahlomain.pdf` 已下载, **未读**; 另一副本 Swansea 连接失败 |
| Nordvall Forsberg 论文与 2010 报告 | 只见检索摘要; 报告页直取 404 |
| Vytiniotis-Coquand-Wahlstedt 2012 | 只见摘要 |
| Agda 检查器到消去子的翻译 | 没查到; Cockx 2017 博士论文未读 |
| #5910, #8572 | 未复现, 只读 issue |
| \|KPi\| 的数值 ψ_{Ω₁}(ε_{I+1}) | 文献常识, 本次没读原文; 结论只用 Rathjen 的强度等价 |
| Kubánek 2025 (外部 Mahlo 典范性) | 未读, 经 Kovács 2026 |
| 能把 (a)(b) 升档的两个小定理 | `Acc`→树的秩下界 (§5.1); EBO→OT_I 保序 (现只有测试) |
| 一条能实打实升档的研究题 | 把 DS 2003 Thm 6.4.1 搬到 Agda, 并查 W(W) 在 `Set₁` 是否走通. 这才把 (c)(d) 从判断变成定理. 只是记号侧, 不进成品 |

## 8. 来源

访问日 2026-11-03. 正文引述均在所列版本上核对; 个别 PDF 文本层损坏, 已注明读图.

- Dybjer, Setzer, *Induction-recursion and initial algebras*, APAL 124 (2003): <https://csetzer.github.io/articles/inductionrecursion.pdf> (作者副本; §6, 印刷页 33-35).
- Dybjer, Setzer, *A finite axiomatization of inductive-recursive definitions*, TLCA 1999: <https://www.cse.chalmers.se/~peterd/papers/Finite_IR.pdf> (文本层损坏, 读图 p.9-14).
- Dybjer, Setzer, *Indexed induction-recursion*, JLAP 66 (2006): <https://www.cse.chalmers.se/~peterd/papers/Indexed_IR.pdf> (引言, §8).
- Dybjer, Setzer, *The extended predicative Mahlo universe in Martin-Löf type theory*, JLC 34(6) (2024): <https://research.chalmers.se/publication/536011/file/536011_Fulltext.pdf> (§2, 脚注 2, §4, §5, §12).
- Setzer, *Proof theory of Martin-Löf type theory, an overview* (2004): <https://csetzer.github.io/articles/overviewProofTheoryTypeTheory2004.pdf> (§2, §4-§7, 附录 D).
- Setzer, *An introduction to well-ordering proofs in Martin-Löf's type theory* (1998): `archive/src/Mahlo/Sources/setzer1998-intro-wellordering.pdf` (读图 p.7-10).
- Setzer, *Universes in type theory part I*: `archive/src/Mahlo/Sources/setzer-partI.txt` (摘要, §4 标题; Theorem 5.3 见 SOURCES §113).
- Rathjen, *Proof theory of constructive systems: inductive types and univalence* (2016): <https://arxiv.org/abs/1610.02191> (Thm 5.2, 6.4, Cor 6.7, 7.2).
- Rathjen 超宇宙摘要: <https://www.philpapers.org/rec/RATTSO>, <https://www.philpapers.org/rec/RATTSO-2>.
- Kovács, *Canonicity for indexed inductive-recursive types*, PACMPL 10, POPL (2026): <https://andraskovacs.github.io/pdfs/ir_canonicity.pdf> (§4.1.2, §5.3).
- Takahashi, *Interpretation of inaccessible sets in Martin-Löf type theory with one Mahlo universe*, LMCS 21(4) (2025): <https://arxiv.org/abs/2402.15074>; 代码 `src/ExternalMahlo.agda` @ <https://github.com/takahashi-yt/czf-in-mahlo>.
- Coquand, *A Russell-style Mahlo universe*: <https://github.com/coquand/agda-mahlo-universe> (README, `notes/mahlo-results.pdf` §5, 注记 5.5-5.6; 该库用 Agda 2.9.0).
- Agda `v2.8.0`: <https://github.com/agda/agda/tree/v2.8.0> (`doc/user-manual/language/{safe-agda,without-k,sort-system,mutual-recursion,lossy-unification,prop,termination-checking}`, `tools/command-line-options`, `src/full/Agda/Interaction/Options/Base.hs`, `src/full/Agda/Termination/{Termination,TermCheck}.hs`).
- Agda issues, 标 `false` 且未关的 13 条: <https://github.com/agda/agda/issues?q=is%3Aissue+is%3Aopen+label%3Afalse>; 尤其 #5910, #8572, #4966.
- Sized types 不一致的新近讨论: <https://arxiv.org/abs/2602.18921> (只读摘要).
- Vytiniotis, Coquand, Wahlstedt, *Stop when you are almost-full*, ITP 2012 (只见摘要). Nordvall Forsberg 报告与论文: <https://personal.cis.strath.ac.uk/fredrik.nordvall-forsberg/thesis/thesis.pdf> (未读全文).

**检索范围 ("没有直接结果").** 英文关键词 "proof-theoretic strength of Agda", "consistency strength induction-recursion universe hierarchy" 等几轮网页检索, 加上述论文的相关工作节. 没查邮件列表全量与专著.
