# KP + ω₁ 与 Mahlo 序数: 哪个大, 差多少

调研日期 2026-11-05. 作者原问: "Mahlo 序数和 KP+ω₁ 哪个大? 大概相差多少?"

## 直接回答

**在最自然的读法下, KP+ω₁ 大得多.** 把 "KP+ω₁" 读成 "KPω + 存在不可数序数" (Arai 记作公理 (ω₁)), 把 "Mahlo 序数" 读成 KPM 的证明论序数 |KPM| = ψ_Ω(ε_{M+1}) (社区叫 Small Rathjen ordinal). 两者之间至少隔着下面这串, 每一级都严格变大:

> |KPM| = ψ_Ω(ε_{M+1}) < |KPM⁺| = ψ_Ω(Ω_{M+ω}) < |KP+Π₃-Ref| = Ψ_Ω(ε_{K+1}) < |KP+Π_ω-Ref| < |Stability| < |KPω+Π¹₁-Ref| < |Σ¹₃-DC+BI| = ψ_Ω(ε_{𝕀+1}) < … < |Σ¹_{N+2}-DC+BI| = ψ_Ω(ε_{𝕀_N+1}) < … < |Z₂| = ψ_Ω(𝕀_ω) < |KP+ω₁|.

前面一段是 Mahlo 型反射的第一层 (Π₂-反射). 中间要走完 Π₃ 到 Π_ω 反射、稳定性、Π¹₁-反射, 再走完对每个 N 的 Π_N-Collection, 才到全二阶算术 Z₂. KP+ω₁ 还在 Z₂ 之上: 它证明 L_{ω₁} 是 ZF⁻ 的传递模型, 从而证明 Z₂ 的 Π¹₁-可靠性 (§3).

**置信度.**
- "KP+ω₁ > |KPM|": 高. 依据是一手文献给出的链 (Rathjen 1991, Arai 2311.12459), 加上一步标准的纸面论证 (KP+ω₁ ⊢ RFN_{Π¹₁}(Z₂), 下面标 [判断]).
- "差多少": 只能给下界和中间标志. KP+ω₁ 的证明论序数**没有**文献给出过; Arai 只对更强的 T₁ = KPω+(V=L)+Π₁-Collection+(ω₁) 做了相对于 ω₁ 的 "提升" 分析, 那不是可计算的证明论序数.
- 第 2 节列了会让结论反转的读法: 把 "KP+ω₁" 读成 KPω, 或把 "Mahlo 序数" 读成最小递归 Mahlo 序数本身. 前一种只是名字混淆; 后一种拿非递归序数去比证明论序数, 两边口径不一.

**按本仓库的强度写法.** 两者都不能写成 ψ₀(Ω_x) 且 x 只用 Ω 的算术. 只用 Ω 算术的 ψ₀(Ω_x) 到 EBO (Ω-塔的极限) 为止. 而 |KPi| = ψ_Ω(ε_{I+1}) 已经要用不可达基数 I, |KPM| 要用 Mahlo 基数 M, |Z₂| 要用 Arai 的 𝕀_N 族. 所以这里照文献原样写 ψ_Ω (Ω = ω₁ 或 ω₁^CK, 只坍缩到 Ω 以下的那一层), 不作换算.

## 1. 档次标记

- **[证]**: 文献里有证明, 且我读到了陈述所在的那一页.
- **[证·未读原文]**: 文献声称有证明, 我只见到二手转述 (维基表格等).
- **[预印本]**: 只在 arXiv 上, 未见期刊发表.
- **[社区]**: googology wiki 等社区来源, 未经证明.
- **[判断]**: 我自己的纸面论证或推断.

## 2. "KP+ω₁" 的各种所指

| 读法 | 理论 | 证明论序数 | 与 \|KPM\| 比较 | 档次 |
|---|---|---|---|---|
| A (推荐) | KPω + "存在不可数序数" (等价地加 V=L, 存在不可数正则序数) | 无文献值; 严格大于 \|Z₂\| = ψ_Ω(𝕀_ω) | **KP+ω₁ 远大** | 下界 [判断] + [预印本] |
| B | Arai 的 T₁ := KPω + (V=L) + (Π₁-Collection) + (ω₁) | 无可计算序数值; Arai 给的是 ω₁ 以下的界 Ψ_{ω₁}(ω_n(ρ₀+1)) | **T₁ 远大** (T₁ ⊇ A) | [预印本] |
| C | 把 "KP+ω₁" 读成 KPω (KP 加无穷公理, 标准模型 L_{ω₁^CK}) | Bachmann–Howard 序数 ψ_Ω(ε_{Ω+1}) | **\|KPM\| 远大** | [证] (Jäger, Pohlers 等经典结果) |
| D | Arai 1801.10025 定理 1.4 的基础理论 "KPω + (V=L) + 常元 ω₁ (只有 ω < ω₁ < ρ₀)" | 与 KPω+V=L 同, 即 BHO | **\|KPM\| 远大** | [判断] (常元只带序关系公理, 是保守扩张) |

### 2.1 读法 A 与 B 的出处

- Arai, *ω₁ under Π₁-Collection*, arXiv:1508.01547 (2015) §1: "Let (ω₁) denote an axiom stating that 'there exists an uncountable regular ordinal', and T₁ := KPω + (V = L) + (Π₁-Collection) + (ω₁)". 定理 1.1: 若 T₁ ⊢ ∃x∈L_{ω₁} φ(x) (φ 是 Σ₂ 公式), 则对某个 n 有 T₁ ⊢ ∃x∈L_{Ψ_{ω₁}(ω_n(ρ₀+1))} φ(x), 其中 ρ₀ 是 ω₁ 之上最小的使 L_{ρ₀} ⊨ Π₁-Collection 的序数. 定义 2.7 把 (ω₁) 写成 Skolem 包与 Mostowski 坍缩的形式 (正则性的改写). [预印本]
- Arai, *Cut-elimination for ω₁*, arXiv:1801.10025 (2018) §1, 定理 1.4: 在 KPω+(V=L) 上, RFN_{Σ₂}(T₁) 等价于记号系统 T(ε_{ρ₀+1}) 上的一个存在性断言 ∀a A(a). [预印本]
- Arai, *Lifting up the proof theory to the countables: Zermelo–Fraenkel set theory*, arXiv:1101.5660 (v5, 2013). 定理 1.1 对 ZF+(V=L) 做同类工作: 界是 Ψ_{ω₁,n}(ω_n(I+1)), 且 Ψ_{ω₁}(ε_{I+1}) 等于 ZF+(V=L)-可证可数的序数的上确界 (原文第 62–64 行附近). 这是 B 的上层同类, 说明 "提升到 ω₁" 是 Arai 的一条专门路线. 期刊信息未核 (记忆中是 JSL 2014).

**这些结果不是证明论序数.** Arai 的 Ψ_{ω₁}(…) 是 ω₁ 以下的界, 依赖真正的 ω₁, 不是可计算的良序. 文献里没有找到 "KP + ω₁ 的证明论序数 = 某个 ψ 项" 这样的结果 (Wikipedia 的 *Ordinal analysis* 大表没有这一行, arXiv 与搜索引擎也没查到).

### 2.2 读法 A 的下界: 为什么严格超过 Z₂ [判断]

纸面论证, 未形式化, 也没有在文献里找到逐字出处. 我认为是集合论的标准事实:

1. KP 证明 L 是 KP 的内模型. V 中不可数的序数在 L 中也不可数, 所以 KP + ∃不可数 能解释 KP + V=L + ∃不可数.
2. 在 KP + V=L 中取不可数的 α. 由凝聚引理, L-可数的序数及其见证都在 L_{ω₁^L} 中, 所以 ω₁^L = {β<α : ∃f∈L_α (f: ω ↠ β)} 由 Δ₀-分离得到, 是一个集合. 它在 L 中正则, 因为 L 有可定义良序, 可数个可数集的并可以典范地枚举.
3. 于是 L_{ω₁} 是一个集合. KP 能对集合结构定义满足关系, 再加凝聚与 Skolem 包论证, 得到 "L_{ω₁} ⊨ ZF⁻ + V=HC" (一致地对所有公式码成立). ZF⁻ + V=HC 与 Z₂ 互相解释, 所以 L_{ω₁} ∩ P(ω) 是 Z₂ 的 β-模型 (相对于 L).
4. 所以 KP+ω₁ ⊢ RFN_{Π¹₁}(Z₂). Arai 2311.12459 §8 定理 8.2 之后写明, 在 RCA₀ 上 TI(ψ_Ω(𝕀_ω)) 与 RFN_{Π¹₁}(Z₂) 等价. 于是 KP+ω₁ 证明 ψ_Ω(𝕀_ω) 整段良基, |KP+ω₁| > ψ_Ω(𝕀_ω) = |Z₂|.

上界: ZFC 证明 L_{ω₂} (或 ω₁ 之上第一个容许序数处的 L) 是它的模型, 所以 KP+ω₁ 远低于 ZFC. 它与 Z₃ (三阶算术) 及各片段的确切位置没有查到文献, 不作断言.

## 3. "Mahlo 序数" 的各种所指

| 所指 | 值 (ψ 的种类) | 出处 | 档次 |
|---|---|---|---|
| \|KPM\|, 社区称 Small Rathjen ordinal | ψ_{Ω₁}(ε_{M+1}). Buchholz 型 ψ, M 为弱 Mahlo 基数, Ω_σ = ℵ_σ | Buchholz 1993 第 6 页定理与推论: \|KPM\| ≤ ψ_{Ω₁}(ε_{M+1}) (上界; 我读了原页图像) | [证] |
| 同上, Rathjen 的 χ-记号写法 | θ = ψ_{χ0 0}(ψ_ξ 0), ξ := χ_{ε_{M+1}} 0, 其中 χ0 0 = Ω | Rathjen 1991, AML 30, 定理 7.15: \|KPM\| = θ. 上界在 7.14, 下界引 Rathjen 的良序证明 [14] (OCR 读出, 符号有乱码, 对照维基的转写) | [证] |
| 同上, 以递归大序数为基础的写法 | ψ_Ω(ε_{M+1}), M 为递归 Mahlo | Rathjen 1994, AML 33, 35–55 (付费, 未读); 维基 *Large countable ordinal* 引用它 | [证·未读原文] |
| Rathjen 1990 记号系统 T(M) 的序型 | T(M) ∩ M = C_{χ00}(ψ_ξ 0) ∩ ψ_ξ 0, ξ := χ_{ε_{M+1}} 0 | Rathjen 1990, AML 29, 定理 6.3 | [证] |
| \|KPM⁺\| / Mahlo 宇宙类型论 TTM | ψ_{Ω₁}(Ω_{M+ω}) | Setzer 1996 (经维基表格; 仓库 `archive/src/Mahlo/SOURCES.md` §77.3 作对照用) | [证·未读原文] |
| 社区的 "ψ(M)" 一类写法 | 社区简化版 Rathjen ψ 中的 ψ_Ω(M) 等 | googology wiki *Rathjen's psi function* 等页; 本轮该站返回 Cloudflare 质询或 HTTP 402, 按规则未绕开, 未读 | [社区], 未读 |
| 最小递归 Mahlo 序数 μ | 非递归的可数序数, > ω₁^CK; L_μ 是 KPM 的标准模型 | Rathjen 1991 引言; 维基 *Large countable ordinal* | [证] |

各读法的大小关系:

- **\|KPM\| 及社区的 Mahlo 层 ψ 值 vs 读法 A/B**: KP+ω₁ 大得多, 依据见下面的链 (§4).
- **最小递归 Mahlo 序数 μ vs 读法 A 的证明论序数**: μ 更大, 因为 μ 不可计算, 而 KP+ω₁ 是 Π¹₁-可靠的 Σ¹₁-可公理化理论, 其证明论序数可计算. 但这是在拿 "模型高度" 比 "证明论序数", 口径不一.
- **口径一致地比模型高度**: L_μ ⊨ KPM. 而 KP+ω₁ 的 L-模型高度必须超过 ω₁^L, 且 μ < ω₁^L (L 认为 μ 可数). 所以又是 KP+ω₁ 大 [判断].
- **社区写法**: Mahlo 层的 ψ_Ω(…) 值 (参数只用一个 M 及其下的运算, 例如 ψ_Ω(M), ψ_Ω(ε_{M+1}), ψ_Ω(Ω_{M+ω})) 都在 |KP+Π₃-Ref| = Ψ_Ω(ε_{K+1}) 之下 [判断: 依据是 Rathjen 的 Π₃-反射记号包含 Mahlo 层, 没有逐个核对社区定义], 所以都小于 |Z₂|.

## 4. 中间标志: 从 |KPM| 到 |Z₂|

下表除标明外取自 Wikipedia *Ordinal analysis* 的大表 (二手), 括号里是表格引用的一手来源. 只有 Rathjen 1991 的引言与 Arai 2311.12459 的定理 1.3, 1.4, 8.2 我读了原文.

| 理论 | 证明论序数 | 来源 | 档次 |
|---|---|---|---|
| KPi (递归不可达) | ψ_Ω(ε_{I+1}) | Jäger–Pohlers 1982 | [证·未读原文] |
| KPM, Δ¹₂-CA+BI+(M) | ψ_Ω(ε_{M+1}) | Rathjen 1991; 二阶算术侧见 Rathjen 1996 MLQ 42 | [证] |
| KPM⁺, TTM | ψ_Ω(Ω_{M+ω}) | Setzer 1996 | [证·未读原文] |
| KP + Π₃-Ref (Large Rathjen ordinal) | Ψ⁰_Ω(ε_{K+1}), K 为弱紧 | Rathjen 1994 *Proof theory of reflection* | [证·未读原文] |
| KP + Π_ω-Ref | Stegert 的 Ψ 项 | Stegert 2010 | [证·未读原文] |
| Stability | Stegert 的 Ψ 项 | Stegert 2010 | [证·未读原文] |
| KPω + Π¹₁-Ref, KPω + (M ≺_{Σ₁} V) | ψ_{ω₁^CK}(ε_{𝕊⁺+1}) | Arai 2023, arXiv:2304.00246, 2304.03851 | [预印本] |
| Σ¹₃-DC+BI, KPω + Π₁-Collection + (V=L) | ψ_Ω(ε_{𝕀+1}) | Arai, arXiv:2311.12459 定理 1.3 (N=1) | [预印本] |
| Σ¹_{N+2}-DC+BI, Δ¹_{N+2}-CA+BI, KPω + Π_N-Collection | ψ_Ω(ε_{𝕀_N+1}) | 同上, 定理 1.3 | [预印本] |
| Z₂, ZFC − Power (Σ^Ω_1-序数) | ψ_Ω(𝕀_ω) := sup_N ψ_Ω(𝕀_N) | 同上, 定理 1.4 | [预印本] |
| KP + ω₁ (读法 A) | > ψ_Ω(𝕀_ω), 无文献值 | §2.2 | [判断] |

两条一手的定位语:

- Rathjen 1991 引言: KPM "is much stronger than KPi but in strength way below the subsystem of second order arithmetic based on Π¹₂ comprehension". 即 |KPM| < |Π¹₂-CA₀|. [证]
- Arai 2311.12459 定理 1.3 与 1.4: Z₂ 的证明论序数是 ψ_Ω(ε_{𝕀_N+1}) 对 N 的上确界, 其中 𝕀_N 满足 L_{𝕀_N} ⊨ KPω + Π_N-Collection + (V=L). Π¹₂-CA₀ ⊆ Δ¹₃-CA, 所以 |Π¹₂-CA₀| ≤ ψ_Ω(ε_{𝕀+1}). [预印本]

**"差多少" 的说法.** KPM 处在反射层级的第一层 (Π₂-反射, 即递归 Mahlo). Z₂ 要求对每个 N 都有 Π_N-Collection, 这已在全部 Π_n-反射、稳定性与 Π¹₁-反射之上 (上表顺序). KP+ω₁ 又在 Z₂ 之上一步, 因为它把 Z₂ 的整个模型 L_{ω₁} 当作一个集合. 用 ψ_Ω 的下标说: |KPM| 的下标是 ε_{M+1}, M 是一个 Mahlo; |Z₂| 的下标是 𝕀_ω, 是 "N-稳定" 族对所有 N 的极限; KP+ω₁ 的下标还要更高, 没有文献值. 上面是对文献链的复述. 没有任何定理给出两者之间的 "距离" 量度, 所以不写倍数或层数之类的数字.

## 5. 论文出处

**一手, 读过陈述所在页**

- T. Arai, *An ordinal analysis of Π_N-Collection*, arXiv:2311.12459 (v1 2023-11-21, v4 2025-08-12; abs 页无期刊信息). 定理 1.1–1.4, §8 定理 8.2 及其后的 TI(ψ_Ω(𝕀_ω)) ⇔ RFN_{Π¹₁}(Z₂). 它的前身 arXiv:2112.09871 (*An ordinal analysis of Π₁-Collection*) 已由作者撤回, 撤回说明称内容并入 2311.12459.
- T. Arai, *ω₁ under Π₁-Collection*, arXiv:1508.01547 (2015), §1, 定义 2.7.
- T. Arai, *Cut-elimination for ω₁*, arXiv:1801.10025 (2018), §1 定理 1.4.
- T. Arai, *Lifting up the proof theory to the countables: Zermelo–Fraenkel set theory*, arXiv:1101.5660 v5 (2013), 定理 1.1.
- M. Rathjen, *Proof-theoretic analysis of KPM*, Arch. Math. Logic 30 (1991) 377–403. 引言, 定理 7.14, 7.15. 读的是 Leeds 主页 PDF 的 Wayback 存档 (链接见 `OrdinalNotationsGuide.md` 第 464 行), OCR 有乱码.
- M. Rathjen, *Ordinal notations based on a weakly Mahlo cardinal*, Arch. Math. Logic 29 (1990) 249–263, 定理 6.3. 同上, 存档 PDF.
- W. Buchholz, *A note on the ordinal analysis of KPM*, Logic Colloquium '90, Lecture Notes in Logic 2 (1993) 1–9. 第 6 页的 Theorem 与 Corollary |KPM| ≤ ψ_{Ω₁}(ε_{M+1}). 仓库已存 `archive/src/Mahlo/Sources/buchholz1993-kpm-note.pdf`, 本轮渲染原页图像核对.

**二手**

- Wikipedia *Ordinal analysis* (wikitext, 2026-11-05 取): 大表中 KPM, KPM⁺, Π₃-Ref, Π_ω-Ref, Stability, Arai 诸行.
- Wikipedia *Rathjen's psi function*: "Small Rathjen ordinal" 的名称; T(M) 序型 ψ_Ω(χ_{ε_{M+1}}(0)) 与 |KPM| = ψ_Ω(ψ_{χ_{ε_{M+1}}(0)}(0)). 与 Rathjen 1991 定理 7.15 的转写一致.
- Wikipedia *Large countable ordinal*: |KPM| = ψ(ε_{M+1}) (引 Rathjen 1994); 递归 Mahlo 序数的定义.

**未取得**

- Rathjen 1994 (AML 33, *Collapsing functions based on recursively large ordinals*): 付费.
- googology wiki 各页与 Cantor's Attic: 本轮返回 Cloudflare 质询或 HTTP 402, 按规则不绕开. 所以社区对 "Mahlo 序数" 的具体命名 (如 "large/small Mahlo ordinal" 是否存在) 未核. 搜索结果里只见到 "Small/Large Rathjen ordinal" 这对名称 (Wikipedia 与个人站点), 没见到 "small/large Mahlo ordinal".
- 中文社区 "KP+ω₁" 的原始出处: 中英文搜索都没有找到. 读法 A 是按字面推定的.

## 6. 对本仓库的意义

不影响纲领与当前路线. 两者都远在主线的 EBO 目标之上. 如果以后要用 Mahlo 层作参照, 仓库已有的 `archive/src/Mahlo/` 材料 (Setzer OT_M, Maksudov, Rathjen T(M)) 是对应的入口. KP+ω₁ 层没有可用的记号系统, 也没有证明论序数, 不宜作为验收参照.
