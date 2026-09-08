# 交接报告：Lens、大序数与快速增长层级

本报告接续《研究方向交接：Lens 与类型论中的大序数构造》，记录第二轮工作的全部结果。
**只报告结果，不给建议、不排优先级。**

标注：
**【核实】** 读到原文或权威二手引用 ·
**【推导】** 本轮的逻辑推演，未与任何论文核对 ·
**【机验】** Agda 类型检查通过 ·
**【未验】** 仍未验证

---

# 第一部分：文献核实

## 1.1 CHS 1997 *Ordinals in Type Theory*【核实】

- `http://www.cse.chalmers.se/~coquand/ordinal.ps` **链接仍有效**，返回 PostScript 二进制。
- 说明页 `cse.chalmers.se/~coquand/ord.html`（最后修改 1998-05-28）仍在线。内容：
  - 目标是给 **MLTT + 一个宇宙**的序数一个**直接构造**；该序数 Aczel 已算出，但现有证明"非常间接"（very indirect）。
  - lens 是为这个直接构造引入的（"introduces the notion of lenses for this purpose"）。
  - 另有计划：把序数表示成迭代集，用于模型化 Aczel 的 CZF，出发点是 Jervell 的想法。
- 原文内容**未读到**（PostScript，本轮环境无法转换）。lens 的原始定义与 MGS'08 讲义版是否一致：**未验**。

## 1.2 Hancock 博士论文 *Ordinals and Interactive Programs*（Edinburgh 2000）【核实】

- 稳定链接：`https://www.lfcs.inf.ed.ac.uk/reports/00/ECS-LFCS-00-421/`（技术报告 ECS-LFCS-00-421）。
  另有 `http://hdl.handle.net/1842/376`。
  提供格式：PDF / PDF.gz / PS / PS.gz / DVI / DVI.gz。
- **摘要关键句**：构造在"有自然数类型、以及一个**对广义笛卡尔积封闭的外部宇宙序列**（an external sequence of universes closed under generalised Cartesian products）"的 Martin-Löf 式类型论中完成。lens 被描述为"自 Gentzen 以来在良基性证明中一直隐含存在的谓词变换器"，作者明说希望它用于"以代数的、系统化的方法为更强类型论设定**下界**"。
- **目录（已核实）**：
  - Ch. 4 **Lenses**（p. 96）
    - 4.1 Ordinals（96）
    - 4.2 Ω（102）：4.2.1 序数记号的 data type / 4.2.2 transition structure / 4.2.3 相关概念 / 4.2.4 **两个 Ω 良基性证明**
    - 4.3（111）：4.3.1 算术表达式 / 4.3.2 **The theory of lenses**（115）/ 4.3.3 **Miniaturisation of the theory of lenses**（117）
  - Ch. 5 Conclusions；5.1.3 Lenses（130）
  - Appendix A 算术组合子；Appendix B Ω 可达性的形式化证明
  - Appendix C **Formal development of theory of lenses**：C.1 basic amenities / C.2 natural numbers / **C.3 Next Universe construction** / C.4 official notation system / C.5 unofficial notation system / C.6 the theory of lenses
- **正文未读到。** PDF 由老式 dvips 生成，字体为位图/Type3，文本层不可提取（本轮抽取结果为乱码）。
- 交接文档所列两处 TODO（lens 极限、dependent lens）在论文中的位置：**未验**，仅从目录推测落在 4.3.2 / 4.3.3 / C.3 / C.6。

## 1.3 Hancock 猜想的两半【核实】

- **有限层**：KNFX (CPP 2020) 记载，Hancock 用 lens 给出猜想"一半"的干净证明；猜想内容为 **n 个宇宙的 MLTT 可达 φ_{ε₀}(0) 嵌套 n 次的序数**。记 Θ₀ = ε₀，Θ_{n+1} = φ_{Θ_n}(0)。KNFX 同时指出 CHS 在纯 Church 编码设定下已达 φ_{ε₀}(0)。
- **极限层**：**MLTT + 无穷多宇宙、无 W-类型，证明论序数为 Γ₀。**由 Hancock 本人猜想（记载于 Martin-Löf 1975），**Aczel 与 Feferman 独立证明**。
- 一致性：Γ₀ 是 α ↦ φ_α(0) 的最小不动点，故 sup_n Θ_n = Γ₀。两条对得上。
- **对交接文档 §5 的修正**：原文档记「CHS 证明了其中一半，哪一半、另一半状态需核实」。结果是：lens 覆盖的是**下界**；上界在极限处（Γ₀）已由 Aczel–Feferman 关闭。
- 附带结论：**Hancock 阶梯 Θ₀…Θ_n 全部 < Γ₀。**有限宇宙的整条证明论阶梯位于 Γ₀ 以下。

## 1.4 lens 是否被形式化过【核实：没有】

证据链：
- **Escardó**（`Ordinals.Codes`, 2011）自陈 "Here I do something more modest, **without lenses**"，并把读者指回 Hancock 主页。
- **KNFX (CPP 2020)** 明说 Hancock 用 lens 证了猜想一半，"in contrast, in our work we are not restricting ourselves to a spartan type theory"——他们做的是易用表示，未实现 lens。
- **de Jong–Kraus–Nordvall Forsberg–Xu**（LICS 2023 / LICS 2025，后者用 Agda 2.8.0）的形式化基于 TypeTopology + agda/cubical，围绕序数的序理论与算术，无 lens。
- 检索 Agda / Coq / Lean 中的 "lens"，命中全部为 bidirectional programming / optics 意义下的 lens，与 CHS 的 lens 同名异物。

## 1.5 宇宙–序数对应的数值【核实】

- MLTT + ω 个宇宙、**无 W-类型** = Γ₀（Aczel、Feferman）。
- MLTT + W-类型 + 一个宇宙：Setzer 1993 证明远大于 Γ₀。
- |MLTT + N + W + U| = |KPI⁺| = ψ_{Ω₁}(Ω_{I+ω})（交接文档原记载，本轮未独立复核）。
- **|MLM| = ψ_{Ω₁}(Ω_{M+ω})**，MLM = MLTT + Setzer 的 Mahlo 宇宙 V（Setzer, *Extending Martin-Löf Type Theory by one Mahlo-universe*, Arch. Math. Log. 39, 2000）。上界由该文给出，与 Se96a 合起来说明界是紧的。
- Setzer, *Well-ordering proofs for Martin-Löf type theory*, APAL 92 (1998) 113–159：ML₁W 下界的完整构造。**本轮未读。**
- Setzer 2004 overview 存在性已确认，**未读**。

## 1.6 其他【核实】

- Hancock 旧主页仍在线：`https://www.dcs.ed.ac.uk/home/pgh/index.html.KEEP`（最后修改 2000-05-20）。含指向 `chat.html`、`people.html`、CV 的链接。**未含 lens 相关材料的直接链接。**
- **Russell'08 Swansea 幻灯片：本轮未能定位到有效链接。**Escardó 将其列为 lens 的第二来源。

---

# 第二部分：推导

以下全部为本轮推演，未与任何论文核对；其中大部分随后被机器验证（见第三部分）。

## 2.1 FGH 是 Ω-代数在 `ℕ→ℕ` 上的实例【推导 → 机验】

令 `𝔽 = ℕ → ℕ`：

```
z_𝔽 = suc                s_𝔽 g = λn. gⁿ(n)         l_𝔽 G = λn. G n n
F_α := α 𝔽 z_𝔽 s_𝔽 l_𝔽
```

- `t₀ = z` ⟹ `F₀ = suc`
- `t₁ = s z` ⟹ `F₁ = λn. 2n`
- `t_ω = l(n ↦ Iⁿ s z)` ⟹ `F_ω = λn. F_n(n)`

推论：**基本列不需要"产出"。`l : (ℕ→X)→X` 构造子本身就是基本列指派。**经典 FGH 中"为每个极限序数选一条基本列"的自由度，在 Church 编码里被吸收进项本身。同一序数的不同 Brouwer 树 = 不同的基本列指派 = 不同的 `F_α`。

对交接文档陷阱 4（外延性与基本列的张力）的影响：FGH 侧需要的正是商掉后会丢失的信息。

## 2.2 lens 的 FGH 版实现关系【推导 → 机验】

实现关系两边取 `X = 𝔽`：

```
F_{φ(α)} = D_𝔽 ( α (F 𝔽) Z_𝔽 S_𝔽 L_𝔽 )
```

对 Gentzen lens，`F 𝔽 = (ℕ→ℕ) → (ℕ→ℕ)`，即快速增长函数上的泛函。

手算验证（后经机验）：
- α = 0：`D(Z) = Z(suc) = λn. 2n = F₁ = F_{ω⁰}` ✓
- α = 1：`D(S Z) = λm. (Zᵐ(suc))(m) = λm. F_m(m) = F_ω` ✓（关键引理 `Zᵐ(suc) = F_m`）
- α = 2：`(S Z)ᵐ(suc) = F_{ω·m}`，故结果 `= λm. F_{ω·m}(m) = F_{ω²}`，用的正是标准基本列 `ω²[m] = ω·m`，**无偏移** ✓

## 2.3 lens 极限的候选定义【推导 → 机验】

```
F X       := Π(n:ℕ). F_n X
Z z s l   := λ n. Z_n z s l
S z s l u := λ n. S_n z s l (u n)
L z s l G := λ n. L_n z s l (λ k. G k n)
D z s l u := l (λ n. D_n z s l (u n))        ← 唯一用到 l 的分量
```

要形成 `Π(n:ℕ). F_n X`，须把 `F_n` 当作函数 `ℕ → Set → Set`，即需要大消去 / 宇宙。与论文摘要"外部的宇宙序列"一致。

## 2.4 大数配方【推导】

```
Θ₀ = ε₀ ,  Θ_{n+1} = φ_{Θ_n}(0) ,  N_n := F_{Θ_n}(9)
```

由 PROP 2，`Θ_n` 的 Church 项 = n 个 Veblen 型 lens 的复合；求值等于在高度为 n 的函数类型塔 `F^n(𝔽)` 上跑一遍。宇宙层数 = 函数类型塔高度 = φ 嵌套次数。

---

# 第三部分：探针（机器验证）

## 3.0 环境

- Ubuntu noble，`apt install agda agda-stdlib` → **Agda 2.6.3**
- 无 stdlib 依赖，无 agda/cubical library 依赖，仅用内建 `Agda.Builtin.*` / `Agda.Primitive`
- 复现：`LC_ALL=C.UTF-8 agda Probe3.agda`

| 文件 | 行数 | 状态 |
|---|---|---|
| `Probe.agda` | 213 | PASS |
| `Probe2.agda` | 109 | PASS |
| `Probe3.agda` | 196 | PASS（主文件） |
| `Probe4.agda` | 65 | PASS |
| `NoCubical.agda` | 193 | PASS |
| `Norm.agda` | 10 | PASS |
| `Bad.agda` | 36 | PASS |
| `Norm2.agda` | 10 | **FAIL（预期，见 3.5）** |

## 3.1 FGH 代数【机验】

```agda
Fn = Nat → Nat ;  zF = suc ;  sF g n = iter g n n ;  lF G n = G n n
F[ a ] = a Fn zF sF lF
```

| 断言 | 结果 |
|---|---|
| `F[ o0 ] ≡ suc` | refl |
| `F[ onat 1 ] 3 ≡ 6`，`F[ onat 1 ] 5 ≡ 10` | refl |
| `F[ onat 2 ] 3 ≡ 24`，`F[ onat 2 ] 2 ≡ 8` | refl |
| `F[ oomega ] 2 ≡ 8`，`F[ oomega ] 1 ≡ 2` | refl |
| `F[ onat 1 ] ≡ λ n → n + n` | 需 funExt（全开发中唯一一处） |

## 3.2 Gentzen lens【机验】

在 **Church 项层**即成立，无需下降到 FGH：

| 断言 | 结果 |
|---|---|
| `pow o0 ≡ onat 1`（ω⁰ = 1） | refl |
| `pow (onat 1) ≡ oomega`（ω¹ = ω） | refl |
| `app (comp gentzen gentzen) a ≡ pow (pow a)`，**a 为自由变量**（PROP 2） | refl |
| `app idLens a ≡ a` | refl |
| `app gentzen (olim f) ≡ olim (λ n → app gentzen (f n))`（正规性） | refl |

## 3.3 极限 lens 与导数算子【机验】

2.3 的候选定义正确：

`app (limLens (powLens gentzen)) o0 ≡ olim (λ n → app (powLens gentzen n) o0)` → **refl**
即 ε₀ 由极限 lens 定义相等地产出。

由此 `deriv t = limLens (powLens t)`（枚举 t 的不动点），`app (deriv gentzen) o0 ≡ ε₀` → refl。

## 3.4 `Lens` 类型上的 Ω-代数【机验】

```agda
veblenLens : Ord (lsuc ℓ) → Lens ℓ
veblenLens a = a (Lens _) gentzen deriv limLens
--                        ^零     ^后继  ^极限

Θ : Ord (lsuc ℓ) → Ord ℓ
Θ a = app (veblenLens a) o0            -- Θ a = φ_a(0)
```

| 断言 | 结果 |
|---|---|
| `Θ o0 ≡ onat 1`（φ₀(0) = 1） | refl |
| `Θ (onat 1) ≡ eps0`（φ₁(0) = ε₀） | refl |
| `Θ oomega ≡ olim (λ n → Θ (onat n))`（φ_ω(0) = Γ₀） | refl |

**宇宙代价由类型检查器强制。**负控制：把 `Θ` 声明为 `Ord ℓ → Ord ℓ`（同层），Agda 拒绝：

```
lsuc ℓ != lzero
when checking that the expression Lens _ has type Set ℓ
```

Hancock 阶梯已构造：`Θ₀ = eps0`，`Θ₁ = Θ Θ₀`，`Θ₂ = Θ Θ₁`，`Θ₃ = Θ Θ₂`，`Gamma0 = Θ oomega`；全部类型检查通过，全部可喂 FGH。

**构造可迭代**（`Probe4.agda`）：在 `Op ℓ = Lens ℓ → Lens ℓ` 上再装一个 Ω-代数（`zOp = deriv`，`sOp F t = limLens (λ n → iter F n t)`，`lOp`），得 `Θ2`；再在 `Op2 ℓ = Op ℓ → Op ℓ` 上装一层，得 `Θ3`。均类型检查通过，FGH 值在输入 1 处可求值。`Θ2 o0 ≡ eps0` 为 refl。

## 3.5 三项推翻前提的发现

### (a) cubical 不必要

`Probe3.agda` 换成 `--safe --without-K`、cubical Path 换成内建 `≡`、删去 funExt，**193 行原封不动通过**（`NoCubical.agda`）。

原因：整条链路每个等式都是定义等式。funExt 只用于把 `F[ onat 1 ]` 与独立写出的 `λ n → n + n` 认同。

对交接文档陷阱 3（定义等式 vs. path）的影响：该陷阱在下界方向不出现。

### (b) 极限 lens 不保持正规性

```
gentzen normal?   YES (refl)
limLens normal?   NO
```

`Norm2.agda` 的失配显示需要**交换两个嵌套极限**：`l (λn. l (λm. …))` vs `l (λk. l (λn. …))`。

即：`limLens` 的**定义**是对的（ε₀ 定义相等地产出），缺的是极限交换引理。

### (c) 定义等式对语法敏感

`powN`（Probe.agda）与 `powLens gentzen`（Probe2.agda）外延相同，但
`app (deriv gentzen) o0 ≡ eps0-byhand`（用 `powN` 写）**不是 refl**——`n` 是绑定变量，两个递归定义都不归约，符号不同即失败。
同一现象在 Probe4 中再次出现（`Θ2 (onat 1) ≡ Gamma0` 非 refl，尽管外延相等）。

## 3.6 求值极限

| 值 | 结果 |
|---|---|
| `FΘ₀ 1 ≡ 2`，`FΘ₀ 2 ≡ 8` | 求值通过 |
| `FΘ₁ 1 ≡ 2`，`FΘ₂ 1 ≡ 2`，`FΓ 1 ≡ 2` | 求值通过 |
| `F[Θ2 …] 1 ≡ 2`，`F[Θ3 …] 1 ≡ 2` | 求值通过 |
| `FΘ₁ 2`，`FΓ 2` | 120s / 100s 超时 |
| `FΓ 0 ≡ 0` | 求值通过（原断言写作 `≡ 1`，Agda 报 `0 != 1`，纠正为 0） |

## 3.7 负控制（确认测试非空）

| 假命题 | Agda |
|---|---|
| `F[ onat 2 ] 3 ≡ 25` | 拒绝 |
| `pow o0 ≡ onat 2` | 拒绝 |
| `F[ oomega ] 2 ≡ 9` | 拒绝 |
| `F[ eps0 ] 2 ≡ 9` | 拒绝 |
| 「每个 lens 都正规」 | 拒绝 |
| `Θ : Ord ℓ → Ord ℓ` | 拒绝 |
| `app (deriv gentzen) o0 ≡ eps0-byhand`（语法不同的序列） | 拒绝 |

## 3.8 退化基本列（`Bad.agda`）【机验】

以下均为合法 Brouwer 树，类型检查通过，求值停机：

```agda
bad1 = olim (λ n → o0)          -- lim(0,0,0,…)
_ : F[ bad1 ] 5   ≡ 6           -- 增长率 = F₀
_ : F[ bad1 ] 100 ≡ 101

bad2 = olim (λ n → onat 1)
_ : F[ bad2 ] 5 ≡ 10            -- 增长率 = F₁

bad3 = olim alt                 -- 在 onat 2 与 o0 之间交替（非单调）
_ : F[ bad3 ] 7 ≡ 8             -- 奇数输入掉回 F₀
```

---

# 第四部分：证明义务的重新划分

## 4.1 免费的

`F_α` 的良定义与停机。Brouwer 树是归纳类型，`l : (ℕ→X)→X` 保证每个极限点有 ℕ-索引下降，`F[α]` 是结构递归的实例化，在正规化的类型论中必然停机。**不需要 accessibility / well-founded 证明。**

## 4.2 不免费的

- **基本列的递增性与共尾性。**由 3.8：基本列的存在保证良基，但不保证递增或共尾。退化项无人阻拦。这对应 Hancock 讲义 §2.1–2.2 的 stature 问题（`t{0,0,0,…}` 是 0 还是 1）以及他经 Fam/Pow 往返定义的 ⊴ 关系（他自评"最终可能不完全令人满意"）。
- **忠实性。**「该封闭项指称 φ_{ε₀}(0) / ψ_{Ω₁}(Ω_{M+ω})」这一断言。本轮只验证了 `Θ o0`、`Θ (onat 1)`、`Θ oomega` 三个点。要证 `Θ a = φ_a(0)` 对任意 `a` 成立，需一个独立的 φ 定义作参照。
- 3.5(b) 的极限交换引理是 4.2 第一项的一个实例。

## 4.3 与传统路线的差异

Setzer 式良序证明顺带给出忠实性——记号系统外部定义、序关系显式。lens 路线把记号与序数合并为一个项，省掉良序证明，代价是"该项是哪个序数"不再有独立参照物。

---

# 第五部分：量级评估（本轮结论，非验证事实）

按两个轴分开。**A 轴**：写得出封闭项、`F[α]` 可算、停机。**B 轴**：有依据断言"它就是那个序数"（含 4.2 的两项义务）。

| | A 轴 | B 轴 |
|---|---|---|
| 已跑通 | Γ₀（3.4）；4 元 Veblen（Probe4） | ~ε₀（仅三个点的 refl） |
| 短期 | 小/大 Veblen | Γ₀ |
| 中期 | Bachmann–Howard | 大 Veblen |
| Mahlo 路线成立时 | ψ_{Ω₁}(Ω_{M+ω}) | BH 一带 |

依据与限制：

- A 轴短期到大 Veblen：Probe4 已验证构造可迭代，通用化为对 n 递归定义算子塔；维度从 ℕ-索引换为 Ord-索引的机制已在 `Ord (lsuc ℓ) → …` 中存在。
- A 轴超过大 Veblen 需要塌缩：即引入 Hancock 讲义 §1.2.2 的 `Ω₂ = μX. 1 + X + (ℕ→X) + (Ω→X)`，并找到把 Ω₂-代数结构压回 Ω-代数结构的 lens，其 `D` 分量产出 ℕ-索引基本列。**该构造是否存在：未验。**相关观察：Hancock 强调 `F` 不必是函子、`U` 不是 B-代数态射。
- Mahlo 另需 dependent lens（讲义 §4.2 整节 TODO，只留 `coalgebra` 一词）。Mahlo 宇宙的反射原理作用于族上的算子，与"lens 作用于类型"相比高一层。
- 纯宇宙原则、不用 W-类型能否达到 Bachmann–Howard：**Hancock 在讲义中作为公开挑战提出，至今未解。**
- 外部基准：KNFX (CPP 2020) 已在 Cubical Agda 中达到 Bachmann–Howard（Cantor 范式 / Brouwer 树 / 良基外延序三者等价），Brouwer 树自带基本列。相对 googology 前沿（Buchholz ψ、Ω_ω、BMS、Taranovsky C），大 Veblen 属中游。

---

# 第六部分：未决事项

**文献**
- CHS 1997 原文内容（链接有效，未转换）
- Hancock 论文正文，尤其 §4.3.2 / §4.3.3 / Appendix C.3 / C.6（PDF 文本层不可提取；容器网络白名单不含 `lfcs.inf.ed.ac.uk`，`x-deny-reason: host_not_allowed`；容器内 `pdftotext`、`tesseract` 可用但无文件可喂）
- Russell'08 Swansea 幻灯片（未定位）
- Setzer 1998 *Well-ordering proofs for MLTT*（未读）
- Setzer 2004 overview（未读）

**技术**
- Hancock 论文中 `lim t` 的真实定义，与 2.3 的候选是否一致
- dependent lens 的定义
- 从 Gentzen lens（α ↦ ω^α）到 Veblen lens（α ↦ φ_α(0)）这一步在论文中的写法；本轮以 `Lens` 上的 Ω-代数（3.4）独立得到，与论文的关系未知
- `Θ a = φ_a(0)` 对任意 `a` 的证明
- 极限交换引理（3.5b）
- "递增 lens"的定义：何种条件保证 lens 产出的项基本列递增且共尾
- 塌缩 lens 是否存在
- CHS 1997 实现关系使用的等式种类

**已降级但未消失**
- lens 能否直接作用于 Brouwer 树而非 Church 编码（3.1 显示 FGH 侧不需要外延化）
- IR × HIT × cubical 交互成熟度（3.5a 显示 cubical 非必需）

---

# 附：文件清单

`agda/` 目录：

| 文件 | 内容 |
|---|---|
| `Probe.agda` | cubical 版：FGH 代数、Gentzen lens、复合、极限 lens、ε₀、正负测试 |
| `Probe2.agda` | 导数算子、Veblen 阶梯、Γ₀、正规性 |
| `Probe3.agda` | **主文件**：宇宙多态、`Lens` 上的 Ω-代数、`Θ`、Hancock 阶梯、FGH 求值 |
| `Probe4.agda` | 构造的迭代：`Op` / `Op2` 上的 Ω-代数，`Θ2` / `Θ3` |
| `NoCubical.agda` | Probe3 的 `--safe --without-K` 版 |
| `Norm.agda` | Gentzen lens 正规性（PASS） |
| `Norm2.agda` | 极限 lens 正规性（**FAIL，预期**） |
| `Bad.agda` | 退化基本列的反例 |

复现：`apt install agda`（Ubuntu noble，2.6.3），`LC_ALL=C.UTF-8 agda <file>`。
`Norm2.agda` 预期失败。
