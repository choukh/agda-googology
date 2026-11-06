# 记号 EBO 的良基: 规模侦察

> 2026-11-04. 侦察报告, 附两个小实验 (`probes/OCF/Align/WfScoutTau.lagda.md`, `WfScoutPull.lagda.md`). 三档: **定理** (编译过), **测试** (有限样本), **判断** (纸面估计). 强度写 ψ₀(Ω_x).

## 结论

1. **路线只有一条现实的: 沿 τ 把归档 OT_I 的构造性良基拉回 EBO.** 归档的 OT_I (Setzer 1998) 在当前环境编译通过, 覆盖到 ψ₀(Ω_{I+ω}), 远高于 EBO = ψ₀(Λ). 它**没有结构基本列** (只有范数搜索), 所以它自己翻不出带标签的树; 有用的是它的 `Acc`.
2. **τ 那一侧比预想便宜, 已做了一半.** τ 严格保序对**全部** EBO 项成立, 不要标准形 (`τ-mono`, 定理, 约 60 行); 可数项落在 OT_I 端点之下 (`τ-bd`, 定理). 拉回本身是 10 行 (`Pull.go`, 定理). 剩下的 τ 义务只有一条: τ 保标准形 (`τ-NF`), 判断 400 到 800 行.
3. **成本集中在一处: EBO 标准形对基本列封闭** (Lean `OTFS_thm` 的 Agda 版). 判断 3000 到 7000 行, 有已构建的 Lean 蓝本 (MIT, `Classical.choice` 已机检可去). 这是整条路的主要风险.
4. **全路线新写约 4000 到 9000 行 (中位判断约 5000).** 做完得到: 每个可数 EBO 标准形都有带字面标签的树 (`Lab`), Ω-塔 `EBOψ k` 对一切 k 都有; 极限树的 FGH 逐点等于记号 ψ₀(Λ)[n] 的 FGH; 记号侧第 3 层 (良基) 完成, EBO 的大数在 Agda 里有良基证明. 条件定理已编译 (`Std.ebo-lab`, `Std.fgh-EBO`), 前提只剩封闭性两条与 `τ-NF`.
5. **它不替代第 4 层的值比较.** 它给的是参照树, 不是比较. 主线树与参照树互相 `⊑⁰` 的证明每站照样要写. 所以与 "每站 1200 到 2000 行" 不是二选一: 记号良基约等于 3 到 5 站的工作量, 换来的是 ψ₀(Ω_{Ω·ω²}) 以上**每一站都有参照树**. 现在那里没有参照树, 只能等树侧的值判据. **值不值得做取决于第 4 层要不要越过 ψ₀(Ω_{Ω·ω²})**: 要越过, 这是最可预期的办法 (数学已知, 有蓝本); 不越过, 不必做. 建议先做 `τ-NF` (有界, 风险小), 封闭性的移植由作者定.

## 1. 归档 OT_I 的良基证明

**位置.** `archive/src/Mahlo/Inacc/` (21 个文件) 与 `WO/` (22 个), 共 43 个 `.lagda.md`, 10501 行, 非空代码 7935 行 (其中序与句法事实 3360 行, `WO/` 的良序证明 3796 行).

**证的是什么** (读 `Theorem.lagda.md`, `WO/Main.lagda.md`, `Closure.lagda.md`, `Order.lagda.md`):

| 项 | 内容 |
|---|---|
| 项 | Setzer T′: `zer`, snoc 和 `_▹_`, `phi a b` (φ 是原语), `psi π b` (π 是 Ω′_a 或 I), `Om a`, `I` (`Syntax`) |
| 序 | `lt : Tm → Tm → Bool`, (≺′1)–(≺′11) 的燃料版; `_≺_` 是 `lt s t ≡ true` 的记录. 线性、传递在**全部** T′ 上已证 (`Linear`, `Trans`) |
| 标准形 | `isOT : Tm → Bool` (Def 2.9, 含 G 条件), `OT` 是记录 |
| `Acc` | `data Acc (y : Tm) : Set where acc : (∀ {z} → OT z → z ≺ y → Acc z) → Acc y` (`WO/Main` §5), 分支限于 OT |
| 主定理 | `wellfounded : ∀ n {y} → OT y → y ≺ endpt n → Acc y`, `endpt n = ψ_{Ω₁}(Ω_{I+n})`; 更一般的 `thm441`: 对任何在 Ω₁ 以下前进的谓词做超限归纳. 对 n 一致 (`Wi : ℕ → Pred (suc 0ℓ)`) |
| 方法 | Setzer 的 distinguished sets: 归纳族 `𝒲`, 对 `Set` 量化的并 `𝕎` (在 `Set₁`), Γ 迭代 (ℕ 到宇宙的大消去). 构造性, 无公设 |

**选项.** 43 个文件头都是 `{-# OPTIONS --safe --cubical-compatible #-}`. `--cubical-compatible` 蕴含 `--without-K`, probes 的库文件本身也加 `--cubical-compatible`, 所以可以从 probes 导入. **另要 `--hidden-argument-puns`** (`WO/Base.lagda.md:110` 用了 `{A}` 双关), 归档 README 没写. 归档没有 `.agda-lib`.

**本次编译** (定理档的前提核实): 把 `archive/src/Mahlo/Inacc` 拷到个人临时目录, 加一个只含 `depend: standard-library-2.4`, `flags: --hidden-argument-puns -W noUnsupportedIndexedMatch` 的库文件, `agda` 2.8.0.2 编译 `Theorem.lagda.md`, **退出码 0**, 共约 75 秒. 第一次没加 `--hidden-argument-puns`, 在 `WO/Base:110` 报错. 归档没有改动.

**覆盖多大.** OT_I 端点 ψ_{Ω₁}(Ω_{I+ω}), 按 EBOI 的约定即 ψ₀(Ω_{I+ω}). EBO = ψ₀(Λ), Λ = ψ_I(0) 是第一个 Ω-不动点 (EBOI §1 的约定与 Setzer 一致), Λ < I. 所以 EBO 只占 OT_I 的一小段: EBOI 里 ψ₀(Ω_{I+n}) 以下的项都在 OT_I 的良基范围内 (EBOI §11 的判断). 可数 EBO 项的 τ-像都在 `endpt 1` = ψ₀(Ω_{I+1}) 之下 (`τ-bd`, 定理).

**有没有基本列.** 没有结构基本列. `FGH.lagda.md` 用范数搜索 λ[n] = max{β ≺ λ : Nβ ≤ Nλ+n}, 只证了 λ[n] ≺ λ 与 λ[n] ∈ OT, 候选表完整性未证 (文件头自述). 不分零、后继、极限, 所以接不上 `AccTree` 的 `View`, 也与 EBO 的规则基本列不逐项一致. 所以判断 OT_I 自己翻不出带 `Lab` 的树 (没有编译过的否定, 只是没有可用的 `View`); 它对我们的用处是 `Acc`. 作者的记忆是对的: 更大的记号、有良基证明、不带 (结构) 基本列.

## 2. 从 OT_I 得到 EBO 的良基

### 2.1 要的陈述

`acc→nat` (AccTree §4) 说字面的 `E.Acc` 只在自然数上成立. 修正后的两个版本在 AccTreeLab 里归到同一件事:

- **可数标准形上 `_<ᵀ_` 良基** (`Class.AccP`): 量词限于类 `P`. 由 `wf→HC` 得 `HC` (遗传良基, 不碰 cΩ), 由 `wf→lab` 得标签.
- **基本列下降的良基** (`AccTree.Acc`, 关于 `_◁_`): `HC→Acc` 从 `HC` 给出. 可数项的 `pred`/`fsn` 后代仍可数 (`Ctbl-pred`, `Ctbl-fsn`), 不碰 cΩ 行, 所以在可数项上第一个版本推出第二个, 不需要另证. 不可数项的 `fgh-tree` 只走 ℕ-截断的哑值, 对标签无用, OT_I 也只给 Ω₁ 以下的 `Acc`, 不做.

所以目标就是: 找一个类 `P` (可数, 对 `pred`/`fsn` 封闭), 证 `P` 上 `AccP`.

### 2.2 τ 路线: 现状

τ 取手册 §3 的映射: $\tau(\mathbf 1)=\varphi'_00$, $\tau(\psi_u0)=\Omega'_{\tau u}$, $\tau(\psi_ua)=\psi_{\Omega'_{\tau u+1}}(\tau a)$ ($a\ne0$), 和逐项.

| # | 义务 (手册 §6.1) | 状态 | 档 | 依据 |
|---|---|---|---|---|
| 1 | EBO 标准形谓词 | 有: `EBOI.isOTᵉ` (Bool, bot 原版) | 定理 (已有) | `EBOI.lagda.md:1052` |
| 2 | τ 严格保序 | **已证, 对全部项, 无标准形前提** | 定理 | `WfScoutTau.τ-mono` |
| 3 | τ 保标准形: `isOTᵉ t ≡ true → OT (τ t)` | 未做 | 测试 (1489 与 14665 个原始项上 `isNF = isOT ∘ τ`, EBOI §10); 本次 `isOT (τ (EBOψ 3))` | `WfScoutTau` §3 |
| 4 | 标准形对 `pred`, `fsn` 封闭 | 未做, 有 Lean 蓝本 | 无 | 见 §2.3 |
| 5 | 可数项在端点之下 | **已证** (`τ≺I`: 一切 τ-像 ≺ I; `τ-bd`: 可数项 ≺ `endpt 1`) | 定理 | `WfScoutTau.τ-bd` |
| — | 拉回 | **已证** (`Pull.go`, `wf`, `hc`, `lab`, `fgh`) | 定理 | `WfScoutPull` §1 |
| — | Ω-塔是标准形 | **已证**, 对一切 k (`nf-tower`) | 定理 | `WfScoutPull` §2 |
| — | 组装 | **条件定理** `Std.ebo-lab : ∀ k → Lab (…) (EBOψ k)`, `Std.fgh-EBO`, 前提 `cl-pred`, `cl-fsn`, `τ-NF` | 定理 (带前提) | `WfScoutPull` §2 |

**义务 2 为什么不要标准形.** 手册预计 "几十行字典序论证", 实际约 60 行. 原因: Setzer 的 (≺′5)–(≺′11) 在 τ 的像上就是 "先比层再比参数" 的字典序, 用到的只是归档已在全部 T′ 上证明的线性、传递与 `Lex` 的 $x<y\Rightarrow x+1\le y$ (`+1-least′`). 这与 Lean 的 `val_lt_val` (语义, 要标准形) 不同. 代价转移到了义务 3: OT_I 的 `Acc` 只给 OT 中的元素, 所以拉回必须知道 τ-像在 OT 里; Lean 不需要这一条, 因为 mathlib 的序数序在全体上良基.

**义务 3 的形状 (判断, 400 到 800 行).** 对 `isOTᵉ` 的各合取项逐一对应 Setzer 的 (OT2)–(OT5):

- 和的降序: `descᵉ` 的 `leᵇ (cmpᴾ y x)` 经 `τ-mono` 与 `cmpᵀ` 的正确性 (probes `Closure` 的 `lt→<ᴾ`, `eq→≡ᴾ`) 变成 `le ⟨τP y⟩ ⟨τP x⟩`.
- $\Omega'_{\tau u}$, $\Omega'_{\tau u+1}$ 的侧条件 (非零, 非不动点, `Suc′`): τ 的像没有 I 与 $\psi_I$, 逐形状 `refl`.
- G 条件: Setzer 的 (G4) 与 EBO 的 `Gᵉᴾ` 同形 (都穿进下标, 门槛 $X\le w$ 经 τ 保序且反射), 需要 "G 沿 `fromL` 拆成分量", "`allLt` 对 `++` 拆开" 两个小引理. **唯一不同在 (G5):** Setzer 的 $G_\pi(\Omega'_c)=G_\pi(c)$ 无条件, EBO 在 $w<X$ 时直接给真. 要补一条引理: 标准形 $w<X$ 时 $G_{\Omega'_{\tau X+1}}(\tau w)=\emptyset$. 纸面论证: 标准形的每个分量 $c$ 满足 $[c]\le w$, 首项下标严格小于项本身 (句法上对全部项成立), 所以 $w$ 里沿 Ω-链可见的 ψ 层都 $<X$, 不被收集. 这一步要标准形 (降序), 是义务 3 里唯一要想的地方.

### 2.3 义务 4: 封闭性

`Std` 的前提 `cl-fsn` 只要 ℕ-下标 (可数项的 `fsn`), 但证明绕不开 Ω-基本列: 规则 6 的输出是 $\psi_u(b[\gamma_n])$, $\gamma$-链经 `fsT`. Lean 的 `OTFS_thm` 正是对一般项下标 `fs X Y` 同时归纳. 所以要的就是全 EBO 的 Buchholz 3.3 (判断: 我没找到只对 ℕ-下标做归纳的证明组织).

| 部分 | Lean (`6da2de5`, 行) | 我方已有 | 要写 |
|---|---|---|---|
| 项、序、全序 | `Basic` 118, `Order` 159 | `T`, `cmpᵀ`, `<ᵀ-trans`, 不可反 (probes `Closure`, `Bachmann`) | 少量 |
| 标准形 | `Std` 66 | `isOTᵉ` (Bool 形); Lean 是列表形 `G`. 要统一 (手册 §5.2 注记 (c)) | 100–300 |
| 和的约化 | `Sum` 304 | 无 | 300–600 |
| 基本列 | `FS` 1204 | `fsn`, `fsT`, `γT` 与递减证书都有, 定义形状不同 (结构递归 + `Below`, Lean 是良基递归 + `tower`) | 转移或重证 300–1000 |
| Buchholz 3.4–3.6, `Trian`, `SubBound`, `bachmann`, `OTFS_aux` | `Closure` 1833 | 无. 片段版有 `Standard` (785 行代码, 可数下标, 到 ψ₀(Ω_Ω)) 与 `StandardOmega` (943 行, 下标 Ω+可数), 用的是关系式 `Vis`/`Bnd` 与绝对的自界引理; 手册 §5.2 陷阱 1 说绝对不变量在项下标上为假, 所以片段的证明不能推广, 要换成 Lean 的相对不变量 `Trian` | 2500–5000 |

合计判断 3000 到 7000 行. 依据: Lean 3000 行左右的密集证明 (`Closure` 里 148 处 `omega`/`simp`), Agda 无这些自动化, 按 1.5 到 3 倍估; 对照归档 58 条 "easy but tedious" 的句法事实写了约 3360 行代码. **这是估计, 不可靠的部分是倍数.** 经典公理不是障碍: `OTFS_thm` 的 `Classical.choice` 已机检可去, `propext`, `Quot.sound` 可去是推断 (手册 §5.2).

### 2.4 另两条路 (判断: 都更贵, 不是否定)

- **把 Setzer 的证明直接搬到 EBO.** OT_I 的良序证明 3796 行代码, 加 3360 行句法事实. EBO 去掉 φ 与 I 会小一些, 但仍要重写 distinguished sets 一整套, 且 EBO 的标准形封闭性一样要证 (证明里要用). 没有理由优于 τ.
- **$W_u$ (Buchholz 1987, pss-proof `OT_B_wellFounded`).** 只到 ψ₀(Ω_ω), ℕ-下标; EBO 的下标是项, 对 `Acc u` 递归定义 $W_u$ 的版本无人写过 (手册 §6.1 末). 它的好处是直接给基本列下降的良基, 形状同树; 代价未知, 风险高于 τ.

## 3. 文献

先看手册已有的条目; 本次没有重新调研, 只读了归档 `Sources/README.md`.

| 证明 | 系统 | 方法 | 档 | 能否 `--safe --without-K` |
|---|---|---|---|---|
| Buchholz 1986, APAL 32 | ψ_ν, ν ≤ ω | 集合论的序数解释, 经典 | 同行评审; 本次未重读 | 原样不能 (要序数) |
| Buchholz 1987, APAL 33 | 同上, $D_\omega$-free 部分 | distinguished sets $W_u$, 句法 `Acc` | 同行评审; pss-proof 的 Lean 版机检·只读 | 推断能 (归纳族); pss-proof 的 39 处经典写法未核; 不覆盖项下标 |
| 扩展 Buchholz (EBO) | Ω 下标为项, 到 ψ₀(Λ) | 社区定义, 无同行评审的良基证明; Lean `OTLt_wf` | 机检·已构建, 经典 | 原样不能, 见下 |
| **Setzer 1998, APAL 92** | **OT_I, 到 ψ₀(Ω_{I+ω})** | **distinguished sets, 在 ML₁W 里构造** | **同行评审; 我方已机检 (归档)** | **能, 已做** (`--cubical-compatible`) |
| Setzer 2000, *Ordinal systems part 2* | I-序数系统 | 两种: 超限序列 (要经典), distinguished sets (构造) | 同行评审; 本地 PDF, 读图 | 后者推断能 |
| Rathjen 1994, AML 33 | KPM, $T(M)$ | KPM 内的良序证明 | 未读 (付费) | 不明 |
| Buchholz 1990 草稿 *Wellordering proofs for systems of fundamental sequences* | 带基本列的系统 | 不明; 按题目, 正是 "基本列下降的良基" | 未取得 | 不明 |
| みずどら | I 层 | 封闭、递减、序同构, 良基经同构 | 人工证明(社区) | 语义, 不能原样 |

**Lean `OTLt_wf` 的经典部分在哪.** `Mono.lean:139`: `OTLt_wf : WellFounded OTLt := valHom.wf Ordinal.lt_wf`. `valHom` 的映射是 `Term.val`, 值在 mathlib 的 `Ordinal`, Ω 由基数给出, ψ 由闭包集合的下确界给出 (`Ord`, `Eval`), 保序是 `val_lt_val` (`Mono.lean:121`, 要标准形). 经典的是整个语义模型 (`Ordinal`, `Classical.choose`), 不是证明里的几步. **换掉的办法就是本报告的路线:** 把目标从 `Ordinal` 换成 OT_I. `valHom` 对应 `τ-mono` (已证, 且不要标准形), `Ordinal.lt_wf` 对应 `Acc-endpt` (已证, 归档), 多出的代价是 `τ-NF`, 因为 OT_I 的 `Acc` 只给 OT 的元素.

## 4. 有了良基之后, 到参照树

**链条** (都是定理, 除了标明的前提): `Std` 的三个前提 → `Pull.wf` (`AccP`) → `wf→HC` → `labᴴ` 给 `Lab (treeᴴ h) t` → `Lab≅tree` (AccTreeLab): 同一个项的带标签树都 `≅`, 所以这棵翻译树与现在任何带 `Lab` 的参照树可以互换 → `fgh-tree`: FGH 逐点等于记号的 FGH.

**范围.** 一切满足 `isOTᵉ t ≡ true` 与 `Ctbl t` 的项, 即 EBO 里一切可数标准形, 全在 ψ₀(Λ) 以下. 具体站点只要把站点的项写出来, `isOTᵉ` 用 `refl` 算, `Ctbl` 是一层构造子. 极限: `EBO-tree = lim (k ↦ 翻译树 (EBOψ k))`, 各分支带标签, FGH 在 n 处就是 $f_{\psi_0(\Omega\text{-塔}_n)}(n)$ (`fgh-EBO`); 按 EBOI 的 `ψ₀Λ-tower` 这正是 ψ₀(Λ)[n]. ψ₀(Λ) 本身不是 EBO 的项, 所以 `EBO-tree` 没有 `Lab`, 只有分支的标签 (判断: 若要, 可在 EBOI 上定义 `Lab`, 未做).

**ψ₀(Λ) 以上.** OT_I 的良基到 ψ₀(Ω_{I+ω}), EBOI 的 τ 也已写好 (`SetzerTest.agda` 的 `τP` 含 $\psi_I$, $I$). 但 EBOI 的新规则只有测试, 其封闭性连 Lean 蓝本都没有, `Lab` 也只对 EBO 的项定义. 判断: 不在这次的范围内.

**还缺什么才能当第 4 层的参照树.**

1. 三个前提 (`τ-NF`, `cl-pred`, `cl-fsn`). 这是本报告估计的成本.
2. **每站的比较本身不变.** 第 4 层是主线树与参照树互相 `⊑⁰`/`≼`. 翻译树只提供 "参照物存在". 主线是差树, 已知与记号不逐项一致 (`no-PxB-M₂` 等), 所以比较要走值的工具 (`V-≃`, `Ψ-emb` 一类). 现有比较工具是对树侧参照族 (`LadderOrd`, `CrossM`, `EmbVV`) 的形状写的; 只用到 "参照树有 `Lab`" 的论证可以直接换成翻译树, 用到参照族具体形状 (如高度 `HtB`) 的不能自动换. 哪些属于前者, 本次没有逐个查 (判断).
3. 树的类型: 翻译树在 `OCF.Align.Level` 的 `Ordᶜ zero`, 主线在 `OCF.Free.Level`, 有 `Bridge.⟦_⟧` (AccTree 文首第 2 点). 不是障碍.

纲领上没有问题: 翻译树读记号, 只在验收文件里用, 是 "验收的参照物, 不是定义的前提" (AGENTS 当前最佳实践). 它不让树更自足.

## 5. 综合估计

| 档 | 内容 | 新写行数 | 依据 |
|---|---|---|---|
| 已有可复用 | OT_I 良基与句法事实 | 0 (现成 7935 行代码) | 归档, 本次编译通过 |
| 已有可复用 | `AccTree`, `AccTreeLab` (`Class`, `wf→lab`), `EBO`, `EBOI.isOTᵉ`, `Standard` 的 `Ctbl` 引理 | 0 | 已编译模块 |
| 本次已做 | τ, `τ-mono`, `τ≺I`, `τ-bd`, 拉回, `nf-tower`, 条件组装 | 约 200 (代码 136 + 66) | `WfScoutTau`, `WfScoutPull` |
| 新证明 | `τ-NF` (义务 3) | 400–800 | §2.2 的形状; 判断 |
| 新证明 | `cl-pred` | < 100 | `pred` 只剥末尾的 1; 判断 |
| 机械移植 (大) | `cl-fsn`: Lean `OTFS_thm` 一路, 含与我方 `fsn`/`fsT`/`γT` 的转移 | 3000–7000 | §2.3; 倍数不可靠 |
| 合计 | | 约 4000–9000, 中位约 5000 | |

**风险.**

1. **封闭性移植 (主要).** Lean 证明建立在 `fs X Y` (良基递归, `tower`) 与列表 `G` 上, 我方是结构递归的 `fsn`/`fsT`/`γT` 与 Bool 的 `Gᵉ`. 两个选择: 在 Agda 里照 Lean 的形状重建再证转移 (测试 26 万对一致, 转移定理未写), 或在我方定义上重证. 两个陷阱 (界相对于 $c$; `bach_pre` 要带前缀) 已知. Agda 侧还有归档记下的工程坑 (`with` 爆炸, 重建项后终止检查失败).
2. **`τ-NF` 的 (G5) 引理**要用标准形的降序; 纸面论证在 §2.2, 没编译.
3. **导入归档的方式.** 归档只读且没有 `.agda-lib`, 本次是拷到临时目录加库文件编译的. 正式做时三个选项: 每次用拷贝; 把 43 个文件作为新模块复制进 probes (约 1 万行重复); 或作者另定. 不改归档的前提下, 只有第二种能用标准编译命令.

**与第 4 层值比较 (每站 1200 到 2000 行, 不可靠) 相比.** 不是替代关系 (§4 第 2 条). 按行数, 记号良基约等于 3 到 5 站. 它买到的是: ψ₀(Ω_{Ω·ω²}) 以上每站都有带字面标签的参照树 (现在没有, README 主线第 2 条说 "再往上要树侧的值判据"); 记号侧第 3 层完成 (`¬EBO-number` 说的字面前提是假的, 这里换成真的前提); EBO 的大数有 Agda 里的良基证明. 判断: 若第 4 层只做到 Ω·ω², 不值得; 若要越过, 这是比等待树侧值判据更可预期的一条, 因为数学已知、有机检蓝本. 不确定的是封闭性的实际行数, 可能落在估计的上端.

**建议的次序** (判断, 作者定): 先做 `τ-NF` (有界, 做完后 τ 一侧全部是定理, 前提只剩封闭性); 封闭性按 Lean 的次序分段 (先 `bachmann` 的 G 界, 它不依赖 `OTFS`; 再 `Trian`; 最后 `OTFS_aux`), 每段单独可编译, 随时可停.

## 实验

**编译.** 归档拷贝 (个人临时目录 `wfscout/arch`, 加库文件 `depend: standard-library-2.4`, `flags: --hidden-argument-puns -W noUnsupportedIndexedMatch`), 然后在仓库根:

```sh
agda --library-file=<库文件> -i src -i probes -i <拷贝>/arch probes/OCF/Align/WfScoutPull.lagda.md
```

两个文件都 `--safe --without-K --lossy-unification` (probes 库文件另加 `--cubical-compatible`), 无公设、无洞、无停机或正性编译指示, 无 `trustMe`; 退出码 0 (`WfScoutTau` 与 `WfScoutPull` 各一次, 不经管道).

**测试** (有限, `WfScoutTau` §3, `refl`): `isOTᵉ (EBOψ 3)`, `isOT (τ (EBOψ 3))`, `τ (EBOψ 2) ≺ τ (EBOψ 3)`, `τ (EBOψ 3) ≺ endpt 1`.

## 文件表

| 文件 | 内容 | 状态 |
|---|---|---|
| `probes/OCF/Align/WfScoutTau.lagda.md` | τ; `τ-mono` (全部项); `τ≺I`; `τ-bd`; 四个 `refl` 测试 | 新建, 编译过 |
| `probes/OCF/Align/WfScoutPull.lagda.md` | 拉回 `Pull` (`wf`, `hc`, `lab`, `fgh`); `nf-tower`; 条件组装 `Std` (`ebo-lab`, `EBO-tree`, `fgh-EBO`) | 新建, 编译过 |
| `probes/Survey/NotationWF.md` | 本报告 | 新建 |
| `archive/src/Mahlo/Inacc/Theorem.lagda.md`, `WO/Main.lagda.md` | OT_I 的 `wellfounded`, `Acc`, `endpt` | 只读, 拷贝编译通过 |
| `archive/src/Mahlo/Inacc/FGH.lagda.md` | OT_I 的范数基本列 (无结构基本列) | 只读 |
| `probes/OCF/Align/AccTree.lagda.md`, `AccTreeLab.lagda.md` | `fgh-tree`, `acc→nat`, `Class`, `wf→lab`, `Lab≅tree` | 只读, 被导入 |
| `probes/OCF/Align/EBOI.lagda.md` | `isOTᵉ`; §10 的 τ 测试 | 只读, 被导入 |
| `probes/OCF/Align/Standard.lagda.md` | `Ctbl`, `Ctbl-pred`, `Ctbl-fsn`, `Ctbl-cof` | 只读, 被导入 |
| `probes/Survey/scripts/eboi/SetzerTest.agda` | τ 的原始写法 (含 $\psi_I$) | 只读 |
| Lean `ExBuchholz` `Mono.lean:121,139`, `Closure.lean` | `val_lt_val`, `OTLt_wf`, `OTFS_thm` | 只读 (已有的构建副本) |
