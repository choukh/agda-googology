# EboLean: EBO-tree 的精简重写, 记号侧第 1–3 层的行数标杆

> **记号侧验收工作.** 读记号 (EBO 的项、序、基本列与标准形; Setzer 1998 的记号 OT_I 及其良基证明), 给的是验收用的参照树, 不是最终定义, 不进成品, 不让树更自足.
>
> **任务** (作者 2026-11-05): 参考现有代码重写 EBO-tree, 去掉不需要的依赖和死代码, 抽象掉重复, 得到没有水分的行数, 作为树侧的标杆: 树侧 3 层内必须小于它. 标签另列一行, 不算第 3 层.
>
> **判决.**
>
> 1. **编译过的定理, 无前提**: `EBO-tree′ : Ord` 与 `fgh-EBO′ : ∀ n → FGH EBO-tree′ n ≡ fgh (EBOψ n) (hc-tower n) n` (极限树的 FGH 在 $n$ 处等于记号沿基本列的 FGH $f_{\psi_0(\Omega\text{-塔}_n)}(n)$). 第 3 层不经标签: 树直接由 `HC` 推导造出. 另有 `lab-NF′` (一切可数标准形有带标签的树) 与 `ebo-lab′`, 作 "+ 标签" 一行. 与旧版的关系也是定理: `EboLeanCmp.fgh≡ : FGH EBO-tree′ n ≡ FGH WfFsn.EBO-tree n` (经 `tree≅`).
> 2. **行数 (定义级切片, 同 `locslice_four.py` 口径):** 第 1 层 **120**, 第 2 层 **131**, 第 3 层 **6524**, + 标签 **6544**. 旧版同口径 **197 / 210 / 7867 / 7941**. 注意旧版先前报的总数 6473 **少算了约 1470 行**: 切片看不见模块应用 `import WO.Main facts`, 归档的 58 条句法事实的证明 (Facts1/2/2b/3) 没有计入. 本文两边都补上了.
> 3. **标杆的读法 (判断).** 6524 是**这条路线** (沿 τ 拉回 Setzer 的突出集) 删干净之后的数, 其中约 5250 行是 Setzer 的 OT_I 机器, 那里仍带着 EBO 用不到的一般性 (二元 Veblen φ、不可达 I、$\psi_I$ 相关的引理与记录字段): 它们分布在被用到的定义内部, 切片删不掉, 要删就得重写 Setzer 的语法. 所以 6524 是**上界**, 不是记号侧的最小值. 对 EBO 专门重写突出集论证 (没有 φ 与 I) 的成本与结果行数没有做, 判断见 §4.
>
> 全部 `--safe`, 无公设、无洞、无停机或正性编译指示, 无 `trustMe`. 本文与 `EboLean*` 各段 `--safe --without-K --lossy-unification`; Setzer 的拷贝 (`EboLean/OT/`) 保留归档原样的 `--safe --cubical-compatible` (蕴含 `--without-K`), 原因见 §5.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLean where

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import OCF.Align.EboLeanDef using (T; EBOψ; HC; fgh)
open import OCF.Align.EboLeanBase using (NF; Ctbl)
open import OCF.Align.EboLeanTau using (AccNF; wfNF′)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF)
open import OCF.Align.EboLeanTree using (Ord; FGH; tree; hc; hc-tower; EBO-tree′; fgh-EBO′) public
open import OCF.Align.EboLeanLab using (Labᴸ; lab-NF′; ebo-lab′) public
```

## §1 定理表

```agda
-- 第 3 层: 可数标准形良基
_ : ∀ {t} → NF t → Ctbl t → AccNF t
_ = wfNF′

-- 第 3 层: 每个可数标准形的基本列遗传良基且可数
_ : ∀ {t} → NF t → Ctbl t → HC t
_ = hc

-- 第 3 层: 极限树, FGH 逐点等于记号的 FGH
_ : ∀ n → FGH EBO-tree′ n ≡ fgh (EBOψ n) (hc-tower n) n
_ = fgh-EBO′

-- + 标签
_ : ∀ {t} (nt : NF t) (ct : Ctbl t) → Labᴸ (tree (hc nt ct)) t
_ = lab-NF′
```

| 名字 | 陈述 | 档 | 文件 |
|---|---|---|---|
| `fsn`, `HC`, `fgh` | 裸值 ω-基本列; 沿基本列的遗传良基; 沿 `HC` 的 FGH | 定义 (第 1, 2 层) | [EboLeanDef](EboLeanDef.lagda.md) |
| `cl-fsn-NF`, `trian-fsn` | 标准形对 ω-基本列封闭 (Buchholz 3.3); $t[n]\lhd_0t$ 含 $t[n]<t$ (3.6) | 定理 | [EboLeanClosure](EboLeanClosure.lagda.md) |
| `Ctbl-fsn`, `Ctbl-cof` | 可数项对 `fsn` 封闭, 不是 Ω-共尾 | 定理 | 同上 |
| `τ-mono`, `τ-NF` | τ 严格保序 (一切项); τ 保标准形 (对 `NF`) | 定理 | [EboLeanTau](EboLeanTau.lagda.md) |
| `𝕎τ` | 一切 EBO 标准形的 τ-像属于 Setzer 的 $\mathbb W$ | 定理 | 同上 |
| `wfNF′` | 可数标准形上 $<^\mathsf T$ 良基 | 定理 | 同上 |
| `hc`, `EBO-tree′`, `fgh-EBO′` | 可数标准形有 `HC`; 极限树; FGH 逐点相等 | 定理 | [EboLeanTree](EboLeanTree.lagda.md) |
| `lab-NF′`, `ebo-lab′` | 带标签的树 | 定理 (+ 标签行) | [EboLeanLab](EboLeanLab.lagda.md) |
| `fsn≡`, `tree≅`, `fgh≡` | 与 EBO 的 `fsn`、与 `WfFsn.EBO-tree` 逐点相同 | 定理 (不计行数) | [EboLeanCmp](EboLeanCmp.lagda.md) |
| `fsn (EBOψ 1) 2` 的值 | `refl` | 测试 | EboLeanTree §4 |

## §2 路线与改动

**路线不变: 沿 τ 拉回 Setzer 的突出集** (NotationWF 的路线 (i)), 但不经 Setzer 的 Theorem 4.41.

旧链: OT_I 的 `Acc-endpt 1` (端点 $\psi_{\Omega_1}(\Omega_{I+1})$ 以下可达) 要突出类 $W_i$ (`WO/Main`) 与 I 层的 Γ-迭代 (`WO/Gamma`, `Gamma2`, 证 $\mathbb W\cap I\cong W(\mathbb W)\cap I$). 新链 ([EboLeanTau](EboLeanTau.lagda.md) §3–§4): τ 的像只用 $0,1,+,\Omega,\psi_{\Omega_{c+1}}$, 没有 $I$, $\psi_I$; 对 EBO 标准形结构归纳证 $\tau t\in\mathbb W$, 只用 $\mathbb W$ 对这几个构造封闭 (Lemma 4.29, 4.31 (a)); 再用 Lemma 4.21 (c) 在 $\mathbb W\cap\Omega_1$ 上归纳得可达. 这一步就是本次的数学改动, 约 40 行.

**删去的, 及为什么不需要.**

| 删去的 | 旧版行数 (切片) | 为什么不需要 |
|---|---|---|
| `WO/Main` (突出类 $W_i$, Theorem 4.41), `WO/Gamma`, `WO/Gamma2` (Γ-迭代) | 208 + 238 + 25 | 只为越过 I 与 $\psi_I$; τ 的像没有它们 (上一段) |
| Lemma 4.31 (b) ($\psi_I0$, $\psi_I(x+1)\in\mathbb W$), 14 个 `OTFacts` 字段及其证明 (Fi-form, Ωⁿ-bound 等, Facts2b 233 → 36) | 约 350 | 只被上一行用到, 或原本无人用 |
| 归档各文件里没人用的定义 (`Arith` 的 `·`, `Syntax` 的 `N`, `Order` 的燃料例子, 测试等) | 不计 (切片本来不数) | 物理删去 (§3 末), 编译核对 |
| `EBO` 的带证书基本列 `Below`, `fsT↓`, `γ↓`, `fsn↓`, `rep↓` 与对齐引理 `fsT↓-trm` 等; 沿全体项 `Acc` 的 `FGH` | 第 1 层 197 → 120 | 递减性在第 3 层由封闭性证明的 `Trian.t<` 顺带给出; 全体项上的 `Acc` 只在自然数上成立 (AccTree `acc→nat`), FGH 改沿 `HC` 递归 |
| bot 的 Bool 标准形 `isOTᵉ` (`EBOI`) 及与 `NF` 的互转 | 约 90 | 直接以归纳的 `NF` 为标准形; τ-NF 对 `NF` 重写 |
| `AccTree` (通用 `Notation`, 反射取名), `AccTreeLab` 的 `HC→Acc`, `Class`, `Level` 的 `Ordᶜ` 与 `FGH` | 47 + 48 + 59 | 树直接由 `HC` 造 (`tree`), FGH 在三构造子树上 5 行 |
| `WfScoutPull` 的 `Pull`/`Std`, `WfTauNF` 的 `StdFsn` 层层参数化 | 42 (+ `StdFsn` 若干行) | 一次实例化, 不要条件定理 |
| `Standard` 沿另一套视图的 `Ctbl-fsn`, `Ctbl-cof`; `Closure`, `Bachmann` 里散的序引理 | 50 + 52 + 49 | 沿 `VΩ`/`Vω` 视图重证 (10 行); 序引理收进 `EboLeanBase` §1 |
| `τ-bd` 与端点 `endpt` | 约 20 | 可数项 $<\Omega_1$ 是 EBO 一侧的句法事实, τ 保序送到 Setzer 的 $\Omega_1$ |

**原样保留的** (只换导入): 封闭性证明 `WfFsnBase/View/Trian/Omega/Bach/Closure` (Buchholz 3.3–3.6, Bachmann 性质; 约 800 行), τ 与 `τ-mono`, Setzer 的突出集与句法事实 (已删去上面几项).

## §3 四层行数表

切片脚本 `probes/Survey/scripts/htfeed/locslice_ebolean.py` (口径同 `locslice_four.py`: 从根出发做定义级切片, 数到达块的非空非注释 agda 行; 导入行不数). 补了切片的两处盲区, 两边都按补后的口径: 模块应用看不见 `facts` 的实现 (把 `FactsImpl.facts` 列为根); 带参数的模块别名看不见其参数 (`Lemma423.Ex̃`, `Lemma423c.E⁺`, 删死代码后编译报缺才发现, 列为根).

| 层 | 根 | 精简版 | 旧版 (同口径) |
|---|---|---|---|
| 1 定义 | `T`, `PT`, `_<ᵀ_`, `cmpᵀ`, `fsn`, `pred`, `EBOψ` | **120** | 197 |
| 2 + FGH | `HC`, `fgh` (旧: `Acc`, `FGH`) | **131** | 210 |
| 3 + 良基、封闭、树与 `fgh-EBO′` | `wfNF′`, `facts`, `cl-fsn-NF`, `hc`, `EBO-tree′`, `fgh-EBO′` | **6524** | 7867 (旧报 6399, 缺 facts) |
| + 标签 | `lab-NF′`, `ebo-lab′` | **6544** (+20) | 7941 (+74; 旧报 6473) |

第 3 层分组 (切片行数):

| 组 | 行数 |
|---|---|
| EBO 定义 (`EBO` 里用到的块 125, `EboLeanDef` 31) | 156 |
| Setzer 句法与序 (`OT/` 的 Syntax, Order, OrderProps, Unfold, Linear, Trans, Lex, Subterm, Arith, Closure, BoolLemmas, OTLemmas) | 1990 |
| Setzer 句法事实 44 条 (Facts1 300, Facts2 305, Facts2b 36, Facts3 218, FactsImpl 47, WO.Facts 54) | 960 |
| Setzer 突出集 (`OT/WO/` 其余 17 个) | 2300 |
| τ 与拉回 (`EboLeanTau`) | 246 |
| 封闭性 (`EboLeanBase` 241, `View` 163, `Trian` 197, `Omega` 58, `Bach` 100, `Closure` 61) | 820 |
| 树与 FGH (`EboLeanTree`) | 52 |

逐模块 (第 3 层, 切片行数, 降序): Trans 560, OrderProps 317, Facts2 305, Facts1 300, WO.Closed2 265, Linear 251, EboLeanTau 246, WO.Lemma417b 241, EboLeanBase 241, Facts3 218, WO.Closed 212, WO.Lemma417c 208, Subterm 202, EboLeanTrian 197, Lex 182, EboLeanView 163, WO.Lemma423 138, WO.Lemma47 132, EBO 125, WO.Lemma430 122, WO.Lemma431 122, WO.OrderLemmas 120, Syntax 119, WO.Union 115, WO.Lemma47ef 112, WO.Lemma423c 110, Unfold 109, WO.Dist 108, EboLeanBach 100, WO.CLemmas 99, WO.K 69, WO.Base 68, Order 62, EboLeanClosure 61, BoolLemmas 61, EboLeanOmega 58, WO.Facts 54, EboLeanTree 52, Arith 52, FactsImpl 47, Closure 39, WO.Lemma413 37, Facts2b 36, OTLemmas 36, EboLeanDef 31, WO.CTilde 22.

**死代码已物理删去.** `EboLean/OT/` 与 `EboLean*` 里切片到不了的定义都删了 (670 行), 删后从头编译通过. 物理行数 (agda 块的非空非注释行, 含导入): `EboLean*` 十个文件 1315, `EboLean/OT/` 36 个文件 5969; 比切片多出的主要是导入行.

## §4 没能缩下去的, 和为什么 (判断档, 除标明者)

1. **Setzer 机器里的 φ 与 I (主要的水分, 约 1400 行).** OT_I 的语法有二元 Veblen φ、不可达 I 与 $\psi_I$, 记录 `WDC`/`WUC`/`DC`/`UC` 与突出集引理对它们逐形状处理. 这些分支长在**被用到的**定义里 (切片按定义计, 不按分支计), 所以删不掉. 粗计 (有限计数, 不是定理): `OT/` 的 5244 行切片代码里有 1444 行字面提到 φ, I, Fi′, tilde 或 $\tilde C$ (其中 tilde 对 Ω 也要用, 不全是水分). 去掉它们要对 EBO 重写 Setzer 的语法与 58 条事实, 即 NotationWF 的路线 (ii) (直接对 EBO 做突出集). 判断: 那样 Setzer 一侧约 2500–3500 行, 第 3 层约 3500–4800, 但没有做, 风险在 $\mathbb W$ 对 Ω 封闭 (Lemma 4.30/4.31) 的特化, 倍数不可靠.
2. **Setzer 的序论按燃料与布尔写** (`OrderProps` 317, `Unfold`, `Linear` 251, `Trans` 560): 字典序的全序与传递在 EBO 一侧只要约 60 行 (`EboLeanBase` §1). 两套序并存是 τ 路线的固有代价: 拉回要 Setzer 序的良基, 而 Setzer 序的性质在它自己的项上证.
3. **封闭性 (约 800 行)** 已是 Lean 蓝本的约 1/3 (见 WfFsn §4), 这次没再压.
4. **`cl-fsT` (Ω-基本列封闭) 不在第 3 层**: FGH 只走 ω-基本列, Ω 部分只作为引理 (`NFΩ`, `TΩ`) 出现.

## §5 编译

从仓库根 (不要归档):

```text
agda --library-file=<含 stdlib 与 cubical 的库文件> -i src -i probes probes/OCF/Align/EboLean.lagda.md
```

`EboLeanCmp` (与旧版比较) 要把归档拷贝加进 `-i`, 同 [WfFsn](WfFsn.lagda.md) §4.

**选项的两处实测 (测试档).** Setzer 的拷贝加 `--lossy-unification` 在 `Lex` 报合一错; 改成纯 `--without-K` (去掉 `--cubical-compatible`) 时 `Facts3` 20 分钟未检查完. 所以 `EboLean/OT/` 保留归档的 `--safe --cubical-compatible`. 另有一处工程坑: `EboLeanTau` 里 `uc-app` 的隐参 $\{y\}\{z\}$ 不写出时, Agda 去合一 `app ?y ?z` 与 τ-像, 检查超过 10 分钟; 写出后 4 秒.

**切片:** `agda --html --html-highlight=all --html-dir=<H> -i src -i probes probes/OCF/Align/EboLeanLab.lagda.md`, 再 `python3 probes/Survey/scripts/htfeed/locslice_ebolean.py <H>`.
