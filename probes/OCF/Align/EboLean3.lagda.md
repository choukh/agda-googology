# EboLean3: 对 EBO 直接用突出集证良基, EBO-tree 第 3 层的标杆 (路线 (ii))

> **记号侧验收工作.** 读记号 (EBO 的项、序、基本列与标准形), 用 Setzer 1998 的突出集方法, 但只对 EBO 的项写 (没有 φ, 没有 I, 不经 τ, 不用 OT_I 的语法). 给的是验收用的参照树与行数标杆, 不是最终定义, 不进成品, 不让树更自足.
>
> **任务** (作者 2026-11-05): 参考现有代码重写 EBO-tree, 去掉不需要的依赖和死代码, 抽象掉重复, 得到没有水分的行数, 作为树侧的标杆. 第 3 层只算到 FGH 可计算, 标签另列一行. 接着 [EboLean2](EboLean2.lagda.md) 的路线 (ii) 做完.
>
> **判决: 做完 (HOLDS).**
>
> 1. **编译过的定理, 无前提:** `wf : NF t → Acc′ t`: **一切 EBO 标准形** (不限可数) 上 $<^\mathsf T$ 良基, 证明是 Setzer 突出集方法的 EBO 专门版 (§2). `EBO-tree″ : Ord` 与 `fgh-EBO″ : FGH EBO-tree″ n ≡ fgh (EBOψ n) (hc-tower n) n`. 导入闭包里没有 Setzer 的 OT_I, 没有 τ ([importclosure](../../Survey/scripts/importclosure.py) 列出的闭包只有 `EBO`, `EboLeanDef`, `EboLeanBase`, `EboLean2`, `EboLean3*` 与封闭性五个模块; 记号模块 `EBO` 在里面, 这本来就是记号侧).
> 2. **与旧标杆一致 (编译过的定理, 不计行数):** [EboLean3Cmp](EboLean3Cmp.lagda.md) 的 `fgh≡ : FGH EBO-tree″ n ≡ EboLeanTree.FGH EBO-tree′ n` 对一切 $n$.
> 3. **行数 (定义级切片, 口径同 [EboLean](EboLean.lagda.md) §3):** 第 1 层 **120**, 第 2 层 **131**, 第 3 层 **1513**, + 标签 **1533**. 旧标杆 (τ 路线) 是 120 / 131 / 6524 / 6544. 良基部分 (EboLean2 §1 的定义 46 行加 EboLean3 的四个文件 441 行) 共 **487** 行, 旧路线是 5486 行 (Setzer 机器 5240, τ 与拉回 246). EboLean2 §3 的估计 (良基部分约 1650–1900, 第 3 层约 2700–3300) **偏高三倍多**, 原因见 §4.
>
> 全部 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示, 无 `trustMe`, 无函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLean3 where

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import OCF.Align.EboLeanDef using (T; EBOψ; HC; fgh)
open import OCF.Align.EboLeanBase using (NF; Ctbl)
open import OCF.Align.EboLean2 using (𝕎; Ag)
open import OCF.Align.EboLean3Dist using (Ag𝕎; Ag-ind)
open import OCF.Align.EboLean3Omega using (𝕎-Ω; 𝕎-Ωs; 𝕎-all; Acc′; wf) public
open import OCF.Align.EboLean3Tree using (Ord; FGH; tree; hc; hc-tower; EBO-tree″; fgh-EBO″) public
open import OCF.Align.EboLean3Lab using (Labᴸ; lab-NF″; ebo-lab″) public
```

## §1 定理表

```agda
-- 第 3 层: 一切标准形属于突出集之并 𝕎, 𝕎 是突出集
_ : ∀ {t} → NF t → 𝕎 t
_ = 𝕎-all

_ : Ag 𝕎
_ = Ag𝕎

-- 第 3 层: 一切标准形良基
_ : ∀ {t} → NF t → Acc′ t
_ = wf

-- 第 3 层: 可数标准形的基本列遗传良基且可数; 极限树; FGH 逐点等于记号的 FGH
_ : ∀ {t} → NF t → Ctbl t → HC t
_ = hc

_ : ∀ n → FGH EBO-tree″ n ≡ fgh (EBOψ n) (hc-tower n) n
_ = fgh-EBO″

-- + 标签
_ : ∀ {t} (nt : NF t) (ct : Ctbl t) → Labᴸ (tree (hc nt ct)) t
_ = lab-NF″
```

| 名字 | 陈述 | Setzer | 档 | 文件 |
|---|---|---|---|---|
| `C`, `M`, `τ`, `𝒲`, `Ag`, `𝕎`, `C-all`, `lt⇒GB` | 层号索引的 $C$-集等定义; 可数层 $C$ 是全体; $y<\psi_w c\Rightarrow G_w(y)<c$ | Def 4.5, 4.12, 4.18, 4.25; 4.7 (a) 成为定义; Rem 2.15 (c) | 定义与定理 (复用) | [EboLean2](EboLean2.lagda.md) §1 |
| `C-cong`, `C-anti`, `C-up`, `C-hs`, `C-lift` | $C$ 的同余、降层、升层、首项下标、由 $M$ 提升 | 4.7 (b)(c)(g), $\tilde y\in C$ | 定理 | [EboLean3Base](EboLean3Base.lagda.md) |
| `𝒲-ind`, `W-hs`, `W-hd`, `W-tl`, `𝒲-cong`, `𝒲-cong≤` | $\mathcal W$-归纳; 分量留在 $\mathcal W$; 只依赖 $A$ 的一段 | Ass. 4.10, 4.13 (b) | 定理 | 同上 |
| `L417.W-+`, `W-Ω`, `W-suc`, `W-ψ`, `under` | $\mathcal W(A)\cap\Omega_{l+1}$ 对和、Ω、后继、$\psi_w$ 封闭 | 4.17 (b)(c) | 条件定理 (前提 `h`, `E` 是模块参数, 在 `AgL` 里由 `Ag A` 填上) | [EboLean3Close](EboLean3Close.lagda.md) |
| `Ag-ind`, `AgL.Ag-+`, `Ag-ψ`, `Ag-hs`, `Rem` | 突出集上的归纳; 突出集对和、ψ 封闭 | 4.20, 4.21 (a), 4.23 (a)(b) | 定理 | [EboLean3Dist](EboLean3Dist.lagda.md) |
| `agree`, `⊑𝕎⇒Ag`, `Ag𝕎`, `0∈𝕎`, `Ag-top` | 突出集的一致; $\mathbb W$ 的段是突出集; 加顶元 | 4.24, 4.26, 4.27 | 定理 | 同上 |
| `𝕎-Ωs`, `L430`, `𝕎-Ω` | $\Omega_l\in\mathbb W\Rightarrow\Omega_{l+1}\in\mathbb W$; 4.30; $a\in\mathbb W\Rightarrow\Omega_a\in\mathbb W$ | 4.23 (c), 4.30, 4.31 (a) | 定理 | [EboLean3Omega](EboLean3Omega.lagda.md) |
| `𝕎-all`, `wf` | 一切标准形属于 $\mathbb W$; 一切标准形良基 | 4.21 (a) 用在 $\mathbb W$ 上 | 定理 | 同上 |
| `hc`, `EBO-tree″`, `fgh-EBO″` | 可数标准形有 `HC`; 极限树; FGH 逐点相等 | | 定理 | [EboLean3Tree](EboLean3Tree.lagda.md) |
| `lab-NF″`, `ebo-lab″` | 带标签的树 | | 定理 (+ 标签行) | [EboLean3Lab](EboLean3Lab.lagda.md) |
| `fgh-irr`, `fgh≡` | `fgh` 与 `HC` 推导无关; 与 τ 路线的 `EBO-tree′` FGH 逐点相同 | | 定理 (不计行数) | [EboLean3Cmp](EboLean3Cmp.lagda.md) |

## §2 证明的结构与对 Setzer 的改动

**链.** `𝕎-all` 对 `NF` 结构归纳: $0\in\mathbb W$; $\Omega_w$ 由 `𝕎-Ω`; $\psi_w(c)$ ($c\ne0$) 由 `Ag-ψ`, 要 $\Omega_{w+1}\in\mathbb W$ (`𝕎-Ωs ∘ 𝕎-Ω`); 和 $\psi_v(b)+y$ 由 `Ag-+`, 界取 $\Omega_{v+1}$. 然后 `wf` 是 `Ag-ind Ag𝕎` 一行. `hcA` 沿 `wf` 递归, 封闭性给出 $t[n]$ 是标准形且 $<t$.

**EBO 专门化带来的简化 (都是编译过的代码里的事实; "为什么短" 是判断):**

| Setzer (EboLean 的切片行数) | EBO 版 | 怎么省的 |
|---|---|---|
| K, CLemmas, Lemma 4.7 (a), C-shift (约 300) | 归纳的 `C` (EboLean2), `C-anti` 等 (约 50) | 按层号索引, $\tilde a=\Omega_{\mathrm{hs}(a)}$, 4.7 (a) 是定义 (EboLean2 已做) |
| 4.17 (b)(c) 的内层 `sizeRec` 与句法分情况 (约 450) | 对 $C$-推导结构递归 (81) | 推导的构造子就是情况; 叶子用前提 `E`; `cψ` 在 $<\Omega_k$ 时矛盾 |
| Remark 4.15, `DC`/`UC` 记录, `Rem4-15` (约 480) | 无 | 只要三条: 和 (`W-+`, 首项为主项), 尾与首项 (`W-hd`, `W-tl`), 首项下标 (`W-hs`) |
| 4.17 (c) 的 $u<\tilde a$, $u=\tilde a$ 两支, $\theta\in W(A)$, `KSide` | 无 | `cψ` 推出 $\psi_v(c)$ 时 $v\ge w$, 只剩 $u>\tilde a$ 一支; $\pi$ 的侧条件就是对 $v$ 的递归 |
| 4.23 (a) 的 `max3` | 无 | 界取 $\Omega_{\mathrm{hs}(c)+1}$, 合成项 $<c$ 即可 |
| 4.24 的截段一般形, 4.28 (a)(b) | `agree` (16), 无 | 只证 4.26 (a) 要的那一句; 4.30 的集合直接用 `⊑𝕎⇒Ag` |
| 4.23 (c) 的 $A^+=\bigcup_{z\in A}\cdots$ | $Y'=(\mathcal W(Y)\cap\Omega_{l+1})\cup\{\Omega_{l+1}\}$ | 只对一个元素 $\Omega_l$ 造 |
| 4.31 (a) 的 `Ω-view` 三支, `CarView`, Fi′ | 无 | EBO 没有 Ω 的不动点; 盖集 $\{0\}\cup\{\Omega_{y+1}\mid y\in\tau^X(a)\}$ 同时管后继与极限 |
| 4.21 (b)(c) (可数部分) | 无 | $\mathbb W$ 含一切标准形, 4.21 (a) 直接给良基 |
| OT_I 的序论与 44 条句法事实 (约 2950) | EboLean3Base §1 的层号事实 (约 70) | EBO 的序是句法字典序, 线性与传递已在 EboLeanBase |

## §3 四层行数表

切片脚本 [locslice_ebolean3.py](../../Survey/scripts/htfeed/locslice_ebolean3.py), 口径同 `locslice_ebolean.py` (从根出发的定义级切片, 数到达块的非空非注释 agda 行, 导入行不数). **盲区的处理:** 带参数的模块别名 `module S = AgL agS` (L430 里) 与 `module W = AgL Ag𝕎`: `S.A⊆W` 的链接指向 `AgL` 的原定义, 别名那一行到不了, `agS` 会漏数; 脚本把 EboLean3* 里的一切别名块列为根并打印出来. 模块应用 `open L417 Y Y.h l (Y.E yΩ)` 写在 `where` 里, 属于被到达的块, 参数可见; `L417.W-+ A h (hs c) (E ac) …` 的参数写在调用处, 也可见. 本路线没有经记录字段的间接 (旧路线的 `OTFacts`). 核对: EboLean3* 六个文件里到不了的块只有导入行与模块行 (脚本加第二个参数时列出), 即没有死代码, 也没有漏数的定义.

| 层 | 根 | EBO-tree″ | 旧标杆 EBO-tree′ (τ 路线) |
|---|---|---|---|
| 1 定义 | `T`, `PT`, `_<ᵀ_`, `cmpᵀ`, `fsn`, `pred`, `EBOψ` | **120** | 120 |
| 2 + FGH | `HC`, `fgh` | **131** | 131 |
| 3 + 良基、封闭、树与 `fgh-EBO″` | `wf` (与别名根 `module S`, `module W`), `cl-fsn-NF`, `hc`, `EBO-tree″`, `fgh-EBO″` | **1513** | 6524 |
| + 标签 | `lab-NF″`, `ebo-lab″` | **1533** (+20) | 6544 (+20) |

第 3 层分组 (切片行数):

| 组 | 行数 | 来源 |
|---|---|---|
| EBO 定义 (`EBO` 里用到的块 125, `EboLeanDef` 31) | 156 | 复用 |
| 序、三歧、标准形、$G_u$、可数项 (`EboLeanBase`; 其中良基部分用到 158) | 241 | 复用 |
| 突出集的定义 (`EboLean2` §1: `C`, `M`, `τ`, `𝒲`, `Ag`, `𝕎`, `C-all`, `lt⇒GB`) | 46 | 复用 |
| 良基: 层号与 $C$/$\mathcal W$ 引理 (`EboLean3Base`) | 154 | 新写 |
| 良基: 4.17 (b)(c) (`EboLean3Close`) | 81 | 新写 |
| 良基: 突出集通用层, 4.21, 4.23 (a)(b), 4.24–4.27 (`EboLean3Dist`) | 92 | 新写 |
| 良基: 4.23 (c), 4.30, 4.31 (a), 组装与 `wf` (`EboLean3Omega`) | 114 | 新写 |
| 封闭性 (`EboLeanView` 163, `Trian` 197, `Omega` 58, `Bach` 100, `Closure` 61) | 579 | 复用 |
| 树、FGH、`hcA`、Ω-塔 (`EboLean3Tree`) | 50 | 重写 (形状同 `EboLeanTree`) |

分层的增量: 第 3 层在第 2 层之上加 1382 行, 其中只为良基的 650 行 (第 2 层之上, 根只取 `wf`: EboLean3 四个文件 441, EboLean2 46, EboLeanBase 158, EBO 5), 封闭性与树 732 行.

**文件与代码行** (agda 块的非空非注释行, 含导入): EboLean3Base 168, EboLean3Close 93, EboLean3Dist 106, EboLean3Omega 130, EboLean3Tree 62, EboLean3Lab 27, EboLean3Cmp 28 (不计), 本文 (入口, 只有定理表的 `_ = …`, 不计).

## §4 还不是最小的地方, 与估计为什么偏高 (判断档, 除标明者)

1. **复用的部分占第 3 层的一半以上** (EBO 156, EboLeanBase 241, EboLean2 46, 封闭性 579, 共 1022 / 1513). 按任务原样复用, 没有重新压. EboLeanBase 里有为封闭性写的 `cmpᵀ`↔$<^\mathsf T$ 对应、大小、$G$ 的单调等; 哪些能省没有逐条核对. 封闭性 (Buchholz 3.3–3.6, 579 行) 是这条路线现在最大的一块.
2. **本文代码里剩下的重复.** 对 $C$-推导的递归有四处同形的和分支 (`C-up`, `W-Ω` 的 `go`, `under`, `star`). 试算过一个通用消去子 (约 14 行) 换掉其中三处, 净省约 0 行 (判断, 未编译), 所以没做. `C-anti` 要三个互递归函数 (`antiT`, `antiP`, `antiN`), 因为叶子换成 $M(A)$ 的推导后推导不变小, 只能对项结构递归.
3. **EboLean2 的估计为什么偏高三倍多.** 它按 Setzer 的模块逐个打折 (§3 的表). 实际省得多, 主要因为三件事 (前两件是这次写的时候才发现的): (a) 内层归纳改对 $C$-推导递归, Setzer 每个引理里 "按项的形状 + 大小归纳 + 判断是否在 $C$ 里" 的结构整个消失; (b) Remark 4.15 那套从弱封闭到封闭的记录不要, EBO 的列表结构只要三条分量引理; (c) 句法事实只剩层号的十几条. 所以 EboLean2 §3 的 "句法事实 350–600" 与 "Closed, Closed2 180" 两项估计最偏.
4. **良基的范围比需要的大.** `wf` 对一切标准形成立, 第 3 层只用到可数的; 这不增加行数 (反而省掉了 4.21 (b)(c)).

## §5 编译

从仓库根:

```text
agda --library-file=<含 stdlib 与 cubical 的库文件> -i src -i probes probes/OCF/Align/EboLean3.lagda.md
agda --library-file=<同上> -i src -i probes probes/OCF/Align/EboLean3Cmp.lagda.md
```

切片: `agda --html --html-highlight=all --html-dir=<H> -i src -i probes probes/OCF/Align/EboLean3Lab.lagda.md`, 再 `python3 probes/Survey/scripts/htfeed/locslice_ebolean3.py <H>` (加任意第二个参数列出到不了的块). 实测 (测试档, 并行环境下): 各文件从头检查都在几秒内, 堆远低于 6G.
