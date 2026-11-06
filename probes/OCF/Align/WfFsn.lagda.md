# WfFsn: EBO 标准形对基本列封闭; 可数 EBO 标准形的带标签树与 EBO 的 FGH (无条件)

> **记号侧验收工作**, 不是最终定义, 不进成品. 读记号 (EBO 的项、`cof`、`fsn`、`fsT`、`γT`, bot 的标准形谓词 `isOTᵉ`, 归档 Setzer OT_I 的良基), 给出的是验收用的参照树. 接 [WfTauNF](WfTauNF.lagda.md) (`StdFsn`) 与侦察报告 [NotationWF](../../Survey/NotationWF.md); 本文件与 `WfFsn*` 各段都是新文件, 不改它们.
>
> **结论 (编译过的定理, 无前提).**
>
> 1. **`cl-fsn` 成立**, 原样的类型 (`WfFsnClosure.cl-fsn`). 而且更强: 不要 `Ctbl` (对一切共尾度为 $\omega$ 的 EBO 标准形, `cl-fsnᵇ`), Ω-基本列也封闭 (`cl-fsT`: $a$ 标准、共尾度 $\Omega_{\mu+1}$, $\eta$ 标准且 $\eta<\Omega_{\mu+1}$ ⟹ $a[\eta]$ 标准). 这是 Buchholz 1986 Lemma 3.3 对扩展 Buchholz 记号 (下标是项) 的 Agda 证明, `--safe --without-K`, 构造性, 按 koteitan/googology-lean `ExBuchholz` (`6da2de5`, MIT) 的证明组织在我方定义上重写.
> 2. **`StdFsn` 的前提全部消去** (§1): `ebo-lab : ∀ k → Lab … (EBOψ k)` (Ω-塔 $\psi_0(\Omega$-塔$_k)$ 对一切 $k$ 有带字面标签的树), `lab-NF` (**一切可数 EBO 标准形都有带标签的树**), `EBO-tree` 与 `fgh-EBO` (极限树的 FGH 在 $n$ 处逐点等于记号沿基本列的 FGH $f_{\psi_0(\Omega\text{-塔}_n)}(n)$). EBO $=\psi_0(\Lambda)$ 的大数在 Agda 里有了良基证明; 记号侧第 3 层 (良基) 完成.
>
> 编译要把归档拷贝加进 `-i` (§3), 只因为 `WfTauNF` 导入归档; `WfFsnBase`…`WfFsnClosure` 六段不导入归档. 全部 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示, 无 `trustMe`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WfFsn where

open import Data.Bool.Base using (true)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import OCF.Align.EBO as E
open E using (T; fsn; EBOψ)
open import OCF.Align.EBOI using (isOTᵉ)
open import OCF.Align.Standard using (Ctbl)
open import OCF.Align.Level using (Ordᶜ; zero; FGH)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.AccTree using (fghₙ)
open import OCF.Align.AccTreeLab using (treeᴴ; HC→Acc)
open import OCF.Align.WfTauNF using (module StdFsn)
open import OCF.Align.WfFsnClosure using (cl-fsn; cl-fsnᵇ; cl-fsT; cl-fsn-NF; trian-fsn; trian-fsT) public
```

## §1 实例化

```agda
module S = StdFsn cl-fsn

ebo-lab : ∀ k → Lab (treeᴴ (S.hc (S.p-tower k))) (EBOψ k)
ebo-lab = S.ebo-lab′

EBO-tree : Ordᶜ zero
EBO-tree = S.EBO-tree′

fgh-EBO : ∀ n → FGH EBO-tree n ≡ fghₙ (EBOψ n) (HC→Acc (S.hc (S.p-tower n))) n
fgh-EBO = S.fgh-EBO′

lab-NF : ∀ {t} (nf : isOTᵉ t ≡ true) (c : Ctbl t) → Lab (treeᴴ (S.hc (nf , c))) t
lab-NF = S.lab-NF
```

## §2 证明的组织 (各段的结论都是编译过的定理)

| 段 | 内容 | Lean 对应 |
|---|---|---|
| [WfFsnBase](WfFsnBase.lagda.md) | $\le$, 三歧; $G_u$ 的成员关系 `InG`; 归纳的 `NF` 与 `isOTᵉ` 互转 (`toNF`, `fromNF`); 门槛之下 $G$ 为空; `pred` 保标准形; 大小 | `Order`, `Std`, `Sum`, FS 的小引理 |
| [WfFsnView](WfFsnView.lagda.md) | 共尾度视图 `VΩ`, `Vω`; 沿视图的 `fΩ`, `fω`, `γ` 与 EBO 的 `fsT`, `fsn`, `γT` 逐点相等; 单调; $\mu$ 标准, $\mu+1<a$ | `dom`, `fs`, `tower`, `fs_numeral`, `fs_mono`, `tower_lt` |
| [WfFsnTrian](WfFsnTrian.lagda.md) | $b\lhd_z a$; 3.4 (`Gtri`); 3.5; 3.6 的 Ω 部分 (`TΩ`, 无标准形); γ-链的界; 规则 6 的 3.6 (`T-case4`) | `Trian`, 3.4, 3.5, `tower_G_le`, `Trian_case4` |
| [WfFsnOmega](WfFsnOmega.lagda.md) | 3.3 的 Ω 部分 (`NFΩ`); 下标的界 (`SB`); 脊上可见性 | `OTFS_aux` 非规则 6 分支, `SubBound`, `G_dom_subset` |
| [WfFsnBach](WfFsnBach.lagda.md) | Bachmann 性质 (`bach`), 大小论证 | `size_fs_W0`, `G_size_succ_lt`, `no_small_between`, `bachmann` |
| [WfFsnClosure](WfFsnClosure.lagda.md) | γ-链不变量 (`tow`); 3.6 的 ω 部分 (`Tω`); 3.3 的 ω 部分 (`NFω`); `cl-fsn`, `cl-fsT` | `towerOT_of_Bachmann`, `Trian_fs`, `OTFS_thm` |

**与 Lean 证明的差别** (都是证明组织, 陈述同 Lean):

1. **结构递归代替大小归纳.** Lean 的 `OTFS_aux`/`Trian_fs_aux` 对 `size` 归纳, 把 3.3 与 3.6 捆在一起. 这里沿共尾度视图结构递归, 依赖是线性的: 3.6(Ω) (无标准形) → 3.3(Ω) → 下标的界 → Bachmann (独立) → γ-链不变量 → 3.6(ω) → 3.3(ω). 原因: 我方 `fsT`/`fsn` 是两个函数, Ω-基本列里没有规则 6, 所以 Ω 部分自成一个归纳; Lean 的 `fs X Y` 一个函数管两种下标, 只能一起归纳.
2. **下标的界直接界 $G_u(\nu)$** (Lean 界 $G_u(\nu+1)$ 再用 3.6 换下来).
3. **Bachmann 性质只用空前缀**, 不要 Lean 的 $\nu+1>A$ 条件.
4. **规则 6 的 3.6 取 $z=0$** (Lean 取 $z=n$; $G_u(n)\subseteq\{0\}$, 等价).

## §3 有限测试 (测试档, 不是证明)

`refl` 算出: Ω-塔第 3 级的两个基本列项是标准形, 与 `cl-fsn` 的结论一致.

```agda
_ : isOTᵉ (fsn (EBOψ 3) 2) ≡ true
_ = refl

_ : isOTᵉ (fsn (fsn (EBOψ 3) 2) 1) ≡ true
_ = refl
```

## §4 结论与估计

**定理表.**

| 名字 | 陈述 | 档 |
|---|---|---|
| `cl-fsn` | `isOTᵉ t ≡ true → Ctbl t → cof t ≡ cω → ∀ n → isOTᵉ (fsn t n) ≡ true` (StdFsn 的前提原样) | 定理, 无前提 |
| `cl-fsnᵇ`, `cl-fsn-NF` | 同上, 不要 `Ctbl` | 定理, 无前提 |
| `cl-fsT` | $a$ 标准、`cof a ≡ cΩ μ`, $\eta$ 标准、$\eta<\Omega_{\mu+1}$ ⟹ `isOTᵉ (fsT a η) ≡ true` | 定理, 无前提 |
| `trian-fsn`, `trian-fsT` | Buchholz 3.6: $t[n]\lhd_0 t$ (要标准形); $a[\eta]\lhd_\eta a$ (不要标准形) | 定理 |
| `Gtri` | Buchholz 3.4 | 定理, 对一切项 |
| `bach` | Bachmann 性质 $G_A(B)<B[\Omega_\nu]$ ($\psi_A(B)$ 标准, `VΩ B ν`), 不要 $\nu+1>A$ | 定理 |
| `ebo-lab`, `lab-NF`, `EBO-tree`, `fgh-EBO` | Ω-塔与一切可数标准形有带标签的树; 极限树的 FGH 逐点等于记号的 FGH | 定理, 无前提 |
| §3 两条 `refl` | `fsn (EBOψ 3) 2` 及其基本列项是标准形 | 测试 |

**侦察估计的复核 (判断档).** 侦察报告估 `cl-fsn` 3000 到 7000 行, WfTauNF 修订为 2500 到 5000 行. 实际是六段共约 850 行非空代码 (不含导入), 约为修订估计下限的 1/3. 判断原因有三: (1) 沿共尾度视图结构递归, 省掉了 Lean 对 `size` 的捆绑归纳与 59 处 `omega`; (2) 我方 `fsT`/`fsn` 分开, Ω 部分没有规则 6, 依赖变成线性, 3.3 与 3.6 不必一起归纳; (3) Lean 的若干步在我方定义上是句法事实 (`pred-suc`, `<sucT`), 不要标准形. 侦察报告说的 "倍数不可靠" 这次偏向了高估. 核心确实是 Lean 的相对不变量 `Trian` 与 Bachmann 性质的大小论证, 静态的 `Gnil` 没有用上, 与 WfTauNF 的判断一致.

**剩下的.** `StdFsn` 的前提已无. 侦察报告 §4 第 2 条仍然成立: 这给的是参照树 (读记号, 只在验收文件里用), 不是第 4 层的值比较; 主线树与参照树互相 `⊑⁰`/`≼` 的证明每站照写. 它不让树更自足.

**编译** (从仓库根; 归档只读, 用临时拷贝): 把 `archive/src/Mahlo` 拷到个人临时目录 `<arch>/`, 加 `<arch>/arch.agda-lib`:

```text
name: wffsn-arch
depend: standard-library-2.4
include: .
flags: --hidden-argument-puns -W noUnsupportedIndexedMatch
```

然后 `agda --library-file=<含 stdlib 与 cubical 的库文件> -i src -i probes -i <arch> probes/OCF/Align/WfFsn.lagda.md`. 只编译封闭性 (`WfFsnClosure`) 不要归档.
