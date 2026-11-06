# 沿 View 递归: 部分的良基

> 入口. [BrwView](BrwView.lagda.md) 的记录 `BrwView` 给每个合法对象一个布劳威尔树的 View (零, 后继, $\mathbb N$-极限, $\Omega$-极限), 但没有部分的良基, 所以还不能沿 View 定义函数. 这里补上: 部分关系 `_◁_`, 带良基的记录 `BrwViewᵂ`, 三个实例, 一般的递归原理, 一个检验 (经 View 读出布劳威尔树、经 View 算 FGH, 与原来的读法一致). 不读记号, 不用 `Funext`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> **判决: 三处都是定理, 良基都无条件.** 第 0 层差树与高度树 `H`: View 无条件, 良基无条件. 第 1 层差树: View 本身条件于 `HW` (不变, 见 BrwView), **在这个 View 上部分良基不要任何别的条件** (证明里 `HW` 只当作 `vw` 的参数传过去). 关键是度量: 不能取值的序 (两条编译过的否定), 第 0 层取 `A` 的直接子树 (部分的值字面地是整体的值的直接子树), 第 1 层取 `B₁` 上的**秩的比较** (模拟序), 它只要 "抬升不升秩" 这一个方向, 这个方向无条件 (`Rv`), 而值一致要的反方向 (`WSq`) 不是无条件的.

## 1 定义 ([BrwWfDef](BrwWfDef.lagda.md))

```text
Obj = Σ Ix (λ i → Σ (X i) Lgl)                       -- 合法对象, 带合法性的证明
data Part {i v} : View i v → Obj → Set where
  p-s : Part (vs y ly e) (i , y , ly)
  p-l : ∀ n → Part (vl f lf st e) (i , f n , lf n)
  p-Ω : ∀ c (lc : LgC c) → Part (vΩ k g lg e) (tg c , g c , lg c lc)   -- 只在合法坐标上
o ◁ (i , x , lx) = Part (view x lx) o
record BrwViewᵂ : Set where
  bv : BrwView ; wf : WellFounded (_◁_ bv)           -- 标准库的 Acc
```

`_◁_` 由 View 的选法决定, 不看对象的字面结构. 递归原理 `rec` ([BrwWfRead](BrwWfRead.lagda.md)) 对 `Acc` 结构递归, 每一步只看 View 的种类与部分上的值.

## 2 定理

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `measure` | BrwWfDef | 部分在某个良基关系里沿度量下降 ⇒ `_◁_` 良基 | 定理 |
| `<ₛ-wf`, `≤ₛ-trans`, `sub≤` | BrwWfRank | 对任意良基的直接子树关系, 秩的比较 (模拟序) 良基、传递、子树在下 | 定理 |
| **`wf₀`**, `view₀ᵂ` | BrwWfZero | 第 0 层差树: 部分良基, 度量 `sum azero`, 关系 `SubA` | **定理, 无条件** |
| **`wfᴴ`**, `viewᴴᵂ` | BrwWfHt | 高度树: 部分良基, 度量是自己, 关系 `SubH` | **定理, 无条件** |
| **`Rv`** | BrwWfOneRank | 第 1 层差树在更大的世界里求值, 秩不升: $b'\sqsubseteq b\Rightarrow S_{q\cdot p}(b',y)\sqsubseteq S_q(b,y)$ | **定理, 无条件** |
| `Ksuf`, `Smono`, `Kmono`, `Imono`, `⊲→⊑` | BrwWfOneRank | 层段的后缀不升秩; 对底单调; 第一位置在下 | 定理 |
| `Jle`, `CKs` | BrwWfOne | 部分积分 `J` 不超过 `I`; `Cut` 在顶上求值不超过 `K` 逐段求值 | 定理 |
| **`wf₁`**, `view₁ᵂ` | BrwWfOne | 第 1 层差树 (`HW`, 即 View 存在的条件): 部分良基, 度量 `toB`, 关系秩的比较 | **定理, 在 View 上无条件** |
| `rec`, `Read.rd`, **`ReadOk.rd≈`** | BrwWfRead | 一般的递归原理; 经 View 读出目标布劳威尔树 (要一切坐标合法 `allC`); 读出的树与值互相 $\preccurlyeq$ (要目标树的四条单调 `Cong`) | 定理 |
| `rd₀≈`, **`rd₀≅`** | BrwWfZero | 第 0 层: 读出的 `A` 与 `sum azero` 互相 $\le$; 更强, 逐点字面相等 | 定理 |
| `rd₁≈` | BrwWfOne | 第 1 层: 读出的 `B₁` 与 `toB` 互相 $\preccurlyeq$ | 定理 (前提 `HW`, 同 View) |
| **`fgh₀≡`** | BrwWfZero | 经 View 算的 FGH 与 `sum azero x` 上的 FGH 逐点相等 | 定理 |
| `test-ω`, `test-ω+1` | BrwWfZero | $f_\omega(2)=8$, $f_{\omega+1}(1)=2$ 经 View 算出 | **有限测试** |
| **`no-strict₀`** | BrwWfNeg | 第 0 层 View 的部分不在值上严格下降 (反例 `nl (λ _ → n0)`) | 否定, 定理 |
| **`no-wf-⊏ᵥ`** | BrwWfNeg | "按值低于某个直接子树" 不良基, 反例 $\lim(\omega,\omega,\dots)$ 合法 | 否定, 定理 |

**第 0 层.** 部分是前缀 $x$ 与部分和 $x⨾(d_0⨾\dots⨾d_{n-1})$, 不是字面子项, 但部分的值字面地是整体的值的直接子树: 后继 `asuc (sum x)` 的 `sum x`, 极限 `alim (pt …)` 的第 $n$ 项 (`ps-pt`). `dec₀` 与 `vw` 同形归纳. 所以度量就是值, 序是值的**结构** (直接子树), 不是值的前序 $\le$.

**第 1 层.** $\Omega$-极限的部分是 "前缀 $x$ 抬到 $W'$, 接 `J`" (`ki`) 或 "抬到 $c$, 接 `Cut`, 接 $u(c)$" (`kκ`); 它们的值与整体的分支只 $\approx$, 而且 $\approx$ 要 `HW`. 秩的比较只要一个方向: 部分的秩 $\sqsubseteq$ 分支的秩. 这个方向是 "在更大的世界里求值秩不升" (`Rv`), 原因是大世界里 `ni`/`nκ` 的分支是小世界里分支的一部分 (坐标 $p''\mapsto p\cdot p''$), 层上的段是后缀. 不要 `WSq`, 不要 `HW`.

**第一个障碍** (已过). 想用值作度量: (1) 值严格下降不成立 (`no-strict₀`, 根子是 `strict→LPO`: 极限步进不严格); (2) "按值低于直接子树" 不良基 (`no-wf-⊏ᵥ`); (3) 第 1 层值的字面相等要 `Funext` (`J` 与 `I` 的极限是两个逐点相等的函数). 三条一起逼出秩的比较: 函数上逐点 (不要 `Funext`), 极限处不把常数列与它的项等同 (良基), 只要一个方向 (无条件).

## 3 检验: 沿 View 递归

- **读出布劳威尔树** (`Read.rd`, 一般): 零→`bz`, 后继→`bs`, $\mathbb N$-极限→`bl`, $\Omega$-极限→`bΩ`, 部分递归地读. `ReadOk.rd≈`: 读出的树与 `val` 互相 $\preccurlyeq$. 第 0 层 (`rd₀≈`, 对 `sum azero`) 与第 1 层 (`rd₁≈`, 对 `toB`) 都实例化. 高度树的 $\Omega$-极限有不合法坐标, `rd` 不适用, 它的 View 是恒等, 不需要读.
- **经 View 算 FGH** (`fgh₀`, 第 0 层): 零 $n+1$, 后继 $f^n(n)$, 极限取第 $n$ 个部分在 $n$ 的值. `fgh₀≡`: 等于 `sum azero x` 上的 FGH, 逐点 $\equiv$. FGH 在 $\approx$ 下不变不成立, 所以这一条走字面相等 `rd₀≅` (第 0 层的 View 是字面的, 这要看 `vw` 的构造, 记录只给 $\approx$).

## 4 未做

- 第 1 层 View 本身仍条件于 `HW` (本篇不动它). 第 1 层的 FGH 要 $\Omega$-极限的基本列, 不在本篇.
- 第 1 层上 `rd₁` 与 `toB` 字面相等 (`≅`): 未做. 第 1 层 View 的 $\Omega$-极限只 $\approx$, 估计不成立 (判断, 未编译).
- 第 2 层以上: 未做. 估计同形: `Rv` 的论证只用 "大世界的分支是小世界分支的一部分", 与层号无关 (判断).

## 5 翻译账

| 模块 | 记号读来的字段或形状 | 树逼出的 | 类 |
|---|---|---|---|
| `BrwWfDef` | 无 | 部分只在合法坐标上 (`p-Ω` 带 `LgC`, 由 `H` 逼出); 部分带自己的合法性证明 (第 1 层 `HW` 带内容) | 提供信息 |
| `BrwWfRank` | 无. 秩的比较是集合论的秩, 不是记号 | 由 `no-strict₀`, `no-wf-⊏ᵥ` 与 "不用 `Funext`" 逼出 | 提供信息 |
| `BrwWfZero` | 无 | 度量是值的结构; `dec₀`, `lit` 与 `vw` 同形 | 提供信息 |
| `BrwWfHt` | 无 | 恒等 | 提供信息 |
| `BrwWfOneRank` | 无 | `Rv`: 一步的结构定理 (对 $y$), 新用到的字段: `ni` 分支的世界参数、`nκ` 的层段 `K` 的路径 (后缀 `Ksuf`), `nw` 的路径结合 (`⊲-assoc`, `tailP-tr`) | 提供信息 |
| `BrwWfOne` | 无. `Jle`, `CKs` 照 `JI`, `CK` 的形状 | 只要一个方向 (秩), 不要 `WSq` | 提供信息 |
| `BrwWfRead` | 无 | `allC` (高度树逼出), `Cong` (目标树的单调) | 提供信息 |
| `BrwWfNeg` | 无 | 否定定理划出度量不能取的两种形状 | 提供信息 |

**按 `AGENTS.md` 归类: 提供信息.** 没有新构造子, 没有改树、折叠或 View, 没有 `Lab`, 没有序数值验收 (不爬站). 新的结构: 秩的比较 $\sqsubseteq$ (树侧的、与记号无关的判据: "抬升不升秩" 对一切第 1 层差树成立). 它是树侧合法性标准的候选 (`Reg`, `wk` 一类): 值一致要 `HW`, 递归只要 `Rv`, 两者分开了.

## 6 审计

`importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRuleSpec --only OCF.Align.TLRuleSum --only OCF.Align.TLRule --only OCF.Align.SumOne --only OCF.Align.BrwMid --only OCF.Align.LayerTr --only OCF.Align.NoCumLit --only OCF.Align.HtFeed --only OCF.Align.BrwView --only OCF.Align.BrwWf OCF.Align.BrwWf`: 闭包 39 个模块 (本地 28, 库 11), 禁用表 0, `--only` 之外 0, OK.

`depslice.py` (到达块 / 记号模块块 / 别处记号词): `BrwWfZero:view₀ᵂ` 78/0/0, `BrwWfZero:rd₀≈` 91/0/0, `BrwWfZero:fgh₀≡` 99/0/0, `BrwWfHt:viewᴴᵂ` 39/0/0, `BrwWfOneRank:Rv` 81/0/0, `BrwWfOne:view₁ᵂ` 166/0/0, `BrwWfOne:rd₁≈` 192/0/0, `BrwWfNeg:no-strict₀` 84/0/0, `BrwWfNeg:no-wf-⊏ᵥ` 14/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明没有受记号启发.

代码行 (agda 块里非空非注释): `BrwWfDef` 26, `BrwWfRank` 33, `BrwWfRead` 58, `BrwWfZero` 127 (含有限测试 6), `BrwWfHt` 34, `BrwWfOneRank` 167, `BrwWfOne` 95, `BrwWfNeg` 48, 入口 10; 合计 598.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwWf where

open import OCF.Align.BrwWfDef using (Obj; Part; p-s; p-l; p-Ω; _◁_; BrwViewᵂ; measure) public
open import OCF.Align.BrwWfRank using (module Rank) public
open import OCF.Align.BrwWfRead using (rec; module Read; Cong; module ReadOk) public
open import OCF.Align.BrwWfZero using (SubA; wf₀; view₀ᵂ; rd₀≈; _≅_; rd₀≅; fghA; fgh₀; fgh₀≡; test-ω; test-ω+1) public
open import OCF.Align.BrwWfHt using (SubH; wfᴴ; viewᴴᵂ) public
open import OCF.Align.BrwWfOneRank using (Sub₁; _⊑_; Rv; Ksuf; Smono; Kmono; Imono; ⊲→⊑) public
open import OCF.Align.BrwWfOne using (Jle; CKs; dec₁; wf₁; view₁ᵂ; rd₁; rd₁≈) public
open import OCF.Align.BrwWfNeg using (no-strict₀; no-wf-⊏ᵥ; Lg-x) public
```
