# 嵌套 `nκ` 的值语义 (续): 入口

> **判决: PARTIAL.** `KStepᴬ` 没有证出, 但已归结为**一格**的比较 `CellStep`; 一格之内的首对齐**未走通**, 只是未完成, 不是否定. 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`. 接 [KNest](KNest.lagda.md), 那里的文件一个没改.
>
> 1. **单个 `nκ` 的一步归结为一格 (定理).** [KNest2Glue](KNest2Glue.lagda.md) `kstep : CellStep → KStep²`. `KStep²` 是 `KStepᴬ` 加一条前提: 两边树世界可比. 对格号 $n$ 归纳, 每一格都满足 `CellStep` 的前提:
>    - 第 0 格: Adm 由支配与上下文复合, 起点可比由新前提给出, $\ell\le\ell'$ 由 `hℓ-inv`;
>    - 第 $n+1$ 格: 起点 $v_n\le v'_n$, Adm 取 $\delta=V_0(d_n)$;
>    - 状态: `Cxᴵ` 经 `cv` 推进.
>
>    部分和逐格累加. 格与格之间**没有对齐问题**, 对齐全在一格之内.
> 2. **可靠性只剩一格 (条件定理).** [KNest2Sound](KNest2Sound.lagda.md) `snd²`: 带下标的关系 ($\kappa$ 规则多一条 "树世界可比") 对一切深度可靠, 唯一的参数是 `CellStep`. `nest-rel²` 无条件: 嵌套族 $\mathrm{nest}_k$ 对一切 $k$ 都在关系里. `nest-mono²` 以 `CellStep` 为参数.
> 3. **`CellStep`: 未走通.** 第一个障碍见 §3. 判断: 照建议的形状 (按 $d_0$ 的结构首对齐, 套 `DValCanon.Gen`/`cong0`) 做不成, 因为 `cong0` 用到 Gen 的 `lim-leP` 一律, 而这条律在带领先量的语义下不可靠.
> 4. **"树世界可比" 为什么要作前提.** 一格之内, 右边起点高时用首对齐, 低时用恒等对齐. $A$ 上的序不可判定, 所以这个选择要由推导携带. 这一条是判断, 没有编译成否定.

## 1 `CellStep` 的精确类型

    Wk u s p ap co Y = F.Walk ac₁ u (W s) p ap (lW s) C.self (lW s) (ll s) (act s) co Y     -- 沿 a ⊲ W s, 在世界 W s 里走
    d0 Δ = F.yc Δ (inj₁ (z⊲ W)) tt

    CellStep = ∀ {V V′} {u : Bk V} {u′ : Bk V′} → SX u u → SX u′ u′ → SX u u′ →
               ∀ (s s′ : Sd) → Ok s s′ → ∀ {a a′} (p : a ⊲ W s) (p′ : a′ ⊲ W s′) (ap : V ⊲ a) (ap′ : V′ ⊲ a′) co co′ Y Y′ →
               Cxᴵ s s′ Y Y′ → ℓ Y ≤ W s → Adm a a′ (W s) (W s′) → (a ≤ a′ ⊎ a′ ≤ a) → W s ≤ W s′ →
               ∀ e e′ → e ≤ e′ → sum e (d0 (Wk u s p ap co Y)) ≤ sum e′ (d0 (Wk u′ s′ p′ ap′ co′ Y′))

    KStep² = ∀ {α α′ V V′ zz zz′} {u : Bk V} {u′ : Bk V′} → Adm V V′ α α′ → (V ≤ V′ ⊎ V′ ≤ V) →
             SX u u → SX u′ u′ → SX u u′ → OutLeᴬ α α′ (nκ zz u) (nκ zz′ u′)

`SX`, `OutLeᴬ`, `Cxᴬ` 沿用 `KNestSound`; `Cxᴵ`, `ℓ` 沿用 `KNestInv`. 判断: 经典地 `CellStep` 成立. 依据:
- 首对齐 (偏移相同) 时, 左右的剩余长度由 Adm 控制;
- 恒等对齐时, 由 $W\le W'$ 控制;
- 状态逐对可比.

## 2 定理

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `Side.cohS`, `cohΔ`, `ℓv`, `invU`, `invL`, `κL`, `κR` | KNest2Glue | 一边的格: 路径一致, 格世界 = 进格时回灌层, 单边不变量, 两条路径换读 | 条件定理 (动作 `CohA`, 状态一致) |
| **`kstep`** | KNest2Glue | `CellStep → KStep²` | 定理 |
| **`snd²`** | KNest2Sound | 关系对一切深度可靠 | 条件定理 (参数 `CellStep`, 动作 `Ok`) |
| **`nest-diag²`, `nest-rel²`** | KNest2Sound | 任意深度的嵌套族在关系里 | 定理 |
| `nest-mono²` | KNest2Sound | 嵌套族单调 | 条件定理 (`CellStep`) |

**否定.** 本轮没有新的否定定理. §3 里关于 `lim-leP` 的结论是判断.

**有限测试.** 无.

## 3 第一个障碍: 一格之内的首对齐

一格是 "沿字面路径 $a\lhd W$ 逐层走分支". 嵌套的分支在层 $c$ 上的领先量是 $\ell\ominus c=(W\ominus c)+z$: 它看的是**整格**剩下的长度, 不是正在走的那一段前缀的. 下面三点都是判断, 依据写在每条里.

- **尾对齐** (`KValCut.CutM`, `DValCanon.Gen.M`) 在 "左边是极限" 那一步出问题. 那一步把左边的前缀 $[a,f_m)$ 整个对到右边; 左边那一对的剩余长度多了 $\lim f\ominus f_m$, 右边没有. 数值形状就是 `KNestAdm.¬adm-end`. 后继步、"右边是极限" 一步、右边多出的尾巴都没有问题.
- **记剩余长度的首对齐** (两边各带 "这一段之后还剩多少" $\rho\le\rho'$). Gen 的结构律里, 单位律、结合律、`⨾`、`nl` 逐项、`nw`、两种传递、`pre-le`、`infl` 都能保持它, 只有 `lim-leP` 不能. `lim-leP` 用前缀 $x⨾\mathrm{pre}\,d\,k$ 的比较推出 $x⨾\mathrm{nl}\,d$ 的比较, 而前缀的剩余长度比全体多了 $\sum_{j\ge k}d_j$. `cong0` (由值 $V_0(d_0)\le V_0(d_0')$ 推出关系) 经 `lim-bd`, `PIL` 用到 `lim-leP`. 所以只有值的比较, 喂不进首对齐.
- **由值求首对齐的对应点**, 要在右边的字面结构里找出与左边偏移值相等的层. 这要比较布劳威尔树的值, 一般不可判定.

**可行的方向 (判断, 没有编译).** 不从值出发, 从**结构**出发. 若两格的坐标 $d_0$, $d_0'$ (上一格的输出) 由一个**不含左边极限截断**的结构关系相关, 一格的首对齐可以照它逐个构造子走:
- 关系的构造子: `n0 ⊑ z`, `n1 ⊑ n1`, `⨾`, `nl` 逐项, `nw` 两边, `pre-le`, 传递, 单位, 结合;
- 不含: `lim-leP`, `lim⊑`.

这要两件:
1. 桥: "`Walk` 沿 `sum-fst b x` ≈ 以 $x$ 为坐标逐项走", 含复合路径 (`⨾` 的 `sum-fst` 是 `⊲-tr`) 与极限 (`WRp` 对 `Rpt`);
2. 折叠的输出在这个结构关系里相关.

第 2 件就是 "对折叠输出封闭的关系", 正是 `MonoPort2` 在 `HtFeedFold` 上做的事. **给 `MonoPort2` 的接口 (判断):** 若它的输出关系在第 0 层坐标上不用左边极限截断 (`lim⊑` 一类), `CellStep` 的首对齐可以接上; 若要用, 首对齐在那一步断, 与这里同一个障碍. 第 0 格的路径是 "树世界 → 折叠世界 → $\ell$", 起点那一段没有坐标树, 要单独处理 (右边起点低时用恒等对齐, 走到 `CutM` 的后继与右极限情形).

## 4 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `KNest2Glue` | 无. 格的前提由 `κc` 的字面逼出: 起点是上一格的格世界, 格世界是 `sum v d`, 状态由 `cv` 换世界; Adm 的 $\delta=V_0(d_n)$ 读自 `sum-toA` | 提供信息 |
| `KNest2Sound` | 无新构造子, 无新折叠规则. 只多一条 "树世界可比", 由一格之内要选对齐方式逼出 (序不可判定) | 提供信息 |

没有用 `Lab`, 没有读自记号基本列的字段. 闭包定理 `snd²` 对一切深度只有一个证明, 只有一个参数, 不按深度加前提.

一步定理与这一站新用到的字段:
- `kstep` 的后继步用到 `Cl.a = v` (上一格的格世界) 与 `Cl.av = sum-fst v d₀`;
- 状态比较用到 `cv` 保持值 (`cv≤`, `≤cv`) 与格输出在 `z⊲`、`κ₀` 两条路径上值相同 (`cohW`).

## 5 审计

- `importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRule --only OCF.Align.TLOpsW --only OCF.Align.SumOne --only OCF.Align.BrwMid --only OCF.Align.LayerTr --only OCF.Align.CvFold --only OCF.Align.CvHigh --only OCF.Align.CvLayer --only OCF.Align.NoCumLit --only OCF.Align.L1Val --only OCF.Align.DVal --only OCF.Align.HtGen --only OCF.Align.HtFeed --only OCF.Align.HtCross --only OCF.Align.KVal --only OCF.Align.KNest OCF.Align.KNest2`: 闭包 39 个模块 (本地 29, 库 10), 禁用表命中 0, `--only` 之外 0, OK. 编译器保证不引用记号; 不说明定义没有受记号启发.
- `depslice.py` (语法级近似): 下表四个根的记号模块块数都是 0, 别处记号词 0. 正对照 `Om1HnAccept:label-term₀` 到达 1188 块, 记号模块 92 块, 别处 58.

| 根 | 到达块数 |
|---|---|
| `KNest2Glue:kstep` | 215 |
| `KNest2Sound:snd²` | 306 |
| `KNest2Sound:nest-rel²` | 45 |
| `KNest2Sound:nest-mono²` | 311 |

- agda 代码行 (代码块内非空): KNest2 4, KNest2Glue 109, KNest2Sound 67, 合计 180.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KNest2 where

open import OCF.Align.KNest2Glue using (d0; Wk; CellStep; KStep²; module Side; kstep) public
open import OCF.Align.KNest2Sound using (_⊑²⟨_,_⟩_; snd²; nest-diag²; nest-rel²; nest-mono²) public
```
