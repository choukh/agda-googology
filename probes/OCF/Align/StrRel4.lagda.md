# 结构关系, 第四轮: 对齐作为数据, 一格可靠: 入口

> **判决: PARTIAL.** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 没有改任何已有文件.
>
> 1. **一格的比较, 对齐作为数据时成立 (定理, 无参数).** [StrRel4Walk](StrRel4Walk.lagda.md) **`cellᴬˡ : CellStepᴬˡ`**. `CellStepᴬˡ` 是 `KNest2Glue.CellStep` 把三条值前提 (领先量 $\mathrm{Adm}(a,a';W,W')$、起点可比、$W\le W'$) 换成一个对齐推导 `Al`, 结论原样. 只用分支的交叉前提 `SX u u′`; **不用 `SX u u`, `SX u′ u′`, 不用 "树世界可比"**. 证明对 `Al` 归纳 (`walk`), 五个构造子各对应 `Walk` 在一边或两边的一次展开.
> 2. **对齐由结构关系生成 (定理).** [StrRel4Gen](StrRel4Gen.lagda.md) **`gen`**: 两棵第 0 层树由 $\sqsubseteq^{\mathsf O}$ 相关 (七个构造子, 含传递), 起点 $b\le b'$, 末端有领先量 ⇒ 两条 `sum-fst` 路径对齐. [StrRel4Pr](StrRel4Pr.lagda.md) **`genᴾ`**: 加上部分和规则 `pr` 的 $\sqsubseteq^{\mathsf P}$ 同样成立. 于是 `kstep` 里的两种格都有对齐:
>    - 第 $n+1$ 格 (**`alSucc`**, **`alSuccᴾ`**): 上一格两边输出结构相关, 起点可比;
>    - 第 0 格 (**`alZero`**, **`alZeroᴾ`**): 前一段 $q_0, q_0'$ 已对齐, 状态第 0 层累计结构相关, 运行世界可比.
> 3. **对齐的代数 (定理).** 传递 `Al-tr` (领先量复合 `adm-comp` 用左消去), 拼接 `cat`, 右边延长 `ext`, 换格世界 `Al-map`.
> 4. **`CellStep` 原样 (值前提) 与嵌套 `nκ` 的无条件可靠性: 未走通.** 第一个障碍见 §2: 下一格的对齐要上一格的输出**结构**相关, 而现在分支与状态的前提只给值. 不是否定.
> 5. **"树世界可比" 一条.** 在一格之内可以去掉 (定理: `cellᴬˡ` 没有这条前提, 它的作用 "选对齐方式" 由 `Al` 推导承担). 在 `KStep` 一级: 第 0 格要 $q_0$ 的对齐 (`alZero` 的前提), 这要求语义对路径 $q$ 带对齐, 而不是 `OutLeᴬ` 的 "一切 $q,q'$"; 这一步未做, 所以在 `KStep` 一级**未走通**, 不是否定.

## 1 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `Al` (五个构造子) | StrRel4Walk | 两条路径的对齐, 每对位置带 $c\le c'$ 与到格世界的领先量 | 定义 |
| **`walk`** | StrRel4Walk | 对齐的两次 `Walk` 输出在 `κ₀` 上对一切 $e\le e'$ 可比 | 条件定理 (`SX u u′`, `Ok`, `Cxᴵ`, `Ld`) |
| **`cellᴬˡ : CellStepᴬˡ`** | StrRel4Walk | `CellStep` 的对齐版 | 定理 (`CellStepᴬˡ` 里的前提是陈述的一部分, 没有外加参数) |
| `vs`, `adm-back`, `adm-comp`, `Tail` | StrRel4Gen | $\sqsubseteq^{\mathsf O}$ 值可靠; 领先量往回推, 复合; 极限尾巴 | 定理 |
| `Al-map`, **`Al-tr`**, `lg-tr`, `lgsf`, `ext`, **`cat`** | StrRel4Gen | 对齐的运算; 长度证据沿 `sum-fst` 回到起点 | 定理 |
| **`gen`**, **`alSucc`**, **`alZero`** | StrRel4Gen | 由 $\sqsubseteq^{\mathsf O}$ 生成对齐; 两种格 | 定理 |
| `_⊑ᴾ_`, `fromᴼ`, `vsᴾ` | StrRel4Pr | 加部分和规则; 嵌入; 值可靠 | 定义 / 定理 |
| **`genᴾ`**, **`alSuccᴾ`**, **`alZeroᴾ`** | StrRel4Pr | 同上, 对 $\sqsubseteq^{\mathsf P}$ | 定理 |
| `CellStep` (值前提), 结构的 `kstep`/`snd²` | — | 见 §2 | 未走通 |

**否定.** 本轮没有新的否定定理. `Al` 不收 "左边极限对右边一段前缀", 依据是已有的 `KNestAdm.¬adm-end`; 值前提不能代替对齐, 依据是已有的 `StrRel2Neg.phead→LPO` (它否定的是 "由值求对应位置", `CellStep` 原样是否可证, 本轮没有定理).

**有限测试.** 无.

## 2 第一个障碍: 格的输出要结构相关 (判断)

`kstep` 对格号归纳. 用本轮的结果, 第 $n$ 格对齐 ⇒ 第 $n$ 格输出的值可比 (`cellᴬˡ`); 要推到第 $n+1$ 格对齐 (`alSuccᴾ`), 还缺: **第 $n$ 格两边的第 0 层输出 $d_n\sqsubseteq^{\mathsf P}d'_n$**. 这是 "结构版的 `walk`":

1. **形状上没有障碍.** `walk` 的五句改成结构结论: `aS` ↦ `z0`, `aP` ↦ `sq`, `aR`/`aRL` ↦ `pr` (本轮加上它, 并证明 `genᴾ` 照样成立), `aL` ↦ `sq` 加 `lm`. 判断: 这部分是机械的 (约 150 行).
2. **分支的前提要给结构.** `SX` 是 `OutLeᴬ`, 只给值. 要一个结构的 `OutLe` (输出第 0 层 $\sqsubseteq^{\mathsf P}$). `n1` 分支的第 0 层输出是 $\omega\cdot(1⨾\mathrm{dz}\,Y)$, 所以**状态也要结构相关** ($\mathrm{dz}\,Y\sqsubseteq^{\mathsf P}\mathrm{dz}\,Y'$), 而不是 `Cxᴵ` 的值. 对 `⊕` 封闭 (`sq`).
3. **换世界 `cv` (格与格之间).** `cv q Y` 在第 0 层读 $Y$ 的路径由 `cmpF` 算出, 两边不一定字面相同. 要结构版的路径一致 (`StrRel3` 缺件 3). 判断: 照 `KValSem` 改写, 约 150 行; 没有否定的迹象.
4. **第 0 格的前一段 $q_0$.** `alZeroᴾ` 要 $q_0\sim q_0'$ 的对齐. $q_0$ 是外层 `Walk` 在对应位置剩下的路径 (`⊲-tr (suc self) bV`). 所以语义 (`OutLe`) 要对 $q$ 带对齐, `walk` 要同时带着 "剩下的路径" 的对齐 (后缀的对齐; `Al` 是从起点量的, 后缀要另一个从前面延长的关系, 或一条 "对齐的后缀仍对齐" 的引理). 这是 `StrRel3` 缺件 2. 判断: 这是剩下的主要工作.

估计 (判断): 1+2+3 约 400 到 600 行, 4 约 300 到 500 行.

## 3 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `Al` 的五个构造子 | 各对应 `Walk` 在一边或两边的一次展开 (`self`, `suc`, `lim`) | **树逼的** (折叠的形状) |
| `Al` 不收左边极限截断 | `KNestAdm.¬adm-end` | **树逼的** (有否定支撑) |
| 每对位置带 $c\le c'$ 与 $\mathrm{Adm}(c,c';W,W')$ | `SX` 的前提 ($c\le c'$) 与 `Cxᴬ` 的领先量 | **树逼的** |
| `Ld` (状态把格世界上的领先量传到回灌层) | $\ell(Y\oplus\Delta)=\mathrm{sum}(\ell Y)(d_0\Delta)$, `adv-sum` | **树逼的** (计算) |
| `pr` | `aR`/`aRL` 的结构输出 | **树逼的** |
| `gen` 的传递一句: 中间格世界取 $\mathrm{sum}\,b\,y\oplus\delta$ | 两段领先量要共用同一个 $\delta$ | 树侧, 计算 |

**归类: 提供信息.** 没有新构造子或节点字段, 没有改树、折叠, 没有 `Lab`, 没有记号. 一步定理: `walk` 对一切对齐推导, `gen`/`genᴾ` 对一切结构推导, 都只有一个证明, 不按深度或阶段加前提. 这一站新用到的字段: `Walk` 极限一句的长度证据 (`stp`, `wl`, 由 `Lg-sum` 给出, `lgsf` 说它沿 `sum-fst` 回到起点), `WRp` 的状态链.

缺陷是否变深: 没有. 本轮把 "对齐" 从一个要判定的值问题 (`phead→LPO`) 变成推导里的数据, 并说明数据从哪里来 (结构关系). 剩下的是把值的语义换成结构的语义 (§2), 是 `StrRel3` 已列的方向, 没有新的翻译.

## 4 审计与账

- 编译: 删掉本组 `StrRel4*` 的 `.agdai` 后从头编译入口, 退出码 0. 无禁用构造, 不出现 `Funext`.
- 导入闭包: 用 [KNest2](KNest2.lagda.md) 审计的 `--only` (StrRel 的那张表加 `BrwMid`, `LayerTr`, `NoCumLit`, `L1Val`, `DVal`): 闭包 51 个模块 (本地 41, 库 10), 禁用表命中 0, `--only` 之外 0, OK. 只用 [StrRel](StrRel.lagda.md) 的那张表: 禁用表命中 0, `--only` 之外 10 (`BrwMidZero`, `NoCumLit`, `LayerTr*`, `DValCanon`, `DValTree`, `L1ValBase`), 都经 `KNestAdm`/`KNestSound`/`KValSound` 进来; `KNest2` 自身在这张表下同样 FAIL, 是继承的, 不是本轮新增. 闭包里有 `DValCanon` (经 `KValSound` 的 `Sd`, `Ok`; `CellStep` 本来就用它们陈述). 编译器保证不引用记号; 不说明定义没有受记号启发.
- `depslice.py` (语法级近似): 根 `StrRel4Walk:walk` 197 块, `cellᴬˡ` 202, `StrRel4Gen:gen` 83, `alSucc` 85, `alZero` 85, `StrRel4Pr:genᴾ` 83, `alZeroᴾ` 85; 记号模块块数都是 0, 别处记号词 0. 正对照 `Om1HnAccept:label-term₀`: 1188 块, 记号模块 92, 别处 58.
- 代码行 (代码块内非空): StrRel4Walk 111, StrRel4Gen 147, StrRel4Pr 84, 入口 5, 合计 347.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel4 where

open import OCF.Align.StrRel4Walk using (Al; aS; aP; aR; aRL; aL; module Go; CellStepᴬˡ; cellᴬˡ) public
open import OCF.Align.StrRel4Gen using (vs; adm-back; adm-comp; Al-map; Al-tr; lgsf; ext; cat; gen; alSucc; alZero) public
open import OCF.Align.StrRel4Pr using (_⊑ᴾ_; fromᴼ; vsᴾ; genᴾ; alSuccᴾ; alZeroᴾ) public
```
