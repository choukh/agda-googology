# 非选择性的增量搬运: 命题 W′ 证或否

> 不含记号. 入口. 对象: [ClosedTermReview](../../Survey/ClosedTermReview.md) §1.2 的命题 W′ (非选择性一侧) 与 [TelW](TelW.lagda.md) 留下的 "由外层界决定的界族". 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延. 定义不读记号, 没有改任何已有文件.
>
> **判决: PARTIAL. 望远镜版 (D1) 否定 (编译过的一般定理, 结论是 $\bot$); 积世界版没有证也没有否, 缩成槽族上的一个类型 (`UniTrNeg.Open`), 写 "未走通".**
>
> 1. **W′ 的形式陈述 (定义, 定理).** `UniTrBase.W′.UniTr`: 对一切下标 $i_0,i$ 的 `tr i₀ i : X i₀ → X i`, 在对角上忠实 (`faith`), 处处合法 (`legal`); "不判定" 不是字段, 否定的形式是 "`UniTr` 推出判定". 积世界上的非选择性回灌 (`Slot.NonSel`: 分量 $i_0$ 的槽是 "旧界 ⊞ δ", 一切分量只增, 保合法, 没有 "别处不变") 与 `UniTr` **互推** (`toNS`, `fromNS`). 所以积世界版 W′ 只是**槽族** (被升高的界的类型族) 的性质. `Lev (Ωtop S)` 的后继分量是实例 (`LevSlot`: 槽就是种类 `(hs c , inj₂ tt)` 的界, `lev-bd` 是 `refl`; `liftR-at`, `liftR-≤`, `liftR-lg`).
> 2. **W 与 W′ 的关系 (定理).** W′ 加 "别处为零" 的律推出弱判定 (`Off.off→wdec`); 判定恰好来自 `off`. 对一切增量族一般的构造推出下标相等**可判定** (`Generic.generic→dec`, 族 $(i_0\equiv i)\uplus\top$): 能成立的构造必须用到槽族本身.
> 3. **积世界版: 自然的两类被否定, 一类被构造 (定理).**
>    - 顶对齐 (增量的新种类翻成目标分量的新种类, 新坐标倒译): **`no-faithful-back`**, 对一切 `S` 与一切倒译 $B$: $B$ 在旧部分上忠实 ($B(\mathrm{up}\,c)\approx c$) 则翻译结果不合法. `DiagK4Neg.¬Lg-Tr₀` 是它的实例 (`¬Lg-Tr₀′`, 用 `back₀-up`); 常值倒译合法而不忠实 (`Lg-constB`, `const-unfaithful`).
>    - 往下搬: **`lossy-pred`**, 从分量 `hs c` 的槽到分量 $c$ 的槽的任何映射都没有左逆 (审查 "必有损" 的定理形式).
>    - 底对齐 (往上搬进同一种类的副本): 有见证 $i_0\lhd i$ 时沿见证的嵌入合法且在 `hself` 上是恒等 (`emb⊲`, `Lg-emb⊲`); 有**选择子** (每对下标给 "见证或放弃", 对角给 `hself`) 就有 `UniTr` (`sel→unitr`); 相等可判定时选择子存在 (`dec→sel`).
>    - 所以积世界版 W′ 在 `Lev` 上等于: 不判定地给出选择子的替代品. 卡点是下面的 `Open-taboo` / `Open-build`.
> 4. **望远镜版 (D1): 否定 (定理).** `UniTrTel.no-outer-lift`, 对一切 `S`: 内层层号比外层高一级 (`Lv (ls ℓ) = step (Lv ℓ)`) 时, 由外层界决定的内层界族 $F$ 若单调 (`Mono`) 且合法, 就**不能**对一切合法内层增量忠实 (`Faith`, 相干世界里格 $F\,b\boxplus\delta'$ 在 $F\,b'$ 之下). 结论是 $\bot$, 有判定也没有用: 内层增量的类型比外层界大, 经外层界升高是 Burali-Forti 的形状 (`no-1⊞`). `tel-no-lift` 是 `TelWTy` 望远镜上的同一条. 前提可满足: `upLift` 单调合法, 对有限增量忠实 (`faith-fin`).
> 5. **两版结论不同.** D1 版的障碍是**类型**: 增量必须穿过更小的外层界, 一切 $F$ 都不行. 积世界版没有这个瓶颈 (增量直接落在分量 $i_0$ 的槽里), 障碍只是**下标不可判定**: 下标可判定时 `UniTr` 存在 (`Inst.decU`, `Sel.dec→sel`), 在 `Lev` 形的槽族上也是 (`FinInst.finU`, 下标 ℕ).

## W′ 的形式陈述 (原文)

```text
module W′ (I : Set) (X : I → Set) (LgX : ∀ {i} → X i → Set) (_≃_ : ∀ {i} → X i → X i → Set) where
  record UniTr : Set where
    field
      tr    : (i₀ i : I) → X i₀ → X i                      -- 对一切分量定义
      faith : ∀ i₀ δ → LgX δ → tr i₀ i₀ δ ≃ δ               -- 在当前分支 i₀ 上忠实
      legal : ∀ i₀ i δ → LgX δ → LgX (tr i₀ i δ)           -- 处处合法 (回灌后的世界合法)
```

积世界版取 `Slot I G`: `X i = HB (G i)`, `LgX = LgB`, `_≃_ = _≈_` (互模拟); 回灌是 `raiseU`: 分量 $i$ 的槽 $b_i\mapsto b_i\boxplus\mathrm{tr}_{i_0\to i}\,\delta$. **单调** (别的分量只增) 由 `⊞-fst` 自动给出 (`toNS` 的 `R-≤`), 合法由 `legal` 与 `Lg-⊞` 给出. 字面版 `SlotL` 取 `x ≃ δ = ∀ w → δ ⊲[w] x`, 这时回灌的格 $b_{i_0}\boxplus\delta$ 字面有界 (`toNSˡ-cell`), 正是 `HtTowerFFold` 的格要的.

**"不判定" 的写法.** 它不是 `tr` 的字段 (任何 `tr` 都经 $\Sigma_i X\,i$ 分解, 限制形状就是稻草人). 否定方向的陈述是 "`UniTr` ⇒ 下标相等的 (弱) 判定" (`Open-taboo`); 构造方向是 "写出 `UniTr`, 不假设判定" (`Open-build`).

**忠于审查原文的理由.** (i) "tr 要对一切 $i$ 定义": 字段 `tr i₀ i` 对一切 $i$. (ii) "在 $i_0$ 处忠实": `faith` 只在对角上要求, 不要求别处忠实 (审查的原文只要求当前分支; `DiagK4` 判决 4 的 "在对得上处忠实" 更强, 它的顶对齐形式由 `no-faithful-back` 否定). (iii) "在别的分量上单调": 回灌是 "旧界 ⊞ 增量", 世界只增 (`R-≤`), 这是 `growL′`, `rais`, `RunM` 的同一形状; `NonSel` 允许任意形状的 `R`, 与 `UniTr` 等价, 所以不因 "⊞" 的形状丢掉情形. (iv) "不判定": 见上. (v) "回灌的格有界": `SlotL.toNSˡ-cell`.

**故意不覆盖的.** 被升高的界不是分量的 `step` 新种类的槽 (分量不是 `step` 形, 如 `Lev (Ωtop S)` 在极限坐标处的分量; 或升高的是分量内部更低的种类); `NonSel` 对 `R` 的形状不设限, 所以只要被升高的是 `step` 的槽, 任意世界操作都在覆盖之内; 只在折叠实际发出的增量上忠实 (那要先刻画读回); `tr` 对 $i_0$ 的单调性 (折叠在一个结点的各坐标上分别回灌, 输出要对坐标单调; 没有试, 判断: 可能是新的否定来源); 槽不是 `step` 的新种类的那些种类 (极限分量的内部种类).

## 已有的 tr 都是特例

| tr | 满足 | 不满足 | 依据 |
|---|---|---|---|
| `embL` / `growL′` (一切分量接同一个 $H_0$ 增量) | 合法, 单调, 不判定 | 忠实 (只在槽为 $H_0$ 的分量上: `growL′-faith₀`; `κ₂` 处不: `growL′-¬faith₁`) | `DiagK3Grow.at-lev`, `ChainZNeg.no-Ω-cell` |
| `back₀` (顶对齐, 对不上的种类取底分支) | 旧部分上忠实 (`back₀-up`), 不判定 | 合法 | `no-faithful-back` ⇒ `¬Lg-Tr₀′` |
| 常值倒译 | 合法, 单调, 不判定 | 忠实 | `Lg-constB`, `const-unfaithful` |
| 任何往下搬的映射 | — | 无左逆 | `lossy-pred`, `lossy-Lev` |
| 选择性 `upd` (`DiagKLev.UpdS`) | 忠实, 合法, 单调 | 不判定 (加 `off` 推出弱判定) | `Off.off→wdec`, `DiagKLev.upd→wdec` |
| 底对齐 `emb⊲` + 选择子 | 忠实, 合法 | 不判定 (选择子就是判定的替代品) | `sel→unitr`, `dec→sel` |
| D1: 由外层界决定的界族 | 单调, 合法 (`upLift`) | 对一切合法增量忠实 | `no-outer-lift`, `tel-no-lift` |

## 定理表

| 名字 | 文件 | 一句话 | 档 |
|---|---|---|---|
| `_≈_`, `≈-rf`, `≈-tr`, `hz⊞`, `⊞-≈`, `≈-hs`, `up-≈` | UniTrBase | 互模拟与它的律 | 定理 |
| `inv-hs`, `inv-hl`, `inv-hΩ`, `hs-inj` | UniTrBase | 第一位置的反演 | 定理 |
| **`no-1⊞`** | UniTrBase | $Y\boxplus(1\boxplus Z)$ 不是 $Z$ 的第一位置 | 定理 |
| `L≈`, `hs≈⊲`, `≈hs⊲` | UniTrBase | 与 $X$ 互模拟的树之后继不是 $X$ 的第一位置 | 定理 |
| `W′.UniTr` | UniTrBase | W′ 的一般形式 | 定义 |
| `Off.off→wdec` | UniTrBase | W′ + `off` ⇒ 弱判定 | 定理 (条件) |
| `Inst.decU`, `decU-off`, `Const.constU`, `FinInst.finU` | UniTrBase | 前提可满足: 下标可判定 (Hedberg; 也满足 `off`) / 常值族 / `Lev` 形槽族配下标 ℕ | 定理 |
| **`Generic.generic→dec`** | UniTrBase | 对一切族一般的构造 ⇒ 相等可判定 | 定理 (否定, 范围: 对族一般) |
| `Slot.NonSel`, **`toNS`**, **`From.fromNS`** | UniTrBase | 积世界上的非选择性回灌 ⟺ `UniTr` | 定理 |
| `SlotL.toNSˡ-cell`, `toNSˡ-≤`, `toNSˡ-lg` | UniTrBase | 字面版: 回灌的格字面有界 | 定理 |
| `LevSlot.lev-bd`, `liftR-at`, `liftR-≤`, `liftR-lg` | UniTrBase | 实例: `Lev (Ωtop S)` 的后继分量 | 定理 |
| **`no-faithful-back`** | UniTrNeg | 一切 `S`, 一切倒译: 旧部分上忠实 ⇒ 顶对齐翻译不合法 | 定理 (否定, 范围: 顶对齐) |
| `back₀-up`, **`¬Lg-Tr₀′`** | UniTrNeg | `DiagK4Neg.¬Lg-Tr₀` 作为推论 | 定理 |
| `Lg-constB`, `const-unfaithful` | UniTrNeg | 常值倒译合法, 不忠实 | 定理 |
| **`lossy-pred`**, `lossy-Lev` | UniTrNeg | 往前一个分量搬没有左逆 | 定理 (否定) |
| `emb⊲`, `Lg-emb⊲` | UniTrNeg | 沿见证往上嵌入, 合法 | 定理 |
| `Sel.Selector`, **`sel→unitr`**, `dec→sel` | UniTrNeg | 选择子 ⇒ `UniTr`; 可判定 ⇒ 选择子 | 定理 (条件) |
| `growL′-faith₀`, `growL′-¬faith₁` | UniTrNeg | `growL′` 在 W′ 里的位置 | 定理 (重述) |
| `Open.Open-taboo`, `Open.Open-build` | UniTrNeg | 开放点的两个方向 | 定义 (未证未否) |
| `Mono`, `OuterLift`, `Faith` | UniTrTel | D1 的界族与忠实 | 定义 |
| `diag`, `Lg-diag` | UniTrTel | 对角增量合法 | 定理 |
| **`no-outer-lift`** | UniTrTel | 一切 `S`: 单调合法的外层界族不能对一切合法内层增量忠实 | 定理 (否定, 结论 $\bot$) |
| `upLift`, `up-fin`, `faith-fin` | UniTrTel | 前提可满足 | 定理 |
| **`tel-no-lift`** | UniTrTel | 同一否定在 `TelWTy` 的望远镜上 | 定理 (否定) |
| "积世界版 W′ 在 `Lev` 槽族上推出弱判定" | — | `Open-taboo` | 未走通 |
| "`Open-build` 不判定地有居留" | — | | 未走通 |

## 前提可满足

- `no-faithful-back`: 前提 "旧部分上忠实" 由 `back₀` 满足 (`back₀-up`); "$B(\Omega_{\mathrm{top}})$ 合法" 由 `back₀` 满足 (值是 `hz`); 合法世界 `azero`. 前提合起来可满足 (所以结论是 "翻译不合法" 而不是空真): `¬Lg-Tr₀′` 就是这个实例.
- `lossy-pred`: 无前提 (对一切映射).
- `Off.off→wdec`: `UniTr` 与 `off` 合起来由 `decU` 满足 (`decU-off`, 下标可判定时); 观察量与 `DiagKLev.tst` 同法 (`≃` 取 `≡` 时取 "是不是零点").
- `generic→dec`: `UniTr` 在可判定下标上存在 (`decU`), 所以前提不矛盾; 结论在那里本来就成立.
- `sel→unitr`: 选择子在可判定下标上存在 (`dec→sel`); 在 `HB S` 上一般不知道.
- `no-outer-lift`: `Mono` 与合法由 `upLift` 满足; `Faith` 的形状由 `upLift` 对一切有限增量满足 (`faith-fin`); 相干世界 $(w, b')$ 用 $b'\lhd b'$ (`hself`). 矛盾来自 "对一切合法增量".
- `tel-no-lift`: 同上, 望远镜 `ls ℓ ∷ ℓ ∷ rest` 对一切 `ℓ`, `rest`.

## 卡点

积世界版 W′ 在 `Lev (Ωtop S)` 上: `Open-build = UniTr` (槽族 `c ↦ HB (Lev (up c))`, 忠实取互模拟), `Open-taboo = UniTr → ∀ c c′ → ¬ (c ≡ c′) ⊎ ¬ ¬ (c ≡ c′)`. 已知 (定理): 换成可判定下标 (ℕ), 同形的 `UniTr` 有居留 (`FinInst.finU`); 对族一般的构造是判定; 顶对齐的忠实翻译不合法; 底对齐要见证. 两个方向都没有做到, 原因 (判断, 纸面):

- **否定方向.** `generic→dec` 与 `off→wdec` 的证明都用一个**布尔观察量**在对角与别处分开两个值. 积世界版里, 别处的输出只受 "合法" 约束, 而任何合法的树都可以放进槽 (例如按增量的任意有限信息输出 `hz` 或 `hs hz`), 所以合法性逼不出别处的有限可观察的损失; 合法性逼出的损失 (`no-faithful-back`, `lossy-pred`) 是对一切坐标的 (无穷的) 不忠实, 布尔观察量看不到. 要从 `UniTr` 抽出判定, 需要一个不经有限观察的论证 (例如连续性), 本轮没有找到能在 Agda 里写出的形式.
- **构造方向.** 结构上 "拉链" 两个高度 (头构造子不同就放弃, 函数分支逐点) 不判定, 在对角上是互模拟意义的恒等; 但它在 `hs` 对 `hs` 处是顶对齐, 新坐标要倒译, `no-faithful-back` 说忠实的倒译不合法, 而倒译只在 "两边处处对上" 时才该忠实, 那是无穷的条件. 底对齐要见证 (`emb⊲`), 给见证就是选择子.
- **注 (判断).** 在经典逻辑下 `Open-build` 成立 (按相等判定选择), 所以在 `--safe --without-K` 里不可能有 `¬ Open-build` 的证明; 否定方向只能是 `Open-taboo` 这样的禁忌.

本轮没有写成否定, 只能写 "未走通". 积世界版的下一步若要否定, 最可能的来源是 "故意不覆盖" 里的第三条 (对 $i_0$ 单调), 那要先从折叠里读出这条要求 (判断, 没有试).

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `UniTr`, `NonSel` 与互推 | 审查的命题 W′ 的文字; 回灌形状取 `HtTowerFFold`/`TelWTy.rais` | 树逼出 (陈述) |
| 互模拟 `≈` | 不用外延时 "忠实" 只能到这一步 | 树逼出 |
| `no-faithful-back` | 把 `DiagK4Neg.¬Lg-Tr₀` 从 `back₀` 推广到一切倒译 | 否定形状 (提供信息) |
| `emb⊲`, `Selector` | 底对齐的见证 | 树逼出 (正面, 定位判定) |
| `OuterLift`, `Faith`, `no-outer-lift` | `TelW` 第一个障碍留下的候选 | 否定形状 (提供信息) |

没有字段读自记号的基本列规则; 没有新构造子, 没有闭包定理, 没有验收, 没有标签. 按 `AGENTS.md` 归类: **摆脱侧, 提供信息**. 加深翻译的三个标志都没有.

## 审计

- **从头编译** (删去本路四个 `.agdai`, 依赖用已有接口, 堆上限 6G): 入口退出码 0, 3.3 秒, 常驻峰值约 0.55G.
- **禁用构造**: 四个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY`, 无 `trustMe`, 无 `REWRITE`, 无函数外延; 都带 `--safe --without-K --lossy-unification`. Hedberg 来自 stdlib 的 `Axiom.UniquenessOfIdentityProofs` (`--safe` 模块, 是定理不是公理).
- **导入闭包** (`importclosure.py`, `--only` 表同 `ChainZ` 加 `OCF.Align.TelW`, `OCF.Align.ClosedReview1`, `OCF.Align.UniTr`): 入口 45 个模块 (本地 33), `UniTrBase` 16 (本地 5), `UniTrNeg` 39 (本地 28), `UniTrTel` 21 (本地 9); 都是退出码 0, 禁用表 0, `--only` 之外 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `no-faithful-back` 68/0/0, `¬Lg-Tr₀′` 85/0/0, `sel→unitr` 80/0/0, `lossy-Lev` 71/0/0, `no-outer-lift` 62/0/0, `tel-no-lift` 109/0/0, `toNS` 64/0/0, `generic→dec` 12/0/0, `liftR-lg` 80/0/0, `finU` 80/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用.
- **文件级代码行** (代码块里非空非注释行): `UniTrBase` 235, `UniTrNeg` 112, `UniTrTel` 57, 入口 5; 共 409.

## 文件

| 文件 | 内容 |
|---|---|
| [UniTrBase](UniTrBase.lagda.md) | 互模拟, 第一位置的反演, `no-1⊞`, `hs≈⊲`; W′ 的一般形式; `Off`; `Generic`; `Slot`/`SlotL`/`LevSlot`; 可满足的实例 |
| [UniTrNeg](UniTrNeg.lagda.md) | 积世界版: `no-faithful-back`, `lossy-pred`, `emb⊲`/`Selector`, `growL′` 的位置, 开放点 `Open` |
| [UniTrTel](UniTrTel.lagda.md) | 望远镜版: `no-outer-lift`, `tel-no-lift`, 可满足的实例 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniTr where

open import OCF.Align.UniTrBase public
open import OCF.Align.UniTrNeg public
open import OCF.Align.UniTrTel public
```
