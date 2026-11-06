# 树的语言: 判据 → 定义 (构造一路, 入口与判决)

> 不含记号. 作者选定原话: "树的语言: 判据→定义". 本路前缀 `TreeLang` (构造), 与否定一路 `NegTreeLang` 配对, 共用接口 [TreeLangIf](TreeLangIf.lagda.md) ("接口定稿 2026-11-05 20:27 (首次编译通过)", 变更记录: 无). 已有的 [TreeLangFeed](TreeLangFeed.lagda.md) 是路线审查的旧实验, 与本路无关, 未改. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> **判决: PARTIAL.** 判据给出了两处正面指引 (定理), 一处定死到级集合, 一处定死到律的定义域之内; 两处都剩下写明的自由度. 没有新闭项, 没有值的定理.
>
> 1. **层的生成规则 ([TreeLangLv](TreeLangLv.lagda.md)).** 判据 `LvCrit` (`base0`, `feed`, `inherit`, `sub`) 推出: 满足它的任一规则, 第 $c$ 层含 `Lev c` 的一切级 (`least`); `Lev` 自己满足 (`LevC`), 所以**在级集合上 `Lev` 是最小的合法规则**; 加字面上界 `LvUpper`, 级集合与 `Lev` **相等** (`exact→`, `exact←`). 在一次封闭的层号 `LH` 上同样: `LFReTy.Lv` 是满足 `LvCritL` 的最小规则, 加上界唯一 (`leastL`, `exactL→`, `exactL←`); 照 `Lev` 的样子搬过去而不加 `step (Lv k)` 的规则不满足 `cof` (`no-crit⁻`).
> 2. **升界 (C6 的下标, [TreeLangRaise](TreeLangRaise.lagda.md)).** 律 `set`/`keep` 推出: 定义域里的一对成员的键必须弱可判定相等 (`ev→wdec`); 键可判定时, 合法升界在读数上唯一, 就是按判定的点更新 (`shape`, `unique`). `Lev` 的 Ω-并以裸坐标为下标, 其积世界上的升界推出分离子 (`sup-bare→Sep`); 以 "同一合法界之下的字面位置" 为下标, 合法升界存在且唯一 (`Pos.posR`, `Pos.pos-unique`). 推出的形状是 "Ω-并只取有界坐标".
>
> **对纲领与目标.** 纲领 1–4 不受影响: 只有种类结构上的规则与定理, 不读记号, 不比较不带公共上界的下标, 无公理. 目标 "让树自足": 这是第一次**由判据推出**定义的形状, 而不是先猜后验. 具体是: `Lev` 的三行 (`step` 加一个级, `sup` 取并) 与 `Lv` 的 `lΩ` 行多出的 `step (Lv k)`, 都是判据逼出的最小内容; 升界的下标必须是有界位置. 但 (i) 正面判据 `feed`, `inherit`, `cof` 本身是选择 (下面翻译账), 不是定理; (ii) 判据只定级集合与律的定义域, 不定重数, 世界的其余结构, 值; (iii) 本路没有推出 C6 的完整解 (跨级读数的搬运, 证据放哪里, 未定).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLang where

import OCF.Align.TreeLangIf
import OCF.Align.TreeLangLv
import OCF.Align.TreeLangRaise
```

## §1 判据接口 (摘要)

见 [TreeLangIf](TreeLangIf.lagda.md) 文件头的表. 三种候选: 层的生成规则 `LvRule S B` (层号 `HB S`), `LvRuleL` (层号 `LH`), 升界 `Raise F`. 律的定义域: `inherit` 带字面子项证据, `set`/`keep` 带 `Ev` 证据; 没有对裸下标的比较律.

## §2 形状定理与实例

| 定理 | 陈述 | 文件 | 档 |
|---|---|---|---|
| `no-self`, `no-down`, `no-selfᴸ` | 满足 `coord` 的任一规则: 第 $c$ 层没有级 $c$; 第 $c$ 层的值不能无损写进它的任一级 $y$ | TreeLangLv | 定理 |
| `least` | `LvCrit R` ⇒ `Lev c` 的每个级都在 `R` 的第 $c$ 层 | TreeLangLv | 定理 |
| `LevR`, `LevC`, `LevU` | `Lev` 满足 `LvCrit`, `LvUpper` | TreeLangLv | 定理 (实例) |
| `exact→`, `exact←` | `LvCrit R`, `LvUpper R` ⇒ `R` 与 `Lev` 的级集合相等 | TreeLangLv | 定理 |
| `R⁺`, `C⁺`, `extra⁺`, `no-extra-Lev`, `not-upper⁺` | 不加上界时有别的合法规则, 在 `hl (λ _ → 0)` 处多一个级 | TreeLangLv | 定理 (自由度) |
| `copies-Lev` | `Lev (hl (λ _ → 1))` 里级 $0$ 有不同的两份 | TreeLangLv | 定理 (自由度: 重数) |
| `LvRL`, `LvCL`, `LvUL`, `leastL`, `exactL→`, `exactL←` | `LH` 上: `Lv` 是满足 `LvCritL` 的最小规则, 加上界唯一 | TreeLangLv | 定理 |
| `no-cof⁻`, `no-crit⁻` | 照 `Lev` 写在 `LH` 上的 `R⁻` 不满足 `cof` | TreeLangLv | 定理 |
| `ev→wdec`, `bare→wdec` | 合法升界 ⇒ 定义域里键的弱判定 | TreeLangRaise | 定理 |
| `shape`, `unique`, `unique¬¬` | 键可判定时合法升界在读数上唯一 (按判定的点更新) | TreeLangRaise | 定理 |
| `bare→Sep`, `sup-bare→Sep` | `Lev` 的裸坐标积世界上的合法升界 ⇒ 分离子 | TreeLangRaise | 定理 |
| `Pos.posR`, `Pos.pos-dec`, `Pos.pos-unique`, `posInst` | 合法界之下的字面位置为下标: 合法升界存在, 唯一 | TreeLangRaise | 定理 (实例) |

**判据推不出唯一形状之处 (自由度), 以及是否需要新判据.**

1. **级集合之外的上界.** 没有 `LvUpper` 时 `R⁺` 合法 (定理). `LvUpper` 是 "只认字面证据" 的选择; 它挑掉的级, 读法上是 "值为 0 的层号却有第 1 层的种类" (判断). 信号: 若不想把 `LvUpper` 当选择, 需要一条关于值的判据 (层号的值与它的级之间), 今天没有.
2. **重数.** 判据只看级集合; `Lev` 有拷贝 (`copies-Lev`). 拷贝在别处是墙的来源 (`CohWNeg` 一族, `ColimA.noCrossA`; 判断档的引用). 信号: 需要一条关于拷贝的判据 (要么禁止, 要么规定拷贝的相干), 今天没有.
3. **世界.** `LvRule` 不看世界; `Raise` 的判据说世界的积不能以裸坐标为下标 (`sup-bare→Sep`), 位置为下标可以 (`posR`), 但 "证据放种类还是放世界" 不定 (判断, 依据 `ColimAIf` 与 `AdmWIf` 的两条出路).
4. **跨级读数.** `RaiseFrame` 的读数类型不随成员变; C6 的跨级族读数随级变, 同键取 $v$ 要沿判定给的相等证明搬运, 这是 `ColimARaise.uip→raiseA1` 的 UIP 墙 (判断: 本路试想过用局部 Hedberg 在位置上得 UIP, 没写成, 难点是判定依赖位置证据, 换证据后给出的相等证明不能证明相同).

## §3 与翻译来的形状对照

| 翻译形状 | 判据推出的 | 一致/不同 | 依据 |
|---|---|---|---|
| `Lev hz = S₀` | 第 0 层含底 (`base0`) | 一致 (底的内容 `A` 是参数 $B$, 判据不定) | `least`, `LevC` |
| `Lev (hs x) = step (Lev x)` | 旧级全留 (`inherit` 沿 `≺s`) 加级 $x$ (`feed`) | 一致, 且是最小 | `least`, `exact→` |
| `Lev (hl f) = sup ℕ (Lev ∘ f)` | 各分支的级之并 (`inherit` 沿 `≺l`) | 一致, 且是最小; 拷贝是多出的重数 | `least`, `copies-Lev` |
| `Lev (hΩ κ g) = sup (E S κ) (Lev ∘ g)`, 种类与级 | 各分支的级之并 | 一致 | `least`, `exact→` |
| 同上, **世界** (裸坐标积) | 升界要求下标在定义域里可判定 | **不同**: 裸坐标积上合法升界推出分离子 | `sup-bare→Sep`, `posR` |
| `Lv (lΩ k g)` 多放 `step (Lv k)` | `cof` 与 `inherit` 沿 $k\prec$ `lΩ k g` | 一致, 且是最小; 不放则违反 `cof` | `leastL`, `no-crit⁻` |
| `step` 的新种类坐标 `HB S` | `feed` 的最早位置 | 一致 (不能更早: `no-self`) | `no-self` |
| `KindLvRd` 读回: 后继级精确, 极限级有损 | 判据不管读回 | 判据没有覆盖 (判断) | — |
| `ColimAIf.LevA`/`GWA` (Ω-并只取有界坐标) | 升界下标是合法界之下的位置 | 一致 (判断; 没有写同构定理) | `posR`, `pos-unique` |

## §4 翻译账

| 判据或结果 | 来自哪里 | 类 |
|---|---|---|
| `coord` | 两个现有形状 (`Lev`, `Lv`) 的共同性质 (`coord-lv`, `E-lvl`); 读回落在 `HB (L y)` 是 `HtTowerTy` 的 "坐标是高度" | 树逼出 (高度树的层级结构), 作为要求是选择 |
| `no-self` | `no-retract` (Burali-Forti 形状, 高度的良基) | 树逼出, 定理 |
| `feed` | 交替路线 "折叠输出回灌作下标"; 位置 `hs x` 由 `no-self` 逼到最早 | 纲领层的最佳实践; 最早性是定理 |
| `inherit` | 嵌入 `up`, `ι` 存在且保第一位置与合法 | 嵌入是树侧定理; 要求级保留是选择 |
| `sub` | 结构递归 (检查器保证停机) 只能引用结构子项 | 判断 (归纳-递归的定义不受此限, 如 `LFReTy`) |
| `cof` | `lΩ k g` 的分支域字面就是第 $k$ 层的值 | 字面读法, 选择; 读法 "Ω_{k+1} ≤ 层号" 受下标塔直觉启发 (`LFReTy` 自述), 如实记为受启发 |
| `LvUpper`, `LvUpperL` | "只认字面证据" (AGENTS 交替路线) | 选择 |
| `Raise` 的 `Ev`, `ev→wdec` | 分离子一族与 `bdec` | 树逼出, 定理 |
| `Pos` 的世界 | 由 `ev→wdec` 与 `bdec` 推出 | 树逼出; 与 `ColimA` 的设计一致 (判断) |

本路没有新构造子, 没有新结点, 没有读自基本列规则的字段. `R⁺`, `R⁻` 是为说明自由度与判据的分辨力造的对照, 不进成品. 摆脱侧: `Lev` 与 `Lv` 的形状从 "受直觉启发" 改记为 "判据 `feed`, `inherit`, `cof` (加 `LvUpper` 时唯一) 逼出的最小规则"; 但 `cof` 本身仍受同一直觉启发, 所以 `Lv` 的 `lΩ` 行是 "启发换了位置", 从定义挪到判据, 不是消失.

## §5 接手清单

1. **值的判据** (自由度 1): 把 `LvUpper` 从选择换成定理, 需要层号的值与级之间的一条树侧关系. 候选: 用 `BrwViewNeg` 的第一位置语言, 级 $y$ 出现当且仅当 `hs y` 是 $c$ 的字面第一位置 (带世界), 那就是 `ColimAIf.AdmL`; 未写.
2. **拷贝判据** (自由度 2): 写一条 "拷贝要相干" 的判据进接口 (只增), 对照 `noCrossA`.
3. **跨级读数** (自由度 4): 接口加一个读数随成员变类型的框架 (只增), 看 `shape` 是否仍成立, 搬运要不要 UIP; 局部 Hedberg 的试法见 §2 第 4 条.
4. **把 `Pos` 接回种类结构**: `posR` 只是世界上的算子; 接到 `KS` 上就是 `ColimAKS.LevC′`, 本路未证两者对应.
5. 否定一路 `NegTreeLang` 的消息说: 否定性判据单独对一切种类结构成立, 分不开候选; 本路的正面判据 (`feed`, `inherit`, `cof`) 是向上封闭的, 给出下界. 两者合起来是否刻画了 `Lev`/`Lv` 之外的东西, 待否定一路对本接口的结果.
