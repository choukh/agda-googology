# 结构关系, 第十五轮的否定一路: 入口

> **判决: 否定成立 (部分).** 对着接口 [StrRel15If](StrRel15If.lagda.md) 写 (定稿 2026-11-05 10:48, §1–§5). 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 不改任何已有文件, 不改接口与 `StrRel15` 前缀的构造文件.
>
> **对纲领与目标意味着什么 (判断).** 全部是第 4 层 (关系与语义) 的结论, 不碰树、折叠、合法性. 跨目标层的状态关系本身没有问题: 它的两条状态律 `Law⊕`, `Lawcv` 对一切 $\Lambda$ 成立 (编译过). 问题在**输出关系**: 接口在跨目标层的目标对上仍用 `StrRel14If.RelX`, 而目标层不同时, 同一个节点 (或同一个 `nκ`) 两边的读数可以一边是链的极限 (`nl`), 一边是节点 (`ni`, 或 `n0 ⨾ nκ`). `RelX` 没有这两种对. 所以接口 §4 的语义 `SemX²` 对节点与 `nκ` **都不自反**, §5 的 `NodeSound²`, `NodeSound²₀` 都不成立, 混合种类的两条义务 `OblRK²`, `OblKR²` 只要非空就是假的. 这些与状态无关 (对一切状态), 不是换不变量能修的; 也没有推出 LPO/WLPO 或判定.

## 1 定理表

| 名字 | 文件 | 陈述 | 档 |
|---|---|---|---|
| **`¬nlni`**, **`¬ninl`** | [StrRel15NDead](StrRel15NDead.lagda.md) | 一切 $\Lambda$, 一切层 $t,t'$: `RelX t t′` 不含 (`nl`, `ni`), 不含 (`ni`, `nl`) | 定理 |
| **`Dead.rk-dead`**, **`Dead.kr-dead`**, `rk-dead⇒`, `kr-dead⇒` | StrRel15NDead | `NodeObl²` 的一切参数 (含一切状态) 与一切目标对: `Out² T T′ rise (keep R′)` 与 `Out² T T′ (keep R) rise` 都不成立; 有一个实际给出该种的 `TX` 对, 就 `¬ OblRK²` / `¬ OblKR²` | 否定 (定理) |
| **`law⊕`**, **`lawcv`** | StrRel15NDead | 接口的 `Law⊕`, `Lawcv` 对一切 $\Lambda$ 成立 | 定理 (正面) |
| `rkT0`, `rkT1`, `tx01` | [StrRel15NNode](StrRel15NNode.lagda.md) | $\Lambda_1=1$, 坐标层 $0$ 的节点在 $T_0$ 上升, 在 $T_1$ 上留; $(T_0,T_1)$ 是 `TX` 对 | 定理 (实例) |
| **`¬oblRK²`** | StrRel15NNode | 同一个节点 `x1` 对 `x1`, 任意状态、动作、上下文: `¬ OblRK²` | 否定 (定理) |
| **`relX1`**, **`¬semX²`** | StrRel15NNode | `RelX Λ₁ Λ₁ tt tt x1 x1` 成立, `SemX² Λ₁ Λ₁ tt tt x1 x1` 不成立 | 否定 (定理) |
| **`¬NodeSound²`**, **`¬NodeSound²₀`** | StrRel15NNode | `¬ NodeSound²`, `¬ NodeSound²₀` (实例 $\Lambda_1$) | 否定 (定理) |
| `ΩX`, `YN`, **`jN`**, `Z₀`, `hZ` | StrRel15NNode | 前提实例: `J² YN YN` (含 `NE`), 零动作的 `HAW²` | 定理 (前提可满足) |
| **`NoNlNi`**, `nn-RelX`, **`refl-nlni`** | StrRel15NNode | 任何缺 (`nl`, `ni`) 推导的关系族都不能把 `x1` 在 $(T_0,T_1)$ 上的两个读数相关, 对一切状态 | 否定 (定理) |
| **`¬nl-n0κ`**, **`relK`**, **`¬semK²`** | [StrRel15NKap](StrRel15NKap.lagda.md) | `nκ` 在 $(0,1)$ 上是回灌 (`nl`) 对保留 (`n0 ⨾ nκ`); `RelX xK xK` 成立 (`κˣ`), `SemX² xK xK` 不成立 | 否定 (定理) |
| `NoNlK`, `nk-RelX`, `refl-nlK` | StrRel15NKap | 同上, 对任何缺 (`nl`, `n0 ⨾ nκ`) 推导的关系族 | 否定 (定理) |
| **`kRR`, `kKK`, `kRK`, `kKR`**, `txRR` … `txKR` | [StrRel15NKind](StrRel15NKind.lagda.md) | $\Lambda_2$: 四种种类都在 `TX` 对上实际出现; 左升右留在同一个节点上 | 定理 (实例) |
| `¬oblRK²₂`, **`¬oblKR²₂`** | StrRel15NKind | 这两对节点上的 `OblRK²`, `OblKR²` 不成立 (任意状态) | 否定 (定理) |

## 2 每条律为什么是构造一路需要的

- `NodeSound²`, `NodeSound²₀` (接口 §5): 接口写出的节点规则可靠性本身; `NodeSound²₀` 是接口点名的特例 (`StrRel13Val` 的 `xL`/`xR`).
- `SemX²` (接口 §4): 节点规则与 `κˣ` 的可靠性都要落到它. 它的结论 `OA²` 在一切 `TX` 对上比; 构造一路的 `Law⊕` 要的就是 `OA²` 相关的输出 (语义在 `⨾` 处把前段输出加进状态, 同 `StrRel12Sem.sem-⨾`), 所以树里出现的每个节点 (包括两边相同的节点) 都要给出 `OA²`.
- `OblRK²`, `OblKR²` (接口 §5): 接口为目标层不同的情形新增的义务; `StrRel14Rk.node-red` 那样的归约要四种义务齐全.

## 3 前提实例

全部写出: `tx01` (`cp00`, `u∞ s∞`); `jN` (`YN` 在一切 `TX` 对上 `RelX` 相关, 两边 `NE`); `hZ` (零动作的 `HAW²`); 上下文 `n0`, `n0ˣ`; 路径 `cp00`; 分支前提 `n1ˣ` (节点), `κˣ` 的分支 `n1ˣ`; `kRR`…`kKR` 的种类等式都是 `refl`, 目标对的 `TX` 都写出.

## 4 只否定什么, 不否定什么

- **只否定**: 以 `StrRel14If.RelX` 作跨目标层输出关系 (`OA²`) 时 (a) `SemX²` 对节点与 `nκ` 的自反性, (b) `NodeSound²`, `NodeSound²₀`, (c) 非空情形下的 `OblRK²`, `OblKR²`. `NoNlNi`/`NoNlK` 两条把 (a) 推广到任何缺 "极限对节点" (`nl` 对 `ni`) 或 "回灌对保留" (`nl` 对 `n0 ⨾ nκ`) 推导的关系族. 全部对一切状态成立, 所以不依赖 `J²` 的选择.
- **不否定**: (i) 状态律 `Law⊕`, `Lawcv` (它们成立); (ii) `LawKp`, `LawKb` (没有处理; 判断: 它们只说 `Kp`/`Kb` 两种输出, 分支前提 `BrOK` 要分支的 `SemX²`, 含节点的分支因此不满足 `BrOK`, 对只含 `n0`/`n1`/`⨾`/`nl`/`nw` 的分支看不出障碍); (iii) `OblRR²`, `OblKK²` (没有找到反例, 也没有证; 在 $\Lambda_2$ 的 `xL`/`xR` 上, `J²` 的跨目标层分量把 `StrRel14NegInv.inv-kill` 用的 "右边高层读数为零" 排除了, 判断); (iv) 给跨目标层的输出关系加 "极限对节点" 与 "回灌对保留" 规则之后的版本 (那两条规则的语义要另看: 左边是链的极限, 其各项是本节点的 `Ai` 沿链的输出; 右边是节点, 分支是 `BNi` 的输出; 判断, 依据 `HtFeedFold.RKi`); (v) 把 `TX` 限制成不跨过任何节点坐标层的目标对 (判断: 那要按树里出现的坐标层选定义域, 不是字面的目标层证据, 而 `Law⊕` 要对一切加进来的输出封闭).
- 没有推出 LPO/WLPO 或判定: 种类由 `cmpH` 在一个世界里算出 (可判定), 失败来自 `RKi` 两句输出的字面形状.

## 5 第二项任务的三问 (简报 §2)

| 问 | 结论 | 档 |
|---|---|---|
| 律与跨坐标层义务能否同时成立 | 律成立 (`law⊕`, `lawcv`); 义务中 `OblRK²`, `OblKR²` 一出现就假, `NodeSound²`/`NodeSound²₀` 假. 冲突不在律与义务之间, 在 `OA²` 用的 `RelX` | 定理 |
| 跨目标层后种类组合是否让某条义务在可满足前提下为假 | 是. 四种都出现 (`kRR`…`kKR`); 左升右留在**同一个节点**上出现 ($k=k'$), 所以 `OblRK²` 与 `SemX²` 的自反性在可满足前提下为假 (`¬oblRK²`, `¬semX²`) | 定理 |
| 是否推出禁忌 | 否. 写不出 LPO/WLPO; 否定是字面形状上的 | 判断 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel15N where

open import Data.Unit using (tt)
open import OCF.Align.HtFeedTree using (hs; hz)
open import OCF.Align.StrRel15NDead (hs hz) tt public using (¬nlni; ¬ninl; module Dead; law⊕; lawcv)
open import OCF.Align.StrRel15NNode public using (¬oblRK²; relX1; ¬semX²; ¬NodeSound²; ¬NodeSound²₀; jN; hZ; NoNlNi; refl-nlni)
open import OCF.Align.StrRel15NKap public using (¬nl-n0κ; relK; ¬semK²; NoNlK; refl-nlK)
open import OCF.Align.StrRel15NKind public using (kRR; kKK; kRK; kKR; ¬oblRK²₂; ¬oblKR²₂)
```

## 6 账

| 文件 | 行 (代码, 去空行与注释) | 内容 |
|---|---|---|
| `StrRel15NDead` | 44 | `¬nlni`, `¬ninl`, `Dead`, `law⊕`, `lawcv` (一切 $\Lambda$) |
| `StrRel15NNode` | 73 | $\Lambda_1$: `¬oblRK²`, `¬semX²`, `¬NodeSound²`, `¬NodeSound²₀`, `jN`, `hZ`, `NoNlNi` |
| `StrRel15NKap` | 30 | $\Lambda_1$: `¬nl-n0κ`, `¬semK²`, `NoNlK` |
| `StrRel15NKind` | 49 | $\Lambda_2$: 四种种类, `¬oblRK²₂`, `¬oblKR²₂` |
| 入口 | 8 | |
| 合计 | 204 | 全部手写, 没有生成文件 |

审计 (2026-11-05): 删掉本组 5 个 `.agdai` (逐个写模块名) 后从入口编译, 退出码 0, 约 4 秒, 峰值常驻约 0.7G (`-M6G`). 代码块里 `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext` 都是 0. 导入闭包 (`importclosure.py`, `--only` 同 `StrRel14Neg`: `OCF.Free.Level`, `OCF.BTBO`, `OCF.Align.` 下 `CumReadCF`, `TLRule`, `TLOpsW`, `SumOne`, `BrwMid`, `LayerTr`, `CvFold`, `CvHigh`, `CvLayer`, `NoCumLit`, `L1Val`, `DVal`, `HtGen`, `HtFeed`, `HtCross`, `KVal`, `KNest`, `MonoPort`, `StrRel`): 五个模块都是禁用表 0, `--only` 之外 0 (入口闭包 71 个模块, 本地 61). 定义级切片: `¬NodeSound²` 155 块, `¬semX²` 153, `¬oblRK²` 145, `¬semK²` 152, `¬oblKR²₂` 144, `lawcv` 76, `law⊕` 64, `jN` 58; 记号模块 0, 记号词 0. 正对照 `Om1HnAccept:label-term₀` 1188 块, 记号模块 92, 记号词 58.

## 7 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `¬nlni`, `rk-dead` | `RKi` 的 `rise` 句输出 `nl`, `keep` 句输出 `ni`; `RelX` 的构造子 | 树逼的 (否定) |
| `¬semX²` 的反例 | `rkT` 在目标层 $0$ 与 $1$ 上对坐标层 $0$ 的两种结果; 接口 `TX` 的字面 | 树逼的 (否定) |
| `¬semK²` | `RKy` 对第 $0$ 层回灌, 对别的层保留 | 树逼的 (否定) |
| `law⊕`, `lawcv` | `StrRel12Sem.advRc`/`cvRc` 的证明 | 树逼的 (正面) |

**归类: 提供信息.** 没有新构造子或节点字段, 没有改树与折叠, 没有 `Lab`, 没有记号. 否定划出: 跨目标层时, 输出关系必须含 "极限对节点" 与 "回灌对保留" 两种对 (或者语义不能在跨过节点坐标层的目标对上比).
