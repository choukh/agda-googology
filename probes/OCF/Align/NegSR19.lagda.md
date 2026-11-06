# 第十九轮的否定一路: 入口

> **判决: 否定成立 (`Trans⁺⁺`; 不带时间条件的 `UpSoundS` 与 `RkSoundZ`; "`ActS` ⇒ 不读累计"; 无条件的 "`DomZ` 经 `cv`"). 接口的 `UpSoundZ`, `RkSoundZ`, `OblRRZ` 未找到否定.** 对着接口 [StrRel19If](StrRel19If.lagda.md) 写 (定稿 2026-11-05 16:01; 16:22 的变更记录是文字补注, 不改定义, 本文对着补注后的版本重编). 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 不改任何已有文件, 不改接口与 `StrRel19` 前缀的文件.
>
> **对纲领与目标意味着什么 (判断).** 全部是第 4 层 (关系与语义) 的结论, 不碰树、折叠、合法性. 本轮的接口用两样东西修补上一轮: 产生时动作的语法 `ActS` (排除读累计的外来动作 `Az`) 与时间条件 `DomZ` (累计换成读数, 读数经 `cv` 保留). 编译的结论:
>
> - **`ActS` 不承担 "不读累计".** `ActS` 由 `Ai` 生成, `Ai` 运行分支, 分支里的 `nκ` 在第 $0$ 层目标上从累计起回灌; `ActS` 里有读累计的动作, 包括闭项自己的保留节点的分支动作 (`NegSR19Act`). 于是 `NegSR18Up.¬UpSoundR` 的机制 (上升输出在产生时读累计, 保留输出的分支在 `cv` 之后运行) 在 `ActS` 下重现: 不带时间条件的 `UpSoundS`, `RkSoundZ` 都不成立 (`NegSR19Up`, `NegSR19Rk`), 反例的再折叠恰被 `DomZ` 的累计分量挡住. 所以 `UpSoundZ`, `RkSoundZ` 若成立, 全靠 `DomZ`.
> - **`DomZ` 的累计分量是可以从不变量得到的.** "累计 ≤ 自己的读数" (`InvZ`) 对空状态、`cv`、`⊕` (加上的一段自反时) 保持; 有它与第 $0$ 层传递性时, `DomZ` 的累计分量由差分量推出 (`NegSR19Dom.domZ-z`, 条件定理). 对一般状态, `DomZ` 不经 `cv` 封闭 (`¬cvClosedZ`), 反例的产生状态违反 `InvZ`. 闭项的状态 $Y_1$ 满足 `InvZ`, 并对任意 `cv` 满足 `DomZ`.
> - **`up` 补上了 `¬trans⁺` 的那一对, 但跨层传递性仍不成立** (`NegSR19Tr`): `rk⁺⁺` 的前提不要 `ActS` (接口 "范围 (ii)"), `up` 要, 以 `Az` 为产生时动作的 `rk⁺⁺` 那一对就是新的反例. 若跨层传递成立, `up` 的 `ActS` 前提在 `rk⁺⁺` 联结的那一对上就是多余的.
>
> 没有推出 LPO/WLPO 或判定. 对 `DomZ` 下的可靠性 (`UpSoundZ`, `RkSoundZ`) 的判断: 对称 (`DomZ` 要求右边再折叠状态的第 $0$ 层读数支配 $z_P$; 右边的链从坐标层上的读数起, 读数里的 $\Omega_t$ 含坐标层 $0$ 的节点, 它们的链与 `Act` 都读第 $0$ 层读数), 未比较值, 没有找到反例.

## 1 定理表

| 名字 | 文件 | 陈述 | 档 |
|---|---|---|---|
| `Good`, `goodRun`, `goodActS` | [NegSR19Good](NegSR19Good.lagda.md) | `ActS` 的动作在一切目标上的输出都不是 `n1` 也不是 `a ⨾ n1` (一切 $\Lambda$) | 定理 |
| `¬ActS-Az` | NegSR19Good | `Az⁰` (输出 "累计 ⨾ 1") 不属于 `ActS` | 定理 |
| `oneK⁺⁺` | [NegSR19Tr](NegSR19Tr.lagda.md) | `NegSR18Up.¬trans⁺` 的那一对: `n1 ≤ Kr` 由 `up` (带 `sAct`) 推出 | 定理 |
| `noN1` | NegSR19Tr | `RelX⁺⁺ hz L′ n1 (ni R u′)` ⇒ 右边分支在 (`self`, `n0`) 上的值不是 `… ⨾ n1` | 定理 (求逆) |
| `¬n1Kr`, **`¬trans⁺⁺`** | NegSR19Tr | `n1 ≤ ORof YP` 推不出 (`Az` 的那一对); `RelX⁺⁺` 的跨层传递性不成立 | **否定 (定理)** |
| `vsum⁺⁺`, `ΩRX⁺⁺`, `hawAct⁺⁺`, `hawS`, `jYs⁺⁺`, `RKA.ge` | [NegSR19Lem](NegSR19Lem.lagda.md) | 第 $0$ 层的值; 有限 $\Lambda$ 上 `Act` 的 `HAWS`; 差为 `dN` 的状态的 `J⁺⁺`; 以至少加一的动作再折叠, 和不减 | 定理 (工具) |
| `semS00`, `sem-in` | [NegSR19Sem](NegSR19Sem.lagda.md) | `RelX⁺⁺ hz hz ⇒ SemS hz hz … Any` (一切 $\Lambda$) | 定理 (工具) |
| `orEq`, `lowAi`, `lowL` | [NegSR19Rk](NegSR19Rk.lagda.md) | 分支为 `nκ`、产生时动作 `Act` 的节点: 保留输出不依赖产生时累计 (`refl`); 左边以 $Y_0$, `Act` 再折叠 $>\Sigma\,\mathrm{RefR}$ | 定理 (值) |
| **`¬RkSoundS-Any`** | NegSR19Rk | `RkSoundZ` 的条件换成 `Any` 后, 在 `(hz, hs hz)` 上不成立 (产生时两边 `ActS`) | **否定 (定理, 值)** |
| `¬domZ-Y0` | NegSR19Rk | 上一行的再折叠不满足 `DomZ YP` (只违反累计分量) | 定理 |
| **`¬ActS→NoZ`**, `actS-AiK`, `actS-fold`, `¬noZ-actS-fold` | [NegSR19Act](NegSR19Act.lagda.md) | `ActS` 的动作不都满足 `NoZ`; `NegSR18Ai.AiK` 与闭项的保留节点的分支动作都属于 `ActS` 且读累计 | **否定 (定理, 值)** |
| **`¬UpSoundS-Any`** | [NegSR19Up](NegSR19Up.lagda.md) | `UpSoundS (λ _ _ → Any)` 不成立 | **否定 (定理, 值)** |
| `domZ⊕`, `InvZ`, `invZ₀`, `invZcv`, `invZ⊕` | [NegSR19Dom](NegSR19Dom.lagda.md) | `DomZ` 对右边 `⊕` 封闭; 不变量 "累计 ≤ 自己的读数" 对空状态、`cv`、(自反的) `⊕` 保持 | 定理 |
| `domZ-z` | NegSR19Dom | `Trans00⁺⁺` ⇒ (`InvZ Y₀`, 差分量, $\tau_0$ 的 `TX` ⇒ `DomZ` 的累计分量) | 条件定理 (`Trans00⁺⁺`) |
| **`¬cvClosedZ`**, `¬invZ-Y₀` | NegSR19Dom | "`DomZ` 经右边 `cv` 封闭" 对一般状态不成立; 反例的产生状态违反 `InvZ` | **否定 (定理, 值)** |
| `invZY₁`, `domZY₁`, `domZ-cvY₁` | NegSR19Dom | 闭项状态 $Y_1$ 满足 `InvZ`; `DomZ Y₁` 对 $Y_1$ 与它的任意 `cv` 成立 | 定理 (正面) |

## 2 每条律为什么是构造一路需要的

- **`UpSoundS Ok` / `UpSoundZ`** (接口 §5): `up` 是 `RelX⁺⁺` 的新构造子, 以 `RelX⁺⁺` 为输出关系的语义要它可靠. `¬UpSoundS-Any` 说可靠性必须用 `DomZ` 的累计分量.
- **`RkSoundZ`** (接口 §5): `rk⁺⁺` 的可靠性. `¬RkSoundS-Any` 说同样必须用 `DomZ` 的累计分量.
- **"`ActS` ⇒ 不读累计"** (接口 "范围 (iii)" 的意图): 若成立, 可靠性就可以不管产生时的累计 (`NegSR18Z` 的读法). `¬ActS→NoZ` 否定它.
- **"`DomZ` 经 `cv`"**: 节点的分支、`nκ` 的格、`Kp`, `Kb` 都先 `cv` 再运行, 再折叠状态要带着 `DomZ` 过 `cv` (`DomL` 过不去, `NegSR17Time.¬domCv`). `¬cvClosedZ` 说不是无条件的; `domZ-z` 说加 `InvZ` 与 `Trans00⁺⁺` 后只剩差分量.
- **`Trans⁺⁺`**: `StrRel17`, `StrRel18` 的接手清单把传递性列为 `Up` 可靠性的来源; `up` 是为了补上 `¬trans⁺` 的缺口. `oneK⁺⁺` 说补上了, `¬trans⁺⁺` 说补完仍不传递.

## 3 前提实例

全部是编译过的定理, 没有空真的否定. `¬trans⁺⁺`: `oneAz` (`in⁺⁺`), `rkAz` (`rk⁺⁺`, `NegSR17RkT.preP`, `(cp00 , u∞ s∞)`, `refl`, `refl`). `¬RkSoundS-Any`, `¬UpSoundS-Any`: `preK` (`RkPre` 六项, 旧关系), `sAct`, 种类 `refl`, `semL`; 再折叠 `cp00`, `hawS hz (hs hz)`, `n0⁺⁺`, `jYs⁺⁺ n0⁺⁺`, `tt`, `(cp00 , s∞)`. `¬ActS→NoZ`: `actS-AiK`. `¬cvClosedZ`: `domB` (`DomZ YB₀` 在 $(Y_B,Y_B)$ 上). `domZ-z` 的条件 `Trans00⁺⁺` 没有实例 (判断: `StrRel18Tr.trans00⁺` 可照搬); 其余前提由 `invZY₁`, `domZY₁` 满足.

## 4 只否定什么, 不否定什么

- **否定**: (1) `Trans⁺⁺` (三个层任意; 反例的 `rk⁺⁺` 用非 `ActS` 的 `Az`). (2) `RkSoundS-Any hz (hs hz)`, `UpSoundS (λ _ _ → Any)` (产生时动作 `ActS`; 读累计的是分支里的 `nκ`). (3) "一切 `ActS` 动作满足 `NoZ`". (4) 无条件的 `CvClosedZ`.
- **不否定**: 接口的 `UpSoundZ`, `RkSoundZ`, `OblRRZ` (判断见文件头; `OblRRZ` 本路没有看); `Trans00⁺⁺`; 两边都限 `ActS` 的 `rk⁺⁺` 下的传递性 (判断: 本文的反例消失, 未试); 产生状态满足 `InvZ` 时 `DomZ` 经 `cv` 的封闭 (第 3 条把它归约到差分量); `Emb⁺⁺` (构造一路的补注判断它可能不成立, 本路没有看).
- 没有推出 LPO/WLPO 或判定.
- **与构造一路的重合 (本路只读了构造一路入口的文件头, 未复核).** 构造一路独立得到 `¬ActS-Az` (`StrRel19Act`), `act-AiK`, `semS00` (`StrRel19Sem`), `domZY₁`; 本文的同名或同义定理是独立写的. 构造一路的新障碍 (再折叠目标对 $(T_1,T_1)$, 右边节点再次保留) 本文没有涉及.

## 5 模块

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR19 where

open import Data.Unit using (tt)
open import OCF.Align.StrRel13Val using (Λ₂)
open import OCF.Align.NegSR19Good Λ₂ tt public using (Good; goodRun; goodActS; Az⁰; ¬ActS-Az)
open import OCF.Align.NegSR19Tr public using (Lr; Kr; oneK⁺⁺; noN1; oneAz; rkAz; ¬n1Kr; Trans⁺⁺; ¬trans⁺⁺)
open import OCF.Align.NegSR19Lem public using (module V0⁺⁺; module Fin⁺⁺; module RKA)
open import OCF.Align.NegSR19Rk public using (orEq; lowAi; lowL; preK; RkSoundS-Any; ¬RkSoundS-Any; ¬domZ-Y0)
open import OCF.Align.NegSR19Act public using (actS-AiK; ¬ActS→NoZ; actS-fold; ¬noZ-actS-fold)
open import OCF.Align.NegSR19Up public using (semL; ¬UpSoundS-Any)
open import OCF.Align.NegSR19Dom public using (module Gen; CvClosedZ; ¬cvClosedZ; ¬invZ-Y₀; invZY₁; domZY₁; domZ-cvY₁)
```

## 6 审计

- **冷编译** (2026-11-05): 删掉本组 `.agdai` (逐个写模块名: `NegSR19`, `NegSR19Good`, `NegSR19Tr`, `NegSR19Lem`, `NegSR19Sem`, `NegSR19Rk`, `NegSR19Act`, `NegSR19Up`, `NegSR19Dom`; 未动 `StrRel19*` 与接口), 从入口重编: 退出码 0, 约 21 秒, 峰值常驻约 2.6 GB (`-M8G`). 代码块里 `postulate`, 洞, `TERMINATING`, `NON_TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext` 都是 0, 不开 K.
- **导入闭包** (`importclosure.py`, `--only OCF.Free. OCF.BTBO OCF.Align.BrwMid OCF.Align.CumRead OCF.Align.DVal OCF.Align.HtFeed OCF.Align.KNest OCF.Align.KVal OCF.Align.L1Val OCF.Align.LayerTr OCF.Align.NegSR16 OCF.Align.NegSR17 OCF.Align.NegSR18 OCF.Align.NegSR19 OCF.Align.NoCumLit OCF.Align.StrRel OCF.Align.SumOne OCF.Align.TLRule`): 入口闭包 94 个模块 (本地 84, 库 10), 禁用表 0, `--only` 之外 0; 八个子文件各自单跑 (81, 82, 75, 70, 83, 86, 85, 76 个模块) 也都是 0, 0. 不加 `--only` 时禁用表也是 0.
- **定义级切片** (`depslice.py`, `--html` 由本组入口在编译通过后生成; 正对照 `Om1HnAccept` 及其闭包的 html 从 `NegSR18` 那一轮的 scratch 目录拷来, 未重生成): `¬trans⁺⁺` 276 块, `¬RkSoundS-Any` 296, `¬UpSoundS-Any` 337, `¬ActS→NoZ` 244, `¬cvClosedZ` 222, `domZ-cvY₁` 211, `¬ActS-Az` 219, `oneK⁺⁺` 184, `¬domZ-Y0` 269; 记号模块 0, 记号词 0. 正对照 `Om1HnAccept:label-term₀` 1188 块, 记号模块 92, 记号词 58. 切片看不见模块应用, 块数偏少; 记号无关由导入闭包保证.

## 7 账

| 文件 | 行 (代码, 去空行与注释) | 内容 |
|---|---|---|
| `NegSR19Good` | 63 | `Good`, `goodRun`, `goodActS`, `¬ActS-Az` |
| `NegSR19Tr` | 60 | `oneK⁺⁺`, `noN1`, `¬n1Kr`, `¬trans⁺⁺` |
| `NegSR19Lem` | 83 | `vsum⁺⁺`, `ΩRX⁺⁺`, `hawS`, `jYs⁺⁺`, `RKA.ge` |
| `NegSR19Sem` | 115 | `law⊕⁺⁺`, 六条规则, `sem-in`, `semS00` (`StrRel16Sem` 的逐字搬运) |
| `NegSR19Rk` | 104 | 实例, `lowAi`, `lowL`, `RkSoundS-Any`, `¬RkSoundS-Any`, `¬domZ-Y0` |
| `NegSR19Act` | 25 | `actS-AiK`, `¬ActS→NoZ`, `actS-fold` |
| `NegSR19Up` | 47 | `reflDrp⁺⁺`, `semL`, `¬UpSoundS-Any` |
| `NegSR19Dom` | 96 | `domZ⊕`, `InvZ`, `domZ-z`, `¬cvClosedZ`, `domZY₁`, `domZ-cvY₁` |
| 入口 | 11 | |
| 合计 | 604 | 全部手写; 几处用 Python 做一次性的字面替换, 没有生成的部分 |

## 8 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `goodActS`, `¬ActS-Az` | `HtFeedFold.Run`, `RKi`, `RKy`/`RKk` 的输出的最外层形状 | 树逼的 (工具) |
| `¬trans⁺⁺` | `rk⁺⁺` 的前提是旧的 `RkPre` (不要 `ActS`), `up` 要 `ActS` | 树逼的 (否定) |
| `¬RkSoundS-Any`, `¬UpSoundS-Any`, `¬ActS→NoZ` | 分支里的 `nκ` 在第 $0$ 层回灌, 第 $0$ 格的世界是 "运行世界 + 累计" (`κc`); `BNi` 先 `cv` | 树逼的 (否定) |
| `InvZ`, `domZ-z`, `¬cvClosedZ` | `St` 的两个字段; `⊕` 给差与累计加同一段在 $\tau_0$ 上的读数; `cv` 清累计、把差搬到新世界 | 树逼的 |

**归类: 提供信息.** 没有新构造子或节点字段, 没有改树、折叠、合法性, 没有 `Lab`, 没有记号. 否定划出: `ActS` 不承担 "不读累计" (那是 `DomZ` 的事); `DomZ` 的 `cv` 封闭要靠不变量 `InvZ`; `rk⁺⁺` 与 `up` 对动作的要求不一致时跨层传递性不成立.
