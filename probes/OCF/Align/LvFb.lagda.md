# 层号由回灌给出: A3 提前探路 (入口与判决)

> 不含记号. 作者选定原话: "A3 提前探路": 不等 CubX, 先在 `--without-K` 下把层号从 ℕ 换成由回灌给出的高度, 外延型的一步写成模块参数 (条件定理), 看结构上还缺什么. 作者另问 "保持 without K 的话, 写出闭项还有什么可行的思路". 本路先试三种不需要外延的写法 (W1, W2, W3), 每种写到能判定为止. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; `Funext` 只在 `LvFbSet` §4 作模块参数 (条件), 不进闭项与证书. 本路没有用到外延型的模块参数来写闭项: 外延型的一步被 W2 绕开了.
>
> **判决: PARTIAL.**
>
> 1. **W1 (外层界用差树表示): 成立 (定理), 在事件世界 `AdmEv` 上.** 因子化 `FacP` 对路径复合封闭 (`LvFbFac.fac-tr`), 部分和的极限包含有它 (`fac-lim`), 所以第 $n$ 站改贴到极限界 $\mathrm{hl}\,b_\bullet$ 保合法 (`Lg-rlω`), 不要 ⊞ 的结合律, 不要外延. 塔的 ℕ-极限按差树写 (各站新增的部分从出生的那一站改贴一次, 取部分和) 合法由形状给出 (`Lim.Inc.Lg-U`). 按站把整个高度改贴的链有拷贝 (`copy-lim`, 否定一侧; 与 `EvFoldLim.no-coh-ev`, `no-lim-n` 一致).
> 2. **W2 (下标用路径码): 成立 (定理).** 码是不带索引的数据, 相等可判定 (`LvFbCode.code-≟`), 码上有 UIP (Hedberg, `code-uip`); 以码为下标的世界上, 单个增量的更新在**一切**码上有精确的 `at` 律 (`CW.at`), 包括极限坐标 $\omega$ 的码 (`atω`, `refl`). 不要 `LoopFix`, 不要族增量, 所以 `NegFamSec.uniformAll→fix`, `slotFam-sep` 的前提都不出现. 代价是拷贝: 同一坐标的不同码各自升高 (`copy-split`).
> 3. **W3 (外延相等当关系): 未走通, 对本仓库的字面合法性 `LgB`.** 到 ≈ 为止地尊重第一位置是定理 (`LvFbSet.⊲≈`); 字面地尊重 (`Resp⊲`, `RespLg`) 推出逐点互模拟的 ℕ-极限相等 (`resp⊲→ext`, `respLg→ext`, 定理), 那是函数外延的实例, 在外延之下前提成立 (`FE.fe→respLg`, 条件). 不加外延时前提证不出 (判断, 元层). 换成到 ≈ 为止的合法性要重写第 3 层证书 (没有做).
> 4. **折叠 (任务 2): 部分.** 选 W2. `LvFbFold`: `FamFoldAll` 的逐级折叠搬进**一个**外层界含极限的世界 (外层界 $\omega+1$), 一切有限级在同一世界里回灌, 读回读折叠输出; 极限坐标 $\omega$ 的槽 (第 $\omega$ 层的界) 由各级级顶的输出读回逐级升高 (`ωslot-s`), 第 $n$ 步升高后其中出现第 $n$ 级新种类的节点 (`lv1`, `lv2`, 计算). 闭项 `T∞c` (合法, FGH). **没有做到的**: 回灌所在的坐标 (层号) 本身由回灌给出. 第 $n+1$ 级仍在码 `kfin (n+1)` 上回灌, $n$ 由外部给出; 极限层的槽没有被任何折叠读 (第一个障碍).
> 5. **值: 没有序数值定理.** 读法全是判断.
>
> **对纲领与目标.** 纲领 1: 闭项是 `A` 的元素, FGH 在树上算. 纲领 2: 无公理, 停机由检查器保证. 纲领 3: 不触壁垒: 一切判定是码的相等 (纯数据) 或同一合法界之下的 `cmpB₀`; 没有序与三歧. 纲领 4: 导入闭包与切片干净 (审计). 目标 "让树自足": W1 的 `fac-tr`/`fac-lim` 是对结构参数 (路径) 的一步定理, 新用到的只是路径复合的结合律; W2 把 "判等" 从坐标挪到码, 码的判定由数据本身给出, 不读记号. 第 $\omega$ 层以上的折叠没有写, 所以 "层号由回灌给出" 在折叠层面没有做到.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvFb where

import OCF.Align.LvFbSet
import OCF.Align.LvFbCode
import OCF.Align.LvFbFac
import OCF.Align.LvFbFold
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `fac-self`, `tr-idˡ`, **`fac-tr`**, `fac-step`, `fac-steps`, **`fac-lim`**, `PSum.fac-ps` | LvFbFac | 因子化是路径的性质, 对复合封闭, 部分和的极限包含有它 | 定理 |
| `RelX.sim`, `RelX.Lg-rl`, **`Lim.Lg-rlω`** | LvFbFac | 沿满足 `FacP` 的路径改贴保合法; 第 $n$ 站到极限 | 定理 |
| **`Lim.Inc.Lg-U`**, `Inst.Lg-Tω`, `Inst.kind-n` | LvFbFac | 差树的极限合法由形状给出; 闭实例 | 定理 |
| **`Lim.copy-lim`** | LvFbFac | 经下一站与直接改贴给同一旧种类不同的极限种类 | 定理 (否定一侧) |
| `≟RA`, `≟RB`, **`code-≟`**, **`code-uip`**, `vB-prop` | LvFbCode | 码的相等可判定, 码上 UIP | 定理 |
| `pB`, `cd`, `cd-tgt` | LvFbCode | 码与可入证据互相给出, 目标一致 | 定理 |
| **`CW.at`**, `CW.off`, `CW.mono`, `CW.legal`, `CW.slot-at` | LvFbCode | 码世界上单个增量的更新, 对一切码 | 定理 |
| `atω`, `atω′`, `lvω` | LvFbCode | 外层界 $\omega+1$, 在 $\omega$ 的码上 | 定理 |
| `copy-tgt`, `copy-ne`, **`copy-split`** | LvFbCode | 拷贝不随更新一致 | 定理 (代价) |
| **`⊲≈`**, `≈→¬<`, `≈⊲→≡`, `≈-rf`, `≈-sym`, `inv-*` | LvFbSet | 到 ≈ 为止地尊重第一位置; 互模拟不互为严格子项 | 定理 |
| **`resp⊲→ext`**, **`respLg→ext`** | LvFbSet | 字面尊重 ≈ ⇒ 逐点互模拟的 ℕ-极限相等 | 定理 |
| `FE.fe→resp⊲`, `FE.fe→respLg` | LvFbSet | 前提在外延之下成立 | 条件 (Funext) |
| `FKc.fold-Ω`, **`FKc.slot-s`**, `FKc.ch-lg`, `FKc.ch-≤` | LvFbFold | 码世界里的第 $n+1$ 级折叠, 槽的递推由 `at` | 定理 |
| `dnc`, `Hc`, `Λc`, **`T∞c`**, `Lg-T∞c`, `fghc` | LvFbFold | 一个世界里的对角闭项 | 定义; 合法是定理 |
| **`ωslot-s`**, `lgV`, `monoV`, `fin-zero` | LvFbFold | 极限层的槽由级顶输出的读回升高; 合法, 只增; 有限码不动 | 定理 |
| `lv1`, `lv2` | LvFbFold | $V_1$, $V_2$ 的极限层槽含第 1, 2 级新种类节点 | 定理 (具体级数的计算) |

## 闭项与 FGH 的类型原文

```text
LvFbFold.T∞c     : A                -- T⁺ Λc lΛc,  Λc = hl cumc,  cumc k = Hc 0 ⊞ … ⊞ Hc k
LvFbFold.Lg-T∞c  : Lg T∞c
LvFbFold.fghc    : ℕ → ℕ            -- FL.FGH (ord T∞c)
LvFbFold.Vω      : ℕ → Wω.Cmpᶜ      -- 一个世界 (外层界 ω+1) 的序列, 极限层的槽被回灌升高
LvFbFold.lgV     : ∀ n → Wω.LgC (Vω n)
LvFbFac.Inst.Tω  : HB Kω            -- 极限界 hl b• 之下的差树极限 (事件世界)
LvFbFac.Inst.Lg-Tω : LgB {Kω} Tω
```

全部无模块参数, 无前提.

## 前提实例

- `LvFbFac.Lim`, `PSum`: 一切合法 $a, b_0$, 一切合法增量族; 实例 `Inst` ($a=0$, $b_0=0$, 增量恒为 $1$, 内层世界 `wz`).
- `LvFbCode.CW`: 一切外层世界 $(a,b)$, 一切码族 $P$; 实例 $(0, \omega+1)$, $P\,k$ = `G₀ (tgt k)`, 起点 `v₀` 合法 (`lv₀`).
- `LvFbSet.resp⊲→ext`, `respLg→ext`: 前提 `Resp⊲`, `RespLg` 在 Funext 下成立 (`FE`); `LgB (hl g)` 的实例 `lg-const`.
- `LvFbFold`: 无前提.

## 第一个障碍

1. **第 $\omega+1$ 级的折叠: 极限层的槽没有消费者.** 读 $\omega$ 的码上的槽, 要一个层为 `HB (step (G₀ ω₀))` 的折叠, 它的旧种类是 $(n,\kappa)$ (`sup ℕ`) 的混合, 新种类的坐标是 `HB (G₀ ω₀)`. 旧种类的翻译可以逐个交给 `trK (pkg n)` (判断), 但读回 `HB (G₀ ω₀)` 之后要降到两种种类的层 (`FamFoldAll` 的 `δK` 要 `d : HB (Sk K₁) → Ht`), 而现有的下降 `dnR n` 是逐级的折叠, 对节点级数无界的混合高度没有定义. 对一般高度 $c$ 的层, 要把 `FamFoldRead.Pkg`, `FamFoldLift` 从 ℕ 推广到高度 (种类 = $c$ 里的后继位置), 那是 "对高度递归的读回包"; 本路没有写 (判断: 几百行).
2. **层号本身由回灌给出.** 在码世界里, 回灌所在的码可以是任何码 (W2 的 `at` 对一切码成立), 所以世界一侧没有障碍; 障碍全在第 1 条 (在那一层要有折叠).
3. **拷贝.** W1 的 `copy-lim` 与 W2 的 `copy-split`: 同一坐标的不同证据/码各自是种类, 各自的界. 合法性不需要它们一致 (W1 `Lg-U`, W2 `legal`); 值是否需要, 未知.

报错原文: 无 (障碍是没写的东西).

## 读法 (全部是判断)

| 闭项 | 读法 (判断) | 测到哪里 |
|---|---|---|
| `T∞c` | $\psi_0(\Omega_{\Omega_\omega})$, 与 `FamFoldAll.T∞` 同 | 有限码的槽从 0 起, 回灌与 `FK` 同法; 没有比较两者的定理 |
| `Vω n` 的极限层槽 | 第 $\omega$ 层的界, 含第 $1..n$ 级的级顶读回 | `ωslot-s`, `lv1`, `lv2`; 不进任何闭项 |
| `LvFbFac.Inst.Tω` | 事件世界里的高度, 不是 `A` 的元素, 没有 FGH | — |

## 翻译账

本路不读记号. 新定义及来源:

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `FacP`, `fac-tr`, `fac-lim` | `AdmEvGrow.fac` 写成路径的性质 | 树逼出 (改贴合法性要的) |
| `PSum.psum` (外层界的部分和) | 主线 `HtTowerFTree.sum`/`Lg-sum` | 树侧 (差树) |
| `RelX` | `AdmEvGrow.Grow₀`/`Relabel` 对一般路径 | 沿用, 一般化 |
| `Lim.Inc.U` (差树的极限) | `copy-lim` 逼出 | 树逼出 |
| 码 `RA`, `RB`, `vA`, `vB`, `Code`, `code-≟` | 路径 `_⊲[_]_` 的去索引写法 | 树侧, 脚手架 (序数值不需要, 去掉环的问题需要) |
| `CW.raiseC` | `AdmWIf.RaiseB` 换下标 | 沿用 |
| `FKc` | `FamFoldAll.FK` 换世界 | 沿用 (回灌形状仍是 `RunM` 的三步, `StallDiagnosis` §4 (i)) |
| `Vω`, `incω` | `FamFold` 接手清单第 3 条 | 树侧 |
| `⊲≈`, `≈→¬<`, `resp*→ext` | W3 的判定 | 第 4 层, 不进证书 |

归类 (判断): 提供信息. W1 是对路径的一步定理 (新用到的字段: 路径复合的结合律); W2 用一条否定式的观察 (码的相等是数据的相等) 去掉了以 $(c,p)$ 为下标时的环问题; W3 用定理划出不能有的东西 (字面合法性尊重 ≈). 加深翻译的地方: `FKc` 的回灌形状照搬 `FK`.

## 审计

- **编译**: 删本路五个模块的 `.agdai` (精确模块名 `OCF.Align.LvFb`, `LvFbSet`, `LvFbCode`, `LvFbFac`, `LvFbFold`), 依赖用共享接口, 入口 `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/LvFb.lagda.md +RTS -M6G -RTS`, 退出码见交回报告.
- **导入闭包** (`importclosure.py`, 不加 `--only`): 五个模块都退出码 0, 禁用表命中 0; 入口闭包 65 个模块 (本地 53).
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词): `LvFbFold:T∞c` 351/0/0, `Lg-T∞c` 355/0/0, `fghc` 369/0/0, `Vω` 338/0/0, `lgV` 350/0/0, `lv2` 341/0/0; `LvFbCode:at` 63/0/0, `code-uip` 52/0/0; `LvFbFac:Lg-U` 169/0/0, `fac-lim` 48/0/0, `copy-lim` 96/0/0; `LvFbSet:respLg→ext` 34/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58.
- **禁用构造**: 五个文件里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`; `Funext` 只在 `LvFbSet` 的模块 `FE` 的参数里.
- **分层行数**: 生成脚本 `probes/Survey/scripts/lvfb/locslice_lvfb.py` (口径同 `htfeed/locslice_four.py`), 数字见交回报告.

## 接手清单

1. 对高度递归的读回包: 把 `FamFoldRead.Pkg n`, `FamFoldLift.Le` 从 ℕ 推广到坐标 $c$ (种类 = $c$ 里的后继位置, 在 `sup` 处取各分量的包), 先只做 $c=\omega$ (各 `pkg n` 的对角) 与 $c=\omega+1$, 写第 $\omega+1$ 级的折叠, 让它读 `Vω` 的极限层槽.
2. 混合高度的下降: `HB (G₀ ω₀)` 到 `Ht`. 判断: 不能逐节点, 要一个第 $\omega$ 级的回灌 (同 `FK`), 它的读回目标是 `Ht` 里的对角 (形如 `Λc`).
3. W1 + W2 合并: 外层界由回灌的部分和给出 (W1 `PSum`), 世界以码为下标 (W2); 码在外层界长高时的弱化 (`cd (wk p)`) 与 `code-≟` 的相容, 没有写.
4. 拷贝的界: `copy-lim` 的两个种类在一切世界里的界相同 (由 `FacP` 大概可证); `copy-split` 的码拷贝要不要按坐标同步, 先问值是否需要.
