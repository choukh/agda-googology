# LamIso: 最高层含与各站层号同形的层 (入口)

> 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不用函数外延 (连前提也没有). 导入闭包只有 stdlib 与 `OCF.Lean.*` (`importclosure.py --only OCF.Lean. OCF.Lean.LamIso`: 禁用表命中 0, `--only` 之外 0). 已有文件一律未改.
>
> **任务** (作者 2026-11-05, 原话选项 "②: 最高层 Λ 含与站层号同形的层"; 选项说明 "新最高层 Λ′ 含与各站层号同形的层 (先 n=3, 再一般 n)"). 目标 (作者 /goal): 写出 ψ₀Λ 的候选闭项. 配对的否定一路: `NegLamIso*` (共用接口 [LamIsoIf](LamIsoIf.lagda.md)).
>
> **对纲领与目标.** 纲领 1, 2: 闭项 `TI : HB S⊥` ([LamIsoTm](LamIsoTm.lagda.md)), 证书 `Lg-TI`, `fghI`, 无公理, 停机由检查器保证, 合法由形状给出. 纲领 3: 接口的律只对一个层与字面的 $\Lambda'$ 说话; `Prt` 是数据, 不判定层号相等. 纲领 4: 导入闭包干净. **目标 "让树自足"**: 新的层 `L n` 不是读自记号的, 而是 `LeanTLv` 的塔 `tw n` (即 $\Lambda=x\mapsto\Omega_x$ 的不动点的那座塔) 在 `SLs` 里的忠实拷贝: 每个 $\hat\Omega$-步的新种类从**第 $n$ 站自己的** `Lv (st n)` 里沿坐标取 (`Lv (st n)` 里有 `st n` 的 "自画像"); 合法性要求逼出了 "提供者沿坐标选, 前缀逐项继承" (否定一路 `NegLamIsoPre.path-illegal`, `station-diag-illegal` 是同一件事的反面). **离 ψ₀Λ 的候选闭项还差什么**: (i) **没有值定理** (严格的 `TI` 高于 `TVs`/`TL` 未走通; 只有世界这一档, [LamIsoVal](LamIsoVal.lagda.md)); (ii) 层 `L n` 内部的拷贝种类 (级 $\ge2$) 在计划里仍有损 (同 `LeanFb` 接手清单第 3, 4 条), 它们现在出现在最高层里, 闭包时有损; (iii) $\Lambda'=\Lambda_L\boxplus\Lambda_F$ 是接缝 (判断: 接 `ΛF` 只是为了让站的头 `νS m` 的结点出现在最高层里; 否定一路 `NegLamIsoInst.Sg-gone`: `Sg (m+1)` 不再是 $\Lambda'$ 的第一位置). 作者的担心 ("前 3 层已经非常接近标杆…不大幅压缩…意义不大"): 本路第 3 层 1391 行, 比 `TVs` 多 96 行 (见 §4), 没有压缩; 新增的 `Ψ` 一族 (105 行) 是一般 $n$ 的代价.

| 文件 | 内容 |
|---|---|
| [LamIsoIf](LamIsoIf.lagda.md) | 接口 (定稿 2026-11-05 22:58): 忠实同形 `Prt` (Ω-结点的种类是一个 `Emb (FL k) (step T)` 的新种类的像, 坐标映射是它的 `cv`), `LamIso Λ`, `OwnRd Λ n` |
| [LamIsoPsi](LamIsoPsi.lagda.md) | 对一切 `T`: 迭代 `it`, 三条等式 (`eqS`, `eqL`, `eqΩ`, 不用函数外延), 提供者 `Src`, $\hat\Omega^m$ 的翻译 **`Ψ`**, `Ψ-fst`, `Ψ-mono`, `Lg-Ψ`, 拷贝结点的同形 `prtNode`, 后继种类 `succE`, **`Prt-Ψ`** |
| [LamIsoL](LamIsoL.lagda.md) | 第 $n$ 站自己的种类 `Est`, `tw-eq`, **层 `L n`** (一切 $n$), `Lg-L`, `L-st` ($L_n\lhd L_{n+1}$ 对一切世界), **$\Lambda'$**, **`prtL`**, 接口实例 `lamIso` |
| [LamIsoTm](LamIsoTm.lagda.md) | `toS`, `toSim`, 头的读回 `Rown n` (级层 `L n`, 读进 `Lv (st n)`, 嵌入 `idE`), `own`, `lvSimI`, 计划 `planI`, **闭项 `TI`**, `Lg-TI`, `fghI` |
| [LamIsoShape](LamIsoShape.lagda.md) | 形状定理: 按自己的级, `L 3` 显式, 头 3 读出 `kTop3` |
| [LamIsoVal](LamIsoVal.lagda.md) | $\Omega_{L_3}$, $\Omega_{L_4}$ 的读回是 $\Omega$-结点; 回灌格的世界 `Cell.top0` (一切 $n$), `CellΩ3.top0-Ωd` |
| [LamIsoTest](LamIsoTest.lagda.md) | 有限测试 `sz-7I` |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LamIso where

import OCF.Lean.LamIsoIf
import OCF.Lean.LamIsoPsi
import OCF.Lean.LamIsoL
import OCF.Lean.LamIsoTm
import OCF.Lean.LamIsoShape
import OCF.Lean.LamIsoVal
```

## §1 主要定理

| 名字 | 文件 | 陈述 | 档 |
|---|---|---|---|
| **`L`, `Lg-L`, `L-st`, `Λ′`, `lΛ′`, `L⊲`** | L | 对一切 $n$: 层 `L n` 合法; `L n ⊲ L (n+1)` 对一切世界; $\Lambda'=\sup_n L_n\boxplus\Lambda_F$ 合法, `L n` 是它对一切世界的字面第一位置 | 定理 (构造) |
| **`prtL`**, `lamIso` | L | 对一切 $n$: `Prt SLs (L n) (st n)` (忠实同形, 每个 Ω-结点带后继种类); `LamIso Λ′` | 定理 (构造) |
| `Ψ`, `Lg-Ψ`, `Ψ-mono`, `Ψ-fst`, **`Prt-Ψ`** | Psi | 对一切 `T`, $m$, 提供者: 前缀与 $\hat\Omega^mA$ 同形, 则 $\Psi_m(y)$ 合法、对 $y$ 单调, 与 $\hat\Omega^m(A\boxplus\iota_k y)$ 忠实同形 | 定理 |
| `succE` | Psi | `Lv (ofHB (Ω̂^m (Y+1)))` 里有 `step (Lv (ofHB (Ω̂^m Y)))` 的嵌入, 对一切 $m$, $Y$ | 定理 (构造) |
| **`own`, `lvSimI`**; `own-x`, `own-em`, `own-reads`, `plan-own` | Tm, Shape | 对一切 $n$: 头 $n$ 的读回的层号就是 `st n`, 嵌入是 `idE`, 读回字面地是 `readS (toS π) idE` (对照否定一路 `NegLeanLvBlind.no-own-sim`: 在 `ΛF` 上 $n\ge3$ 不可能; 对照盲定理 `NegLamIsoBlind.ownConst`: 接口不逼沿 π 读, 实例是) | 定理 (`refl`) |
| `L3-top`, `L3-br0`, `L3-node`, `L3-node-co` | Shape | `L 3` 显式: 顶种类是第 3 站的 `(inj₁ tt , inj₂ tt)`; 第 0 支是 `L 2`; 第 $c+1$ 支的结点种类是第 3 站分量 `inj₂ (c+1)` 的左分量的新种类, 坐标 `HB (Lv (g₂ c))` | 定理 (`refl`) |
| **`rd-top3`**, `rd-top3-has` | Shape | 合法世界 `W3` 里一份 `L 3` 上的数据读成 `kTop3` (坐标 `HB (Lv (st 2))`) 的 Ω-结点; 对照 `NegLeanLvS.no-top3-RLs` (`TVs` 的头 3 读不出) | 定理 |
| **`rdΩd3`**, `rdΩd3-base`, `rdΩd4` | Val | 对一切世界, $\Omega_{L_3}$ 读成第 3 站 `(inj₂ (β+1), (inj₂ 1, inj₂ tt))` 的 Ω-结点 (基世界里是 `kTop3`); $\Omega_{L_4}$ 读成一个 Ω-结点 (不再有损) | 定理 (`refl`) |
| `Cell.top0`, `CellΩ3.top0-Ωd` | Val | 一切 $n$: 回灌第 0 格的世界里头 $n$ 的顶 = 原顶 $\boxplus$ 读回; 头 3, 状态取 $\Omega_t$ 时升上来的顶含上面的种类 (前提实例 `Y-Ωd`) | 定理 (世界档) |
| `sz-7I` | Test | 有界展开 $k=7$: `TI` 也是 7238 (同 `TVs`, `TL`) | 有限测试 |

否定一路已编译的相关结果 (引用, 复核由主审做): `NegLamIsoPre.path-illegal`/`pathcopy-illegal` (按路径选拷贝不合法), `station-diag-illegal` (对角相邻项不继承种类不合法), `ΛC` (`Sim⁺` 被一种类塌缩满足; 由此接口用 `Prt`); `NegLamIsoBlind.col-never-prt`, `ΛC-no-LamIso`, `ΛF-no-own`, `ownConst`; `NegLamIsoInst.L-no-head` (一切 `L n` 不含站的头的结点), `Sg-gone`, `own-in-ΛL`; `NegLamIsoRd.rd-top3`, `rd-br0`.

**先 $n=3$, 再一般 $n$.** 一般 $n$ 的构造 (`Ψ`) 第一次就编译通过, 所以没有另写一个手写的 $n=3$ 文件; $n=3$ 的显式形状由 `L3-top`, `L3-br0`, `L3-node` (`refl`) 给出: 一般定义里经 `tw-eq`, `eqH` 的 `subst` 在 $n=1$ 处化成 `refl`.

## §2 闭项与读法

`TI = sum hz ΨI`, 折叠 [LeanTFold](LeanTFold.lagda.md) 取 `T = SLs`, 最高层 $\Lambda'=\Lambda_L\boxplus\Lambda_F$, 底种类 `νS 0`, 参数 `fbI`. 计划与 `TVs` 的差: 头 $n\ge2$ 的级层是 `L n` (原来一律 `Sg 1`), 读回沿 `prtL n` 读进 `Lv (st n)` (原来读进 `Lv (st 2)` 再经 `emb2`); 头 0, 1 的级层 `L 0 = 0`, `L 1 = 1`, 读回不变; 其余深种类有损.

**$\Lambda'$ 与原 `ΛF` 的关系 [判断].** $\Lambda_L=\sup_n L_n$ 与 `LeanTLv` 的 $\Lambda=\sup_n$ `tw n` 逐结点同形 (`prtL`), 即仍以 $\Lambda=x\mapsto\Omega_x$ 的不动点为目标; `ΛF` $=\sup_n(1\boxplus$ `tws n`$)$ 是同一不动点的 "站头" 写法 (`tws (n+1)` 的分支过第 $n$ 站的头). $\Lambda'$ 把两者接起来, 量级读作 $\Lambda\cdot2$ 一类, 目标不变. 读回的种类比 `TVs` 多: 头 $n$ 读出 `Lv (st n)` 自己的种类 (例如头 3 的 `kTop3`, 级 `st 2`).

**读法 [判断, 粗].** 没有重算 `TI` 的序数读法. `TVs` 的读法判断是与 `TF` 同一档或更高 (`LeanFb` 对 `TF`: 不超过 $\psi_0(\Omega_3)$ 量级). `TI` 的头 $n$ 的界按 `Lv (st n)` 的种类升 (世界档定理), 但层 `L n` 内部级 $\ge2$ 的拷贝种类的闭包有损, 所以判断它不会到 $\psi_0(\Omega_\Lambda)$ 量级; 是否高于 `TVs` 没有定理, 有限测试 ($k=7$) 分不出.

## §3 值

**严格的值定理未走通** (没有编译过的 `TI` 严格高于 `TVs` 或 `TL`, 也没有否定). 有的是世界这一档 ([LamIsoVal](LamIsoVal.lagda.md)). 卡点同 [LeanLvVal](LeanLvVal.lagda.md) §3 (判断): 从 `RKa` 往下两边在不同世界里跑, `rkT` 的保留/上升可能不同, 闭包结点的分支对世界的单调没有定理; 而否定一路 `NegLeanLvVal.absorb-D` 说明逐格严格推不出闭项严格 (`strict-cell`). 本路新增的是: 回灌格里升上来的增量现在含头自己的级上更高的种类 (`top0-Ωd`, `kTop3`), 这是 "回灌格不被常数倍界住" 的候选证据, 没有走到第 0 层输出.

## §4 行数 (定义级切片)

脚本 `probes/Survey/scripts/lamiso/locslice_lamiso.py` (口径同 `leanlv/locslice_leanlv.py`; HTML 由同一目录里先后编译 `OCF.Lean.LamIso` 与 `OCF.Lean.LeanLv` 得到). 记号模块 0; 第 3 层闭包里 `OCF.Lean` 之外的仓库块 0.

| 层 | `TI` | 对照 `TVs` (LeanLv) | 对照 `TF` (LeanFb) | 记号侧标杆 |
|---|---|---|---|---|
| 1 定义 (含层 `L`, $\Lambda'$, `Ψ`) | 542 | 397 | 379 | 120 |
| 2 + 同形, 读回, 折叠, 计划, 闭项, FGH | 1387 | 1293 | 1050 | 131 |
| 3 + 证书 | **1391** | **1295** (去掉经模块应用带进的旧计划 27 行是 1268) | **1052** | **1513** |
| 4 + 形状与世界定理 | 1529 | 1565 | 1144 | 1533 |

**第 3 层逐件增量** (对 `TVs` 的 1295: 共有 1169; 只在 `TVs` 的 126 行是 `LeanLvTmS` 43 (`Sg`, `σ₂⁺`, `RLs`, 计划, 闭项), `LeanLvEmb` 32 (`supMap`, `ΩE`, `ΩMap`, `nodeMap`, `embΩ`, `emb2`: 不再需要), `LeanFbTm` 31 与 `LeanFbRd` 20 (经 `LeanFbTm` 根上的模块应用带进的旧计划, 本路把 `bkS` 重写四行避开); 只在 `TI` 的 222 行):

| 件 | 文件 | 行 |
|---|---|---|
| 接口 `Prt` | LamIsoIf | 7 |
| 迭代与等式 (`it`, `eqS`, `eqL`, `eqΩ`, `eqH`, `Zf`, `X`) | LamIsoPsi | 17 |
| 分量 (`ΩF`, `lft`, `rgt`) 与提供者 (`Src`, `Gb`, `Qt`, `Pv`, `Qn`) | LamIsoPsi | 16 |
| 翻译 `Ψ` 与它的 `fst`/`step`/`mono`/`Lg` | LamIsoPsi | 36 |
| 同形 (`prtNode` 9, `succE` 7, `Prt-Ψ` 16, `P⟨_⟩` 2) | LamIsoPsi | 34 |
| 层 `L`, `Lg-L`, `L-st`, `ΛL`, $\Lambda'$, `L⊲`, `one′`, 站的种类与 `tw` 的形状, `prtL`, `skL` | LamIsoL | 52 |
| `bkS`, `toS`, 读回与回灌 (`R0′`, `RX′`, `Rown`, `feed*`), 计划, `toFbI`, 闭项, 证书, FGH | LamIsoTm | 58 |
| 合计 | | **+222** (1169 + 222 = 1391) |

其中**为一般 $n$ 付的**是 `Ψ` 一族与等式 (约 100 行); **因 `Feed` 以 $\Lambda$ 为下标而重述的** `R0′`, `RX′`, `feed0′`, `feed1′`, `toFbI` (约 20 行, 与 `LeanFbTm`/`LeanFbRd` 逐字同形, 工程). 1391 < 1513 (记号侧第 3 层), 但比 `TVs` 多 96 行 (对去掉旧计划的 1268 多 123 行): **没有压缩**.

## §5 翻译账

- **新定义来自哪里.**
  - 层 `L n` 的形状: 读自 `LeanTLv` 的塔 `tw n` ($\hat\Omega$ 的迭代), 不是读自记号的基本列. `tw` 与 `Lv` 的形状本身记为记号引导 (`LeanTLv` 自述), 本路没有改它.
  - 忠实同形 `Prt` (Ω-结点的种类是嵌入的新种类, 坐标映射是 `cv`): 由否定一路的盲定理 `ΛC` 逼出 (`Sim⁺` 允许常值坐标映射, 一个种类就满足 "含同形层").
  - 提供者沿坐标选、前缀逐项继承: 由合法性逼出 (否定一路 `path-illegal`, `station-diag-illegal`).
  - 后继种类 `succE`: 由 $\Omega_L$ 的主结点过一支本身逼出 (不加时 `Ωd (L n)` 读成有限值; 否定一路 `rd-br0-lossy` 在加之前编译过, 加之后换成 `rd-br0`); 位置读自 `Lv` 的形状 (第 $1$ 支里的后继), 对一切 $m$ 递归.
  - $\Lambda'=\Lambda_L\boxplus\Lambda_F$ 的 $\boxplus\Lambda_F$: 为了让站的头出现在最高层里 (判断; 否定一路 `L-no-head`: $\Lambda_L$ 里没有站的头). 这是接缝, 不是树逼出的.
- **新脚手架.** `it` 与三条等式, `tw-eq`, `tw1`, 提供者里的 `subst` (约 25 行): 因为不用函数外延, 层号的等式只能对 $m$ 归纳、逐步 `cong Ω̂`, 再 `subst` 到同形与嵌入上 (工程; 对具体的站化成 `refl`). `R0′` 等重述 (约 20 行, 工程). 没有为翻译加的脚手架.
- **缺陷变深还是新思路 [判断].** 没有新结点、新构造子, 闭包定理没有专属前提, 不用 `Lab`. 新信息: (1) **`Lv (st n)` 里有 `st n` 自己的忠实画像** (`L n` 只用第 $n$ 站的种类加前缀 `L (n-1)`): 对一切 $n$, 头按自己的级读回由此可得 (`own`); `LeanLv` 接手清单第 1 条的 "按级选全局一致的拷贝" 的答案是 "按坐标在自己的站里选". (2) 提供者的选法与 $\hat\Omega$ 的递归一一对应 ($\hat\Omega(Z+1)$ 的新种类 ↔ `Lv (ofHB (Ω̂ (Z+1)))` 的左分量; 下一层 ↔ 第 $e+1$ 支), 这是树侧的一条规则, 不看记号. (3) 头 $n$ 的读回现在读出 `Lv (st n)` 里高于 `emb2` 像的种类 (`kTop3`), `NegLeanLvS.no-top3-RLs` 划出的缺口在本路的实例上补上了.

## §6 接手清单

1. **值 (b).** 严格的值定理仍要一条带 $W\le W'$ 的模拟关系穿过 `LeanTFold` (卡点同 `LeanLvVal` §3). 新的候选证据: `CellΩ3.top0-Ωd` 的增量含 `kTop3` 一类种类的 Ω-结点; 要证它在第 0 层输出里留下大于常数倍的痕迹 (对照 `absorb-D`).
2. **层内部的深拷贝种类有损.** `L n` 的内部结点是第 $n$ 站的拷贝种类 (级 $\ge2$ 的大多有损, `memS 0/1` 之外); 它们现在在最高层里出现, 闭包时走有损行. 要给它们回灌 (同 `LeanFb` 接手清单第 3, 4 条), 或证明它们的有损不影响量级.
3. **接缝 $\boxplus\Lambda_F$.** 能否让 `L n` 自己含站的头 (例如顶种类取站头 `νS 0`, 内部某些结点取 `νS m`), 从而去掉 $\boxplus\Lambda_F$; 否定一路 `Sg-gone`, `L-no-head` 是现状. 未研究.
4. **压缩.** `LeanLvEmb` 的 `embΩ`/`emb2` 一族、`LeanLvTmS`, `LeanLvTm`, `LeanLvRd` 在本路里不用; 若以 `TI` 为主候选, 清理时连同否定一路的引用一起删. `R0′` 等的重述可以把 `LeanFbTm` 的计划对 $\Lambda$ 参数化 (改已有文件, 要作者定).
5. **一般 $n$ 的读回的形状定理** (`rdΩd3` 对一切 $n$): 对变量 $n$, `prtL n` 经 `subst` 卡住, 只能对具体的 $n$ 写 `refl` (本路写了 3, 4). 要一般的, 写 "`Prt` 沿等式搬运后 `readS` 不变" 的引理.

## §7 审计 (2026-11-05)

- **编译.** 从仓库根: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Lean/LamIso.lagda.md +RTS -M6G -RTS`, 退出码 0; `LamIsoTest` 单独编译, 退出码 0. 各模块 2 到 4 秒, 常驻内存 0.4G 以内.
- **禁用构造.** 八个文件的代码块里 `postulate`, 洞, `TERMINATING`/`NO_POSITIVITY`, `trustMe`, `Funext`, `REWRITE`, `--with-K` 都是 0; 选项都是 `--safe --without-K --lossy-unification`.
- **导入闭包.** `importclosure.py --only OCF.Lean. OCF.Lean.LamIso`: 禁用表命中 0, `--only` 之外 0; `LamIsoTest` 同.
