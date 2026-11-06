# LeanLv: 头按自己的级读回 (入口)

> 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不用函数外延 (连前提也没有). 导入闭包只有 stdlib 与 `OCF.Lean.*` (`importclosure.py --only OCF.Lean. OCF.Lean.LeanLv`: 禁用表命中 0, `--only` 之外 0). 已有文件 (含 `LeanT*`, `LeanFb*`) 一律未改.
>
> **任务** (作者 2026-11-05, 原话 "LeanFb: 头按自己的级读回"; 选项说明 "构造+否定配对: 第 n≥2 站的头按自己的级读回 (层的子层与 Lv (st n) 的种类对应, KindLvRd 式), 并做第一条值定理 (TF 严格高于全有损折叠)"). 目标 (作者 /goal): 写出 ψ₀Λ 的候选闭项. 配对的否定一路: `NegLeanLv*` (共用接口 [LeanLvIf](LeanLvIf.lagda.md)).
>
> **对纲领与目标.** 纲领 1, 2: 主候选闭项 `TVs : HB S⊥` ([LeanLvTmS](LeanLvTmS.lagda.md); 只有 $0$, 后继, $\mathbb N$-极限的布劳威尔树), 证书 `Lg-TVs`, `fghVs`, 无公理, 停机由检查器保证, 合法由形状给出 (读回的合法 `Lg-readS` 对一切数据). 纲领 3: 接口的律只对一个种类、一个世界或一对带第一位置证据的坐标说话; `Sim`, `Sim⁺` 是数据, 不判定层号相等; 级层是最高层的字面第一位置 (对一切世界). 纲领 4: 导入闭包干净. **目标 "让树自足"**: 读回的每一行都是对 "层与层号的同形" 的结构递归 (`Sim⁺`), 种类由层号 `Lv` 的形状给出, 没有读记号基本列的字段; 但 `Lv` 的形状本身记为记号引导 (`LeanTLv` 自述), 后继种类的位置 (`inj₂ (hs c)`) 读自 `st 2` 的形状. **离 ψ₀Λ 的候选闭项还差什么**: (i) 第 $n\ge3$ 站的头没有自己的级层 (在 `ΛF` 上不可能: 否定一路 `NegLeanLvBlind.no-sim`), 要改最高层 $\Lambda$ (接手清单第 1 条); (ii) 级 $\ge2$ 与含函数层号的同级拷贝仍有损 (同 `LeanFb`); (iii) **没有值定理** (严格的 `TVs`/`TF` $>$ `TL` 未走通, [LeanLvVal](LeanLvVal.lagda.md) §3 写了卡点).

| 文件 | 内容 | 参考 (只读, 不导入) |
|---|---|---|
| [LeanLvIf](LeanLvIf.lagda.md) | 接口: `Emb`, `Sim` (层 ↔ 层号同形), `RdSTy`, `LvSim`, `HasK`; 只增 §6 `Sim⁺` (极限处的后继种类), `RdS⁺Ty` | `KindLvIf`, `StratTwIf` |
| [LeanLvEmb](LeanLvEmb.lagda.md) | 嵌入的构造 (`idE`, `stepE`, `supE`, `∘E`, `botE`, `supMap`), 沿嵌入的连续分支 `nbJ`, $\hat\Omega$ 的嵌入 `embΩ`, `nodeMap`, `emb2 m : Emb (Lv (st 2)) (Lv (st (2+m)))` | `KindLvEmb` |
| [LeanLvRd](LeanLvRd.lagda.md) | 沿 `Sim` 的读回与写入 (不是主候选; 否定一路对它编译过) | `KindLvRd`, `StratTwRd` |
| [LeanLvRdS](LeanLvRdS.lagda.md) | 沿 `Sim⁺` 的读回 `readS`, 写入 `wrS`, 起点 `readS-fst`, 合法 `Lg-readS` | 同上 |
| [LeanLvTm](LeanLvTm.lagda.md) | `Sg m`, `σ₂ : Sim SLs (Sg 1) (st 2)`, 闭项 `TV` (沿 `Sim`, 不是主候选) | `LeanFbTm` |
| [LeanLvTmS](LeanLvTmS.lagda.md) | `σ₂⁺`, 回灌 `RLs m`, `feedLs m`, 计划 `planS`, **闭项 `TVs`**, `Lg-TVs`, `fghVs` | `LeanFbTm` |
| [LeanLvShape](LeanLvShape.lagda.md) | 形状定理 (第 4 层) | — |
| [LeanLvVal](LeanLvVal.lagda.md) | 回灌格的世界 (定理); 严格值定理的卡点 (未走通), 粗界 (判断) | `ValNew*` |
| [LeanLvTest](LeanLvTest.lagda.md) | `TVs` 与全有损 `TL` 的有限测试 | `LeanFbTest` |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanLv where

import OCF.Lean.LeanLvIf
import OCF.Lean.LeanLvEmb
import OCF.Lean.LeanLvRd
import OCF.Lean.LeanLvRdS
import OCF.Lean.LeanLvTm
import OCF.Lean.LeanLvTmS
import OCF.Lean.LeanLvShape
import OCF.Lean.LeanLvVal
```

## §1 主要定理

| 名字 | 文件 | 陈述 | 档 |
|---|---|---|---|
| `TVs`, `Lg-TVs`, `fghVs` | TmS | 无条件闭项, 证书, FGH | 定理 (构造) |
| `readS`, `readS-fst`, **`Lg-readS`** | RdS | 对一切 $T$, 层 $a$, 层号 $x$, `σ : Sim⁺ T a x`, `Em : Emb (Lv x) X`: 层 $a$ 上的数据读进 `HB X`, 起点是第一位置, 合法由形状给出 | 定理 (构造) |
| `embΩ`, `nodeMap`, `emb2` | Emb | `Emb (Lv (ofHB h)) (Lv (ofHB (Ω̂ h)))` 对一切 $h$; 站的层号 `st 2` 嵌进 `st (2+m)`; 没有沿 `E-lvl` 的搬运 | 定理 (构造) |
| `σ₂`, `σ₂⁺` | Tm, TmS | `Sg 1` (最高层的第 1 项) 与 `st 2` 同形, 坐标映射恒等 | 定理 (构造) |
| `heads-fed` | Shape | 对一切 $n$, 头 $n$ 有回灌 (无条件, 不经 `find0`) | 定理 |
| `lv-layer`, `Sg1≢1` | Shape | 头 $2+m$ 的级层是 `Sg 1`, 不是 $1$ | 定理 (`refl`) |
| **`own2-x`, `own2-em`, `own2-Q`** | Shape | 头 2: 同形的层号 = 坐标的层号 `st 2`, 嵌入 = `idE`, 读回目标 = `Lv (st 2)` (**按自己的级**) | 定理 (`refl`) |
| `lvm-x` | Shape | 头 $2+m$ ($m\ge1$) 的同形层号仍是 `st 2` (不是自己的级) | 定理 (`refl`) |
| **`rd-a`, `rd-b`, `rd-ab0`, `kinds0`, `kinds1`** | Shape | 读回产出不止一种种类: 两份数据分别读出 `j (emb2 m) κa` (坐标 `HB S⊥`) 与 `j (emb2 m) κb` (坐标 `HB (step S⊥)`) 的 $\Omega$-结点 (一切 $m$); 一份数据同时含两者 ($m=0$); $m=0,1$ 时两种类不同. 对照 `rdX-one-kind` | 定理 |
| `x₂-lossy-Sim` | Shape | 沿 `Sim` (`TV`) 读, 过一支本身的结点读成 $1$; 沿 `Sim⁺` 读成 $\kappa_b$ 的 $\Omega$-结点 | 定理 (`refl`) |
| `exec-head`, **`exec-TVs2`**, `fb2`, `fb2-ℓ` | Shape | `ΨVs` 沿显式路径的子项字面地是头 2 的回灌行 `RKa _ (fbS (νS 2)) …`, 它的级层是 `Sg 1` | 定理 (`refl`) |
| `Cell.top0` | Val | 回灌第 0 格的世界里头 $2+m$ 的顶 = 原顶 $\boxplus$ (状态在 `Sg 1` 上的数据的读回) | 定理 |
| `rdΩd`, `CellΩ.top0-Ωd` | Val | $\Omega_{\mathrm{Sg}\,1}$ 读成后继种类 `(inj₂ (hs β) , inj₂ tt)` 的 $\Omega$-结点; 状态在 `Sg 1` 上是 $\Omega_{\mathrm{Sg}\,1}$ 时 (实例 `Y-Ωd`), 升上来的顶含这个种类 | 定理 |
| `sz-7V` | Test | 有界展开 $k=7$: `TVs` 与 `TL` 都是 7238 | 有限测试 |

否定一路已编译的相关结果 (引用, 复核由主审做): `NegLeanLvPre.lvl-cases`/`lvrd-cases` (基世界里 `ΛF` 的第一位置只有 $0$, `Sg m`, `ΛF`; 所以一切 `LvRd SLs ΛF` 的级层在这张表里), `no-own`, **`NegLeanLvBlind.no-sim`** (这些层与 `st (3+n)` 之间没有 `Sim`, 对任意坐标映射; 推论 `no-own-sim`), `NegLeanLvS.no-sim⁺` (同上对 `Sim⁺`), `img-readS`/`img-readS⁺`, **`no-top3-RLs`** (头 3 的读回只在 `emb2 1` 的像里, 不产出 `Lv (st 3)` 里坐标为 `HB (Lv (st 2))` 的种类), `rdΩ-top-lossy` (沿 `Sim` 读, 过 $\Omega$-极限一支本身有损; 由此加了 `Sim⁺`), `succK-co`, `rd-Ωd⁺`, `NegLeanLvVal.absorb-D` ("每格严格" 推不出 "闭项严格"), 盲: `simConst` (`LvSim` 被常数读回满足), `sim-any-k`, `toSim⁺`.

## §2 闭项与读法

`TVs = sum hz ΨVs`, 折叠 [LeanTFold](LeanTFold.lagda.md) 取 `T = SLs`, 最高层 `ΛF = up Λs`, 底种类 `νS 0`, 参数 `fbS = map₁ toFb ∘ planS`. 与 `LeanFb` 的 `TF` 只差头 $n\ge2$ 的回灌: 级层 `Sg 1` (原来 $1$), 读回沿 `σ₂⁺` 读进 `Lv (st 2)` 再经 `emb2` 放进 `Lv (st n)` (原来 `rdX (find0 (st n))`, 只产出一个级 0 种类). 头 0, 头 1, 级 `lz`/`ls lz` 的同级拷贝原样; 其余深种类有损 (同 `LeanFb`).

**读法 [判断, 粗, 只从树形与回灌算].** 头 2 的界按自己的级 (`Lv (st 2)`, 坐标的级 $1+c$, $c$ 可数) 升, 升上来的增量含后继种类的 $\Omega$-结点 (`top0-Ωd`). 头 $n\ge3$ 的界也按 `Lv (st 2)` 的那份拷贝升 (`no-top3-RLs`), 比 `TF` 多出可数多个级的种类. 读法与 `TF` 同一档或更高 (`LeanFb` 对 `TF` 的判断是不超过 $\psi_0(\Omega_3)$ 量级; 本路没有重算 `TVs` 的读法). 没有值定理, 有限测试分不出.

## §3 值

**严格的值定理未走通** (没有编译过的 `TVs`/`TF` 严格高于 `TL`, 也没有否定). 有的是世界这一档 (`top0`, `top0-Ωd`): 回灌格的世界里头的界升上去, 而且升的是 `Lv (st 2)` 的后继种类的 $\Omega$-结点. 卡点 ([LeanLvVal](LeanLvVal.lagda.md) §3, 判断): 从 `RKa` 往下两边在不同的世界里跑, (a) `rkT` 的 "保留/上升" 两边可能不同, (b) 闭包结点的分支对世界的单调没有定理 (`ValNew` 接手清单第 1 条, `ValTK` 的第一个障碍); 否定一路 `absorb-D` 说明 "每格严格" 不够. 粗界全部是判断 (见 Val 的表).

## §4 行数 (定义级切片)

脚本 `probes/Survey/scripts/leanlv/locslice_leanlv.py` (口径同 `leanfb/locslice_leanfb.py`; HTML 由编译本入口得到). 记号模块 0; 第 3 层闭包里 `OCF.Lean` 之外的仓库块 0.

| 层 | `TVs` | 对照 `TF` (LeanFb) | 对照 `TΛ′` (LeanT) | 记号侧标杆 |
|---|---|---|---|---|
| 1 定义 | 397 | 379 | 265 | 120 |
| 2 + 读回, 折叠, 计划, 闭项, FGH | 1293 | 1050 | 722 | 131 |
| 3 + 证书 | **1295** | **1052** | **745** | **1513** |
| 4 + 形状与世界定理 | 1565 | 1144 | 772 | 1533 |

**第 3 层逐件增量** (对 `TF` 的 1052: 共有 1042; 只在 `TF` 的 10 行是 `Act`, `ΨF`, `TF`, `Lg-TF`, `fghF`; 只在 `TVs` 的 253 行):

| 件 | 文件 | 行 |
|---|---|---|
| 嵌入的构造 (`idE`, `stepE`, `supE`, `∘E`, `botE` 与 `Bot`, `supMap`) | LeanLvEmb | 43 |
| 沿嵌入的连续分支 (`nbJ`, `nbJ-mono`, `nbJ-fst`, `Lg-nbJ`) | LeanLvEmb | 25 |
| $\hat\Omega$ 的嵌入 (`ΩE`, `ΩMap`, `nodeMap`, `embΩ`, `emb2`) | LeanLvEmb | 24 |
| 级读回与写入 (`Br`, `readS`, `readSp`, `rdN`, `rdP`, `slf`, `wrS`, `wrK`) | LeanLvRdS | 41 |
| 读回的起点与合法 (`*-fst` 25, `Lg-*` 32) | LeanLvRdS | 57 |
| 接口 (`Emb` 11, `Sim⁺` 7, `RdS⁺Ty` 2) | LeanLvIf | 20 |
| 级层, 同形, 回灌, 计划, 闭项, 证书, FGH | LeanLvTmS | 43 |
| 合计 | | **+253** (1042 + 253 = 1295) |

**切片的上近似.** `TVs` 的第 3 层里有 27 行是经 `LeanFbTm` 根上的模块应用 (`open Fold … fb`) 带进来的旧计划块 (`fb`, `plan`, `planK`, `feedH`, `find0`, `findSt`, `oldAK`, `supAK`), `TVs` 在语义上不用 (`planS` 不经 `planK`). 去掉它们是 1268 (判断: 切片看不见 "模块应用里哪个参数被用到"). `LeanFb` 的那份 "闲置的新种类回灌机器" (`κc₁` 一族, 在 `TF`, `TVs` 上都不执行) 仍在第 3 层里.

1295 < 1513 (记号侧第 3 层). 对 `TF` 多出 243 行 (净), 其中嵌入的构造与 `nbJ` (68 行, 加接口的 `Emb` 11 行) 是 `KindLvEmb` 的重写, 读回 98 行是 `KindLvRd`/`StratTwRd` 的重写; 真正新的是 $\hat\Omega$ 的嵌入 (24 行), `Sim⁺` (7 行) 与 `LeanLvTmS` (43 行).

## §5 翻译账

- **新定义来自哪里.**
  - 级层 `Sg 1`: 由树侧的墙逼出: `LvRd.ℓ⊲` 要对一切世界是第一位置, 基世界里这样的层只有 $0$, `Sg m`, `ΛF` (否定一路 `lvl-cases`); `Sg 1` 是其中唯一与头 2 的层号同形的 (`σ₂`; 否定一路 `no-sim` 说 $n\ge3$ 没有).
  - `Sim` (层 ↔ 层号同形): 由 "层的子层与 `Lv x` 的种类对应" 这一要求本身逼出; 每个构造子对应 `HB` 与 `LH` 的一对构造子, 坐标映射是 `lΩ` 的下标. `Lv` 的形状 (`lΩ` 多一个 `step (Lv k)` 分量) 记为记号引导 (`LeanTLv`, `LFReTy` 自述), 本路没有改它.
  - `Sim⁺` 的后继种类: 由 $\Omega_L$ 的写法逼出 (`Ωd (hΩ κ g)` 的主结点 `ni (sL top hself)` 过一支本身; 不加它, 这个结点有损, $\Omega_{\mathrm{Sg}\,1}$ 读成有限值, 否定一路 `rdΩ-top-lossy`). 种类的位置 `inj₂ (hs c)` 读自 `st 2 = lΩ lz g₂` 的形状 (`g₂ (hs c)` 定义相等于 `ls (g₂ c)`), 即 `Lv` 的形状; 不是读自记号的基本列.
  - `embΩ`, `nodeMap`, `emb2`: 由头 $n\ge3$ 的坐标类型 `Lv (st n)` 逼出 (读回要放进它), 对 $\hat\Omega$ 与 `node` 的结构递归, 每一步坐标类型定义相等.
  - 读回与写入的行: `KindLvRd`/`StratTwRd` 的已有形状 (树侧路线), 换成一次封闭的层号. 极限处与写入经过 $\Omega$ 处有损, 同那里.
- **新脚手架.** `rdN`/`rdP`/`slf` 的三段 (检查器的覆盖与归约要求先按路径分情形, 约 10 行, 工程); `Bot` 模块 (空结构的嵌入, 14 行); `Sg` 在 `LeanLvTmS` 重写两行与 `planKs` 前三行直接写 (为切片, 不是为值). 没有为翻译加的脚手架.
- **缺陷变深还是新思路 [判断].** 没有新结点, 新构造子, 闭包定理没有专属前提, 不用 `Lab`. 新信息: (1) 头 2 有按自己的级的读回, 头 $n\ge3$ 在 `ΛF` 上没有 (否定一路定理); 所以 "按自己的级" 要求最高层含与 `st n` 同形的层, 即改 $\Lambda$; (2) $\Omega_L$ 的主结点过一支本身, 按级读回要在极限处有 "后继种类"; `Lv (lΩ k g)` 只在 $g$ 的值是后继时字面地有 (`st 2` 是); (3) 读回只产出嵌入的像里的种类 (否定一路 `img-readS⁺`): 按级读回的强度由级层的同形决定, 嵌入不加种类.

## §6 接手清单

1. **头 $n\ge3$ 的自己的级层 (要改 $\Lambda$).** 在 `ΛF` 上不可能 (`no-sim`, `no-sim⁺`). 候选: 新的最高层 $\Lambda'=\mathrm{hl}\,P$, $P_{n+1}=P_n\boxplus(L_{n+1}\boxplus \mathrm{Sg}(n+1))$ (累加, 相邻项第一位置由 `⊞-fst` 给出, 对一切世界), $L_n$ 是与 `st n` 同形 (`Sim⁺`) 的合法层, 级层取 $P_{n-1}\boxplus L_n$ (`Sim` 要加一个 "前缀读成 `lz`" 的构造子, 或对 $\boxplus$ 写引理). 难点 (判断): $L_n$ 的 $\Omega$-结点要用站 $n-1$ 的种类 (`Lv (st (n-1))` 里坐标合适的拷贝); 按 "在 `st (n-1)` 里的路径" 选拷贝时, `hΩ` 处不同分支用不同分量的拷贝, 分支间不再是第一位置 (不合法); 要按 "级" 选全局一致的拷贝. $n=3$ 可以手写 (第 $c$ 支用 `Lv (st 2)` 的分量 `inj₂ (hs j)` 的新种类, 单调由 $\hat\Omega$ 式的 $\boxplus$ 给出, 判断), 一般的 $n$ 未找到. 先配对派一路否定 (例如 "按路径选拷贝的层不合法").
2. **值 (b).** 严格的值定理要一条带 $W\le W'$ 的模拟关系穿过 `LeanTFold` (卡点见 Val §3). 否定一路的 `absorb-D` 划出了 "每格严格" 不够; 要找回灌格不被常数倍界住的证据 (`top0-Ωd` 的 $\Omega$-结点在第 0 层输出里留下的痕迹).
3. **`emb2 m` 保持第一分量** (小引理, 用 `LeanFbShape.tw-shape`): 有了它 `kinds0`, `kinds1` 推广到一切 $m$.
4. **`LeanLvRd`, `LeanLvTm` (`TV`)** 是沿 `Sim` 的版本, 被 `Sim⁺` 版取代; 否定一路对它们编译过, 所以留着. 将来清理时连同否定一路的引用一起删.
5. **级 $\ge2$ 与含函数层号的同级拷贝** (同 `LeanFb` 接手清单第 3, 4 条) 未动.

## §7 审计 (2026-11-05)

- **编译.** 从仓库根: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Lean/LeanLv.lagda.md +RTS -M6G -RTS`, 退出码 0; `LeanLvTest` 单独编译, 退出码 0. 各模块几秒到十几秒, 堆 6G 以内.
- **禁用构造.** 十个文件的代码块里 `postulate`, 洞, `TERMINATING`/`NO_POSITIVITY`, `trustMe`, `Funext`, `REWRITE`, `--with-K` 都是 0; 选项都是 `--safe --without-K --lossy-unification`.
- **导入闭包.** `importclosure.py --only OCF.Lean. OCF.Lean.LeanLv`: 30 个模块 (本地 19, 库 11), 禁用表命中 0, `--only` 之外 0; `LeanLvTest` 同.
