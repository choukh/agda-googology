# LeanFb: 在 LeanT 上加回灌实例 (入口)

> 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不用函数外延 (连前提也没有). 导入闭包只有 stdlib 与 `OCF.Lean.*` (`importclosure.py --only OCF.Lean.`: 禁用表命中 0, `--only` 之外 0). 已有文件 (含 `OCF/Lean/LeanT*`) 一律未改.
>
> **任务** (作者 2026-11-05, 原话 "在 LeanT 上加回灌实例"; 选项说明 "在重写的 745 行上只给 Fb 实例: ℕ 下标的站 (Fab2/SLFb) + 同级拷贝的共享槽 (Slot) + 按级读回; 先证回灌那一行真的被执行; 目标闭项前 3 层 < 1300, 并报每一件的增量"). 配对的否定一路: `NegLeanFb*` (共用接口 [LeanFbIf](LeanFbIf.lagda.md)).
>
> **对纲领与目标.** 纲领 1, 2: 闭项 `TF : HB S⊥` (只有 $0$, 后继, $\mathbb N$-极限的布劳威尔树), 证书 `Lg-TF`, `fghF`, 无公理, 停机由检查器保证. 纲领 3: 接口的律只对一个成员、一个世界说话, 没有两个下标的比较律; 能一起升的同级拷贝只在**数字层号** (`lsʲ lz`, 构造子可判定) 上分组, 含函数的层号不分组 (否定一路的 `wdec1`, `no-slot-κHc` 说那里不能); 站以 $\mathbb N$ 为下标. 纲领 4: 导入闭包干净. **目标 "让树自足"**: 这一轮没有新结点、新构造子; 新加的三件都写成对层号或站号的结构递归, 没有读记号的规则 (翻译账见 §4). 但它**没有**给出值判据: 回灌在闭项的计算里出现是定理 (`exec-TF0..2`), 回灌让值变大没有定理, 有限测试在可算深度内分不出 (`LeanFbTest`). **离 ψ₀Λ 的候选闭项还差什么**: (i) 第 $n\ge2$ 站的头没有自己的级层 (读回只产出一个级 0 种类的 $\Omega$-结点), (ii) 级 $\ge2$ 的同级拷贝与含函数层号的拷贝有损, (iii) 没有值定理. (i) 是本轮的主要缺口, 见 [LeanFbRd](LeanFbRd.lagda.md) 文件头的判断.

| 文件 | 内容 | 参考 (只读, 不导入) |
|---|---|---|
| [LeanFbIf](LeanFbIf.lagda.md) | 接口: `Up` (一起升), `LvRd` (按级读回), `Feed`, `Plan` | `SlotIf`, `KindLvIf` |
| [LeanFbSt](LeanFbSt.lagda.md) | 站 `SLs = sup ℕ FS`, 塔 `tws`, 对角 `Λs`, 最高层 `ΛF = up Λs`, ℕ 上的点更新, 一个站的头 `headUp n` | `Fab2SLs` §1, §3 |
| [LeanFbSlot](LeanFbSlot.lagda.md) | 数字层号 `num`, 判定 `eqN`; 级为 `num j` 的一切拷贝一起加 (`Add`), 成员位置 (`Pos`), `slotUp j`, 种类查成员 `memS` | `SlotCp.cpSlot`, `SlotGen` |
| [LeanFbRd](LeanFbRd.lagda.md) | 级 0 读回 `R0` (`sum`), 级 1 式读回 `rdX` (目标任意 $X$), 级 0 种类的查找 `find0` | `LeanTTree.rd₁`, `SLFbTm.KH₁`, `SLFbKit.akV` |
| [LeanFbTm](LeanFbTm.lagda.md) | 回灌计划 `plan`, 转换 `toFb`, 闭项 `TF`, `Lg-TF`, `fghF` | `LeanT` §2 |
| [LeanFbShape](LeanFbShape.lagda.md) | 形状定理 (第 4 层) | — |
| [LeanFbTest](LeanFbTest.lagda.md) | 与全有损 `TL` 的有限测试 | `LeanTCmp` |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanFb where

import OCF.Lean.LeanFbIf
import OCF.Lean.LeanFbSt
import OCF.Lean.LeanFbSlot
import OCF.Lean.LeanFbRd
import OCF.Lean.LeanFbTm
import OCF.Lean.LeanFbShape
```

## §1 主要定理

| 名字 | 文件 | 陈述 | 档 |
|---|---|---|---|
| `TF`, `Lg-TF`, `fghF` | Tm | 无条件闭项, 证书, FGH | 定理 (构造) |
| `heads-fed` | Shape | 对一切 $n$, `plan (νS n)` 是回灌 ($n\ge2$ 经塔的形状 `st-shape`) | 定理 |
| **`exec-TF0`, `exec-TF1`, `exec-TF2`** | Shape | `ΨF` 沿显式路径的子项字面地是 `RKa _ (fb (νS n)) …`, $n=0,1,2$ (路径由否定一路先找到) | 定理 (`refl`) |
| `exec-head`, `stage-head` | Shape | 第 $n$ 站层的头是 `inj₁ (νS n)`; 它的闭包结点在第 0 层目标上走 `RKa ac (fb (νS n))` | 定理 (`refl`) |
| `Raise.cell0`, `cellS`, **`raise0`**, `self` | Shape | 级回灌每一格的世界是 `rz` 加读回增量; 每个成员 (含触发的种类自己) 的顶是原顶 $\boxplus$ 读回 | 定理 |
| `rz-top` (`top-addN`, `top-addSt`), `head-keep` | Slot, St | 级为 `num j` 的**一切**位置升后是原顶 $\boxplus\delta$ (位置含函数下标, 不判定); 升一个站的头别的站原样 | 定理 |
| **`cp1-fed`, `cp1-moves`**, `head1-moves` | Shape | `NegSLFbInst` 的 `cp1` (第 3 站里第 1 站头的拷贝) 现在有回灌, 与头 1 加同一个增量 (对照那里的 `cp1-lossy`, `cp1-not-moved`) | 定理 (`refl`) |
| `bk-merge` | Shape | 底种类 `νS 0` 与第 1 站的级 0 种类同在 `slotUp 0`, 一次调用加同一个增量 | 定理 (`refl`) |
| `rdX-node`, `read0`, `read1` | Rd, Shape | 过第 0 层的结点读成 $\Omega$-结点 (不是可数增量, 对照 `Fab2SLs.rdC-form`) | 定理 (`refl`) |
| `lv2-lossy`, **`cp2-lossy`**, `cp2-not-moved`, `deep-lossy` | Shape | 级 `num 2` 的拷贝有损; 第 4 站里与第 2 站头同坐标类型的种类有损, 升头 2 时不动; 深种类有损当且仅当不是级 `lz`, `ls lz` 的成员 | 定理 |
| `sz-5`, `sz-7F`, `sz-7L` | Test | 有界展开结点数 $k\le7$: `TF` 与全有损的 `TL` 相同 (7238, 也与 `TΛ′` 相同) | 有限测试 |

否定一路已编译的相关结果 (引用, 复核由主审做): `NegLeanFbInst.ctrl-TL0` (同一路径在全有损折叠上是常值序列), `TF-old` (`TF` 的折叠里闭包结点全是旧种类, 所以 `step SLs` 新种类的回灌 `κc₁`/`rd₁` 与作为 `BotK` 的 `bkS` 在 `TF` 上不执行, 一行读法), `rdX-one-kind` (`rdX a` 的增量里一切 $\Omega$-结点都是 `aK a`), `lossy-hl` (第 3 站坐标 $1+\mathrm{hl}\,f$ 分量的新种类有损, 是某个合法世界里的目标层的头: 有损的是含函数下标的整族), `slot-merge`/`same-iter` (只经同一个 `Up` 升界的成员读数恒相等; 基世界读数都是 0: 盲, 不是否定), `rdConst` (常数读回满足 `δ-n1`; 接口头已按变更记录更正文字).

## §2 闭项与读法

`TF = sum hz ΨF`, 折叠 [LeanTFold](LeanTFold.lagda.md) 取 `T = SLs`, 最高层 `ΛF = up Λs`, 底种类 `νS 0`, 参数 `fb = map₁ toFb ∘ plan`. 回灌的分配 (定义, 见 [LeanFbTm](LeanFbTm.lagda.md) 的表): 级 `lz` 的一切种类 (头 0 与一切站里的级 0 拷贝) 一份 `Up`, 读回 `sum` (级层 0); 级 `ls lz` 的一切种类 (头 1 与它的一切拷贝) 一份 `Up`, 读回 `rdX newAK` (级层 1): 这两级**按自己的级读回**; 第 $n\ge2$ 站的头各自一份 (ℕ 点更新), 读回 `rdX (find0 (st n))` (级层 1, 不是自己的级); 其余深种类有损.

**有损的种类 (定理 `deep-lossy` 的刻画; 数量是判断).** 一切级不是 `lz`, `ls lz` 的深种类: 级为 `num j` ($j\ge2$) 的拷贝 (`lv2-lossy`), 第 $n\ge2$ 站头的一切同级拷贝 (`cp2-lossy`), 一切含函数层号的种类 (否定一路 `lossy-hl`). 按种类计这是 "几乎全部" 深种类 (判断: 每个站的层号含函数时, 只有数字层号的那些位置有回灌).

**读法 [判断, 粗, 只从树形与回灌算].** 与 [SLFbTm](../Align/SLFbTm.lagda.md) 的 `TF` 同一机制: 第 $n\ge2$ 站的头只按一个级 0 种类的 $\Omega$-结点升界 (`rdX-one-kind`), 级 0, 1 的回灌在自己的级上. 本轮比那里多的是: 级 0, 1 的同级拷贝 (含坐标下标的整族) 一起升, 头 1 按自己的级读回 (那里是级层 1 的 `rdQ`, 对头 1 恰好也是自己的级). 读法与那里同一档 (那里的判断是不超过 ψ₀(Ω_3) 量级; 这里没有另算, 判断); 没有值定理, 有限测试分不出.

## §3 行数 (定义级切片)

脚本 `probes/Survey/scripts/leanfb/locslice_leanfb.py` (口径同 `leant/locslice_leant.py`; HTML 由编译本入口得到). 记号模块 0; 第 3 层闭包里 `OCF.Lean` 之外的仓库块 0.

| 层 | `TF` | 对照 `TΛ′` (LeanT) | 记号侧标杆 |
|---|---|---|---|
| 1 定义 | 379 | 265 | 120 |
| 2 + 读回, 折叠, 计划, 闭项, FGH | 1050 | 722 | 131 |
| 3 + 证书 | **1052** | **745** | **1513** |
| 4 + 形状定理 | 1144 | 772 | 1533 |

**第 3 层逐件增量** (对 `TΛ′` 的 745: 共有 735, 只在 `TΛ′` 的 10 行是 `bkL`, `Λ′`, `Λ` 与它们的证书; 只在 `TF` 的 317 行):

| 件 | 文件 | 行 | 估计 (`LeanT` §6) |
|---|---|---|---|
| 站 (ℕ 下标, 塔, 对角, 点更新, 头的 `Up`) | LeanFbSt | 62 | — |
| 同级拷贝一起升 (数字层号, 加法, 位置, 成员查找) | LeanFbSlot | 117 | 60–80 (加实例 140–200) |
| 按级读回 (`R0`, `rdX` 与证书, `find0`) | LeanFbRd | 71 | 130–170 |
| 其他 (接口 26, 计划与转换与闭项 41) | LeanFbIf, LeanFbTm | 67 | — |
| 合计 | | **+317** (735 + 317 = 1052) | 350–450 |

1052 < 1300. 估计的 "带证据的世界" (160–200) 没有做: 加性的一起升不要同界证据. 第 3 层里仍有 `LeanTFold`/`LeanTTree` 的新种类回灌机器 (`κc₁`, `κΔ₁`, `Cl₁`, `rd₁` 一族, `drp₁`; LeanT §5 的回灌专用 139 行里只服务新种类的那部分), 它们在 `TF` 上不执行 (否定一路 `TF-old` 加一行读法); 不改已有文件, 所以留着.

## §4 翻译账

- **新定义来自哪里.** 站以 $\mathbb N$ 为下标: 由树侧的墙逼出 (否定一路 `wdec1`: 以层号为下标的世界上 "只升一层" 推出分离子). 塔 `tws` 的形状由头种类的坐标类型逼出 (同 `Fab2SLs`). 加性的一起升: 由 "世界必须变大而没有同界证据" 逼出 (`rz≤` 只靠 `⊞-fst`). 只在数字层号上分组: 由可判定性逼出 (纲领 3). 读回 `rdX` 是 `rd₁` 的已有形状换目标; `find0` 对层号结构递归. **没有**新结点、新构造子, 没有读自记号基本列的字段, 闭包定理没有专属前提, 不用 `Lab` 验收.
- **新脚手架.** 成员位置 `PosN`/`kN`/`coN` (约 30 行) 是为 `rz-top` 对一切位置成立的陈述 (接口要每个成员的读数), 属于定义的验收, 不是翻译带来的. `upd` 一族 (约 25 行) 是 ℕ 上的点更新.
- **缺陷变深还是新思路.** 没有变深 (没有新的翻译). 新信息: (1) 回灌行在闭项里被执行是定理 (此前 `TΛ′` 一行也不执行); (2) "同级拷贝" 在数字层号上可以一次全升, 位置含函数下标也行, 不用世界证据; (3) 第 $n\ge2$ 站的头没有自己的级层: 层是站种类的高度, 头的坐标是 `SL` 高度的层号, 两者之间没有字面对应 (判断, 未写否定定理). `Lv` 的形状仍记为记号引导 (`LeanTLv` 自述).

## §5 接手清单

1. **值 (b) 未做.** 要么对两个 `fb` (回灌与全有损) 写 `ValNew` 式的模拟关系穿过整个折叠, 要么在 `exec-TF0` 的位置上算出第 1 格世界里头 0 的界不是 $0$. 有限测试 ($k\le7$ 的有界展开, 若干路径指纹) 分不出 `TF` 与 `TL`.
2. **第 $n\ge2$ 站头的自己的级层.** 需要层的子层与 `Lv (st n)` 的种类一一对应 (`KindLvRd` 式). 见 [LeanFbRd](LeanFbRd.lagda.md) 头的判断; 未走通, 无否定定理.
3. **级 $\ge2$ 的数字层号拷贝.** 若最高层前接 $\omega$ (`ΛF′ = ω ⊞ up Λs`), 第 $j$ 层对一切世界是第一位置, 可用 `rdN j`/`wrN j` (KindLvRd 限于数字层号) 让一切 `slotUp j` 有回灌 (估计 +130 行, 判断).
4. **含函数层号的拷贝** (`cp2`, 否定一路的 `lossy-hl` 族) 只能按结构位置成组 (`SlotCp.cpSlot` 式, 位置对 `st m` 的塔结构递归), 不能按层号相等成组; 未做.
5. **闲置的新种类回灌机器** (`κc₁` 一族) 在 `TF` 上也不执行; 若将来重写折叠时去掉, 第 3 层约少一百行 (判断, 要先证它对一切 `Λ = up _` 的折叠都不执行, 否定一路的 `kd-Run` 是起点).
