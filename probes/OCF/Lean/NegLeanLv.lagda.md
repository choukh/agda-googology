# 头按自己的级读回: 否定一路 (入口)

> 不含记号. 与构造一路 `LeanLv` 配对 (作者原话 "LeanFb: 头按自己的级读回"); 接口 [LeanLvIf](LeanLvIf.lagda.md) ("接口定稿 2026-11-05 22:11", 22:20 只增 §6 `Sim⁺`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延 (连前提也没有).
>
> **判决: 没有关闭任何路线.** 否定定理只杀写明的形状 (各文件头的 "只否定什么").

## 对纲领与目标

- **纲领 1, 2.** 本路只写关于构造一路的闭项 `TV` (沿 `Sim`), `TVs` (主候选, 沿 `Sim⁺`) 与接口的定理, 不造新闭项. 值的比较用 `HB S⊥` 上通常的布劳威尔树的序 ([NegLeanLvVal](NegLeanLvVal.lagda.md)).
- **纲领 3 (壁垒) 的影子.** 本路的否定都不是 LPO 型的: `no-sim` 的证据是一处可判定的构造子差. 它说的是 **现有 $\Lambda_F$ 的级层表太小**: 级层必须对一切世界是 $\Lambda_F$ 的字面第一位置 (`LvRd.ℓ⊲`), 而基世界里每个头的界是 $0$, 所以只剩 $0$, 站层 $S_m$, $\Lambda_F$ (`lvl-cases`).
- **目标 (让树自足) [判断].** "按自己的级" 在接口里是同形 `Sim` (层与层号逐构造子对上) 加恒等嵌入. 这是树侧的判据, 不看记号; 按这个判据, 头 $0,1,2$ 有自己的级层 ($0$, $S_0$, $S_1$; `sim0`, `sim1`, `sim2`), 头 $n\ge3$ 在 $\Lambda_F$ 里**没有** (`no-sim`, 对任意坐标映射; `no-sim⁺`). 构造一路对头 $n\ge3$ 用 $S_1$ 加嵌入 `emb2`, 按它自己接口的定义不是 "自己的级", 它已如实写明. 由此的读法: 头 $n\ge3$ 的界只在 `Lv (st 2)` 的那份拷贝里长 (`no-top3⁺`: 坐标为 `HB (Lv (st 2))` 的种类读不出), 是 `NegLeanFbInst.rdX-one-kind` 高一层的版本. 要往上走, 判断是要改 $\Lambda$ (加与 `st n` 同形的层); 由 `st3-branch`, `no-station-at`, 这样的层在一处要用站里的拷贝种类作头.
- **值.** 构造一路的值定理未走通 (`LeanLvVal` 自述). `absorb-D` 说 "回灌那一行每格严格大于有损格" 推不出闭项严格大: 每格的值被有损格的固定倍数界住时, 求和后值相同.

## 文件

| 文件 | 内容 | 依赖 |
|---|---|---|
| [NegLeanLvPre](NegLeanLvPre.lagda.md) | 接口之前: `no-retract` (重写); `lvK`, `lvK-not-self`; **`lvl-cases`**, `lvrd-cases`; 规范读法 `ofL`, `own0/1/2`, **`no-own`**, **`big-half`**, `big-Λ`; `succK-co`; `st-not-ls2`, `st3-branch`, `no-station-at` | `LeanTLv`, `LeanFbSt`, `LeanFbIf` |
| [NegLeanLvVal](NegLeanLvVal.lagda.md) | 接口之前: 值的序; **`absorb`**, **`absorb-D`**, `succ-absorb`, `below-absorb`, **`strict-cell`** | `LeanTBase`, `LeanTTree` |
| [NegLeanLvBlind](NegLeanLvBlind.lagda.md) | 接口的盲区与边界: **`simConst`**, `sim-any-k`; `sim0/1/2`; **`no-sim`**, **`no-own-sim`** | `LeanLvIf`, Pre, `NegLeanFbBlind.rdConst` |
| [NegLeanLvEmb](NegLeanLvEmb.lagda.md) | `emb2 1` 的像: `kTop3-co`, **`img-left`**, **`miss-top`** | `LeanLvEmb` (只读) |
| [NegLeanLvInst](NegLeanLvInst.lagda.md) | 对 `LeanLvRd`: **`img-readS`**, **`no-top3`**; **`rdΩ-top-lossy`** (对照 `succK-co`) | `LeanLvRd` (只读) |
| [NegLeanLvTm](NegLeanLvTm.lagda.md) | 对 `TV`: **`exec-TV2`**, `own-head2`, **`not-own-head`**, `no-top3-RLv`, **`rd-Ωd`** (读成 $b+2$), `rd-deep` | `LeanLvTm` (只读) |
| [NegLeanLvS](NegLeanLvS.lagda.md) | 对主候选 `TVs`: `fromSim⁺`, **`no-sim⁺`**, `toSim⁺`; **`img-readS⁺`**, **`no-top3-RLs`**; **`rd-Ωd⁺`**, **`exec-TVs2`** | `LeanLvRdS`, `LeanLvTmS` (只读) |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLeanLv where

import OCF.Lean.NegLeanLvPre
import OCF.Lean.NegLeanLvVal
import OCF.Lean.NegLeanLvBlind
import OCF.Lean.NegLeanLvEmb
import OCF.Lean.NegLeanLvInst
import OCF.Lean.NegLeanLvTm
import OCF.Lean.NegLeanLvS
```

## 定理表 (按档)

**[定理, 刻画与边界]**

- `NegLeanLvPre.lvl-cases`: $\ell\lhd_{w_0}\Lambda_F$ ⟹ $\ell=\Lambda_F$, $\ell=0$, 或 $\ell=S_m$ ($S_m$ = `up (1 ⊞ tws m)`). `lvrd-cases`: 接口 `LvRd SLs ΛF Q` 的一切实例的级层都在这张表里.
- `NegLeanLvBlind.no-sim`: $\forall n$, $\ell\lhd_{w_0}\Lambda_F$ ⟹ `¬ Sim SLs ℓ (st (3+n))` (任意 `cv`). `no-own-sim`: 一切 `LvSim SLs ΛF Q` 的层号 $\ne$ `st (3+n)`. `NegLeanLvS.no-sim⁺`: 同样对 `Sim⁺`.
- `NegLeanLvPre.no-own`: 规范读法 `ofL ℓ` 与 `st (3+n)` 不外延相等 (`≈`). `big-half`: $m>n$ 时 `HB (Lv (ofL Sₘ))` 不是 `HB (Lv (st n))` 的收缩 (`no-retract`).
- 正面: `own0`, `own1`, `own2`; `sim0`, `sim1`, `sim2`.

**[定理, 对实例]**

- `NegLeanLvInst.img-readS`, `NegLeanLvS.img-readS⁺` (对一切 $T$): 读回只产出 `j Em` 的像里的种类. `NegLeanLvEmb.miss-top`: `emb2 1` 的像不含 `kTop3` (坐标 `HB (Lv (st 2))`). 合起来 `no-top3-RLv` (`TV`), **`no-top3-RLs`** (`TVs`): 头 3 的读回不产出 `kTop3` 的 $\Omega$-结点.
- `NegLeanLvInst.rdΩ-top-lossy` (`refl`): 沿 `Sim` 过 $\Omega$-极限一支本身的结点有损; `NegLeanLvPre.succK-co` (`refl`): 头 2 那里有忠实的种类. 构造一路据此加了 `Sim⁺` (接口 §6) 与 `TVs`; `NegLeanLvTm.rd-Ωd` (`TV`: $\Omega_{S_1}$ 读成 $b+2$) 对 `NegLeanLvS.rd-Ωd⁺` (`TVs`: 读成后继种类的 $\Omega$-结点).
- `NegLeanLvTm.exec-TV2`, `NegLeanLvS.exec-TVs2` (`refl`): 头 2 的按级回灌行在闭项的计算里出现.

**[定理, 盲]** `simConst` (`LvSim` 有不看数据的实例, 对一切 $T,\Lambda,Q$); `sim-any-k` (`Sim` 不决定层号首项); `toSim⁺` (§6 不逼后继种类).

**[定理, 值]** `NegLeanLvVal.absorb`, **`absorb-D`**, `succ-absorb`, `below-absorb`, **`strict-cell`**.

**[判断]** (各文件结论段单列) "子层与种类对应" 取 `ofL`/`Sim` 是我们与构造一路共同的选择; 头 $n\ge3$ 的界只在 `Lv (st 2)` 的拷贝里长 (`no-top3` 只证了 $n=3$); 要头 $n\ge3$ 有自己的级须改 $\Lambda$ (未研究); `TVs` 的值没有定理, 也没有测试能分辨.

## 前提实例 (否定与条件定理的每个前提)

| 定理 | 前提 | 实例 |
|---|---|---|
| `lvl-cases`, `no-own`, `no-sim`, `no-sim⁺` | $\ell\lhd_{w_0}\Lambda_F$ | `lvl-inst m` ($S_m$), `z⊲ᴮ ΛF`, `hself` |
| `lvrd-cases`, `no-own-rd` | `LvRd SLs ΛF Q` | `simConst`'s `R`; 构造一路 `RLv m`, `RLs m` |
| `no-own-sim` | `LvSim SLs ΛF Q` | `simConst SLs ΛF Q` (`no-own-sim-inst`); `lvSim (1+m)` (`not-own-head`) |
| `big-half`, `big-Λ` | 任意 $d$, $u$ | 前提是收缩本身 (被否定的对象); 种类 `kAt` 存在 (构造) |
| `no-top3`, `no-top3⁺` | 起点在像里 | 起点 $0$ (`no-top3-hz`); 一切 `Sim T a (st 2)`, 例如 `σ₂`, `σ₂⁺` |
| `absorb`, `absorb-D` | $c\le f_n\le c\cdot K$ | `succ-n1`, `succ-ω` (经 `succ-absorb`, $K=2$) |
| `strict-cell` | `1 ≤ sum 0 x` | $x$ = `n1` |

## 编译

从仓库根: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Lean/NegLeanLv.lagda.md +RTS -M6G -RTS`, 退出码 0.
