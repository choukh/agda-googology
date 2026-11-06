# 最高层含与站层号同形的层: 否定一路 (入口)

> 不含记号. 与构造一路 `LamIso` 配对 (作者本轮选定, 原话 "②: 最高层 Λ 含与站层号同形的层"); 接口 [LamIsoIf](LamIsoIf.lagda.md) ("接口定稿 2026-11-05 22:58", 变更记录: 无). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延 (连前提也没有).
>
> **判决: 没有关闭任何路线.** 否定定理只杀写明的形状 (各文件头的 "只否定什么").

## 对纲领与目标

- **纲领 1, 2.** 本路不造闭项; 只写关于接口、构造一路的实例 (`LamIsoPsi`, `LamIsoL`, `LamIsoTm` 23:2x 版) 与几个反例层的定理.
- **纲领 3 (壁垒) 的影子.** 本路的否定都不是 LPO 型的: 证据是种类的继承 (`has⊲`), 构造子差, 或 Burali-Forti 形状 (`prt-br` 的截面). 它们说的是: 同形层的**种类**必须逐项继承 (对角上, 结点的可比分支间), 一种类的塌缩不忠实.
- **目标 (让树自足) [判断].** "按自己的级" 现在写进了接口的类型 (`Prt`: 结点的种类是某个 `Emb (FL k) _` 的新种类的像, 坐标映射就是 `cv`; `OwnRd`: 读回目标就是 `Lv (st n)`). 这是树侧的判据, 不看记号. 本路的定理说明它比旧的 `Sim⁺` 严: `Sim⁺` 被一种类的塌缩 $\Lambda_C$ 满足 (`NegLamIsoPre.ΛC`), `Prt` 不被满足 (`NegLamIsoBlind.ΛC-no-LamIso`). 构造一路的实例满足 `Prt` 对一切 $n$, 头 3 的读回确实产出级为 `st 2` 的种类 `kTop3` (`NegLamIsoRd.top3-has`, 对照旧的 `no-top3-RLs`). 但 `L n` 的形状是 $\hat\Omega^n$ 的逐结点翻译 (`LamIsoPsi` 自述), 提供者经 `subst` 沿 `tw-eq` 取: 层的骨架读自塔 `tw`, 不是读自记号.
- **值.** 没有值定理. 有限测试 `sz′ 7 TI = 7238` 与 `TVs`, `TL` 相同 (无分辨力). [判断] $\Lambda'=\Lambda_L\boxplus\Lambda_F$ 只在 $\Lambda_F$ 前面加 $\Lambda_L$ (`NegLamIsoInst.heads-prefixed`: 站的头都在前缀之后), 增长若有, 要从读回来.

## 文件

| 文件 | 内容 | 依赖 |
|---|---|---|
| [NegLamIsoPre](NegLamIsoPre.lagda.md) | 接口之前: `has⊲`, **`path-illegal`**, **`diag-illegal`**, `has-chain`; **`pathcopy-illegal`** (第 3 站按路径选拷贝), 实例 `Lpath`, 对照 `Lone`; **`station-diag-illegal`**, **`indep-col-illegal`**; 盲 **`ΛC`** (`Lg-ΛC`, `ΛC-fst`, `ΛC-sim`, `col-kind`); `BaseBot`; **`col3-not-own`** | `LeanTBase`, `LeanTLv`, `LeanFbSt`, `LeanLvIf` §6, `NegLeanLvPre` |
| [NegLamIsoAcc](NegLamIsoAcc.lagda.md) | 接口之前: **`⊞-inv`**, `acc-cases`, **`top-cases`**; **`prefix-reads`**, `desc-st`, **`head-not-st`**; 对累加候选 **`cand-no-own`**, **`cand-own-early`** | Pre, `NegLeanLvPre` |
| [NegLamIsoBlind](NegLamIsoBlind.lagda.md) | 接口的盲区与边界: `prt→sim⁺`, **`prt-br`**, **`col-never-prt`**, **`ΛC-no-LamIso`**; **`ΛF-no-LamIso`**, **`ΛF-no-own`**; 正面 `prt2`, `own2`; 盲 **`ownConst`** | `LamIsoIf`, Pre, `NegLeanLvBlind` |
| [NegLamIsoInst](NegLamIsoInst.lagda.md) | 对实例: **`L-no-head`**, **`heads-prefixed`**, **`Sg-gone`**, **`own-in-ΛL`** | `LamIsoPsi`, `LamIsoL` (只读), Pre, Acc |
| [NegLamIsoRd](NegLamIsoRd.lagda.md) | 对实例的读回: **`rd-top3`**, **`top3-has`** (合法世界 `Wi`); **`rd-br0`**, `br0-has`, `succ3`, `succ3-k` | `LamIsoTm`, `LamIsoL` (只读), `NegLeanLvEmb` |
| [NegLamIsoTest](NegLamIsoTest.lagda.md) | 有限测试 `sz-7I` (不是证明; 入口不导入) | `LamIsoTm`, `LeanFbTest` |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLamIso where

import OCF.Lean.NegLamIsoPre
import OCF.Lean.NegLamIsoAcc
import OCF.Lean.NegLamIsoBlind
import OCF.Lean.NegLamIsoInst
import OCF.Lean.NegLamIsoRd
```

## 定理表 (按档)

**[定理, 一般]** `NegLamIsoPre.has⊲` (第一位置继承种类), **`path-illegal`** ($\Omega$-结点界内可比的两支, 前一支有某类种类而后一支没有 ⟹ 不合法), **`diag-illegal`** ($\mathbb N$-极限同理), `has-chain`, `BaseBot`/`bb-L₀` (底世界里界只有底坐标). `NegLamIsoAcc.⊞-inv`, `top-cases` (累加最高层的第一位置: 自己, $P_0$ 里, 或 $P_j\boxplus b'$).

**[定理, 否定]**

- `NegLamIsoPre.pathcopy-illegal`: 顶为头 0 的层, 第 $e$ 支只用第 2 站分量 `inj₂ e` 的拷贝, 第 $1$ 支用了分量 `inj₂ 1` ⟹ 不合法. 前提实例 `Lpath` (与 `st 3` 有 `Sim⁺`).
- `NegLamIsoPre.station-diag-illegal`, `indep-col-illegal` (`no-naive-diag` 的站版): 对角的相邻项各只用自己一站 ⟹ 不合法, 即使每项单独合法且与 `st k` 同形 (`indep-col-each`).
- `NegLamIsoAcc.cand-no-own`, `cand-own-early`: 累加候选 $Y_j=Z_j\boxplus S_j$ 里, 规范读法为 `st n` 的第一位置层只在 $P_0$ 或前三块.
- `NegLamIsoBlind.col-never-prt`, **`ΛC-no-LamIso`**: 一种类的塌缩不忠实 (对一切 $\kappa_0$). `ΛF-no-LamIso`, `ΛF-no-own`: 不改最高层就没有.

**[定理, 盲]** `NegLamIsoPre.ΛC` (旧判据 `Sim⁺` 被一种类满足, 对一切 $n$, 合法); `col3-not-own` (规范读法分得开). `NegLamIsoBlind.ownConst` (`OwnRd` 有常数读回的实例, 只要有 `LamIso`).

**[定理, 对实例]** `NegLamIsoInst.L-no-head`, `heads-prefixed`, `Sg-gone`, `own-in-ΛL`. `NegLamIsoRd.rd-top3`, **`top3-has`** (头 3 读出 `kTop3`), **`rd-br0`**, `br0-has` (过顶结点第 0 支本身也读成 `kTop3`; 23:0x 版里这里有损, 依本路 `succ3` 的提示构造一路加了 `succE`), `succ3`, `succ3-k`.

**[有限测试]** `NegLamIsoTest.sz-7I`: `sz′ 7 TI ≡ 7238` (无分辨力).

**[判断]** (i) 一般 $n$ 上 "按级全局一致地选拷贝" 是否可写, 本路没有否定; 构造一路的 $\Psi$ (前缀逐项继承, 提供者沿坐标选) 是一个写法, 合法 (`Lg-L`, 构造一路). (ii) 头 $n\ge4$ 的读回是否产出级为 `st (n-1)` 的种类, 只查了 $n=3$. (iii) $\Lambda'$ 的值与 $\Lambda_F$ 的关系无定理.

## 前提实例 (否定与条件定理的每个前提)

| 定理 | 前提 | 实例 |
|---|---|---|
| `path-illegal` | 合法世界, 界内 $c\lhd c'$, 一支有一支没有 | `W2`, `lW2`, $1\lhd2$; `Lpath` 的第 1, 2 支 |
| `pathcopy-illegal` | 第 1 支用分量 `inj₂ 1`; 各支只用自己的分量 | `Lpath` (`here refl`, `onlyB`) |
| `station-diag-illegal` | 第 $n$ 项有第 $\sigma n$ 站的结点; 第 $n+1$ 项只用第 $\sigma(n+1)$ 站; $\sigma n\ne\sigma(n+1)$ | `indep-col-illegal` 用 `col (νS (σ k)) (tw k)`, $\sigma=$ 恒等或 `pred′` |
| `cand-no-own` | $b'$ 不含新种类 | `Inst.P3-not-own` ($P_0=0$, $Z=0$, $b'=0$; `P3-fst`) |
| `prt-br` | `Prt T a (lΩ k g)` | `prt2` |
| `ownConst` | `LamIso Λ` | 构造一路的 `lamIso` |
| `heads-prefixed`, `own-in-ΛL` | $\Lambda'$ 的第一位置 | `inst-head`, `inst-own` |
| `rd-top3` | 合法世界, 两个界 | `Wi`, `lWi`, `hself`, `hself` (`top3-has`) |
| `rd-br0` | 底坐标的界 | `botBd` (`br0-has`) |

## 编译

从仓库根: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Lean/NegLamIso.lagda.md +RTS -M6G -RTS`; `NegLamIsoTest` 单独编译.
