# 单一并上的 ψ₀Λ 折叠: 改一层的界碰到 WLPO

> 摆脱侧 (结构), 没有攀爬. 入口. 接 [CohW](CohW.lagda.md) 的第一个障碍 2. 作者的目标是 "写出 ψ₀Λ 的候选闭项"; 这一路试的是**在一个并 (`SL⋆`) 上写一个折叠**. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延 (`FE` 只作定理的前提). 定义不读记号, 没有验收文件, 没有打开 `EBO`, `Lab`, 标签.
>
> **判决: 没有候选闭项; 在陈述的形式内否定 (定理 + 一条判断).**
>
> 1. **折叠要的世界操作 (判断, 读自 `HtTowerFFold`).** 闭包回灌: 读当前世界在闭包那一层的界, 把**这一层**的界接长, 在升高的世界里跑分支, 再把低层的树搬回原世界 (`drp`, `drp₁`), 所以被升那一层的子层号的界要不变. 写成记录 `RaiseAt` ([CohW2Need](CohW2Need.lagda.md)): 按层号读界 (`World.β`, 即 `CohWGl.glob` 的形状), `r-at` (被升的一层恰好接长), `r-sub` (子层号不变). 比 `CohWUpd.Upd` 弱: 不要求别的层号不变.
> 2. **这些层号确实出现在 `Λ` 之下 (定理).** `Lc c = ofHB (1 ⊞ c)`, $c$ 是可数坐标. 合法世界 `wc (c+1)` 里, 最外是 `ν (Lc c)` 的合法层是 `Λ` 的第一位置 (`lim-layer`, `Lg-lim-layer`, [CohW2Lim](CohW2Lim.lagda.md)). 所以对 `Λ` 的一切合法层工作的折叠, 要在每个 `ν (Lc c)` 上有闭包 (判断: 照 `Ωd`).
> 3. **否定 (定理).** **`raise-Lc→WLPO`**: `FE` (`ℕ → LH` 的函数外延, 作前提) 加上对一切可数坐标 $c$ 的 `RaiseAt (Lc c)`, 推出 **WLPO**. 只用到一族合法的极限坐标 `l⁰ (hα α)` (`Lg-hα`). 不带 `FE` 的形式 `raise-Lc→wdec`: 要么 $\alpha$ 恒假, 要么两个层号不相等. **前提可满足**: 有限层号上 `RaiseAt` 是构造的 (`raiseFin`); 坐标有限时 `Lc (nat n) = fin (n+1)`, 也有 (`raise-nat`). 所以分界正好在**极限坐标**: `Λ` 的第三项 $\Omega_{\Omega_1}$ 之下就有.
> 4. **出路之一, 部分 (定理).** 不搬回, 目标世界跟着长 (`DiagK2` 在 `L′ 1` 上试的那条; 接口是记录 `RaiseGrow`, 与 `RaiseAt` 只差 `r-sub` 换成 "各层只长"). **`growA`**: 增量可数时, `GW` 上对**一切**层号 (含 `ℓα α`) 都有, 构造性的 ([CohW2Grow](CohW2Grow.lagda.md)). 第 0 层的回灌够用; 更高层的回灌增量不可数, 要把坐标在层号之间翻译, 在同一层上翻译回来只是外延的恒等, `g-at` 的等式要函数外延 (判断). 未走通.
>
> **否定的依据与它不说的.** 第 3 条是编译过的定理, 但 "折叠必须用 `RaiseAt`" 是判断 (第 1 条), 所以按 `AGENTS.md`, 这条路线在审核前只能写 "在 `RaiseAt` 这个接口内走不通 (定理)", 不能写成 "单一并上的折叠已否定". 不说的: 界只作关系、不能读的世界 (没有试); `RaiseGrow` 加坐标翻译 (第 4 条, 未走通); `HtFeed` 族之外的折叠 (例如 `BTBO` 那样按路径比较层号; 判断: 在 `lΩ` 处比较两个下标同样要界, 界又要随回灌长); 逐层折叠再取 ℕ-对角 (`DiagK`). 与 `DiagK` 的 `updL′→wdec` 同向: 那里是 `L′ 1` 里函数值的世界分量, 这里是按层号读界的世界, 两者都是 "恰好改一个分量要判定下标相等".

## 设计

| 件 | 定义 | 文件 |
|---|---|---|
| 子层号 | `_≺_` (`LH` 的结构真子项), `Acc`, `wf`, `irr`, `≺→≢` | [CohW2Need](CohW2Need.lagda.md) |
| 世界的接口 | `World` (`Wd`, `β`, `w₀`, `β₀`); `RaiseAt Wo ℓ` (`raise`, `r-at`, `r-sub`); `GWo` (`CohWGl.GW` 的实例) | 同上 |
| 有限层号 | `fin`, `sel` (对层号结构递归选值, 不判定任意层号的相等), `raiseFin` | 同上 |
| `Λ` 之下的层号 | `Lc c = ofHB (hs hz ⊞ ιS lz (cv lz c))`; `nat`, `ω⁰`, `sn`, `sw`, `pickH`, `hα`, `y₀ = Lc ω⁰`, `ℓα α = Lc (l⁰ (hα α))` | 同上 |
| 定理 | `isZ`, `FE`, `WLPO`, `raise-Lc→wdec`, `raise-Lc→WLPO` | 同上 |
| 出现在 `Λ` 之下 | `wc`, `Lg-wc`, `brL`, `lim-layer`, `Lg-lim-layer`, `Lg-hα` | [CohW2Lim](CohW2Lim.lagda.md) |
| 只增长的世界 | `RaiseGrow` (`raise`, `g-at`, `g-grow`), `⊞⁰-fst`, `embA`, `growA` | [CohW2Grow](CohW2Grow.lagda.md) |

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `wf`, `irr`, `≺→≢` | CohW2Need | 子层号良基, 没有层号是自己的子层号 | 定理 |
| `sel-at`, `sel-off`, **`raiseFin`** | CohW2Need | 每个有限层号上 `RaiseAt` 成立 (`GW`) | 定理 (前提可满足的见证) |
| `Lc-z`, `Lc-s`, `Lc-l`, `Lc-nat`, **`raise-nat`** | CohW2Need | `Lc` 把后继读成 `ls`, 极限读成 `ll`; 有限坐标处 `RaiseAt` 成立 | 定理 (`refl` 与归纳) |
| `sw-true`, `sw-false`, `≺-sn`, `y₀≺ℓα`, `pt` | CohW2Need | $\alpha\,n$ 真则 $y_0\prec\ell_\alpha$; $\alpha$ 恒假则逐点 `Lc (hα α n) ≡ Lc (nat n)` | 定理 |
| `raise-Lc→wdec` | CohW2Need | 对一切 `Lc c` 的 `RaiseAt` 推出: $\alpha$ 恒假, 或 `ℓα α ≢ y₀` | 定理 (不用 `FE`) |
| **`raise-Lc→WLPO`** | CohW2Need | `FE` + 对一切 `Lc c` 的 `RaiseAt` 推出 WLPO | 定理 (壁垒形式) |
| `Lg-wc`, **`lim-layer`**, `Lg-lim-layer` | CohW2Lim | 合法世界里, 最外是 `ν (Lc c)` 的合法层是 `Λ` 的第一位置 (一切可数 $c$; 合法性要 $c$ 合法) | 定理 |
| **`Lg-hα`** | CohW2Lim | 定理用到的那族极限坐标都合法 | 定理 |
| `⊞⁰-fst` | CohW2Grow | 接长后原来的界是第一位置, 一切层号一切世界 | 定理 |
| **`growA`** | CohW2Grow | 可数增量时, 一切层号上都有 `RaiseGrow` | 定理 |
| "折叠必须用 `RaiseAt`" | 本篇 | 读自 `HtTowerFFold` 的 `RunM`, `drp`, `drp₁` | 判断 |

## 闭项与读法

**没有闭项.** 没有 `SL⋆` 上的折叠, 没有对角处的序数树, 没有 FGH, 没有强度的定理. 四层表的层 1 到 3 对闭项为空 (见账).

## 第一个障碍

**高层回灌的增量要翻译到一切层.** `RaiseAt` 那条在极限坐标处是 WLPO (第 3 条); `RaiseGrow` 那条, 可数增量没问题 (`growA`), 不可数增量要一个 "把层 $\ell$ 的坐标翻译成层 $y$ 的坐标" 的结构, 并且在 $y\equiv\ell$ 处恰好是恒等. 判断: 没有函数外延时这个等式拿不到 (翻译经过坐标来回, 分支是函数). 可试的方向 (判断, 没有试): 把 `g-at` 放宽成 "新界与 `β ℓ w ⊞⁰ x` 互为第一位置" (值上一致, 不要求相等), 看 `RunM` 的回灌只用到第一位置还是要等式.

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `RaiseAt` 的三条 | `HtTowerFFold` 的回灌 (`RunM`) 与搬回 (`drp`, `drp₁`) | 读自现有折叠 (判断), 不读记号 |
| `RaiseGrow` | 不搬回、目标世界跟着长 (`DiagK2` 的出路) | 树侧; 为与 `DiagK2` 相容写成记录 |
| 子层号 `_≺_` | 只升一层时哪些层必须不变 | 树逼的 (`drp` 只对低层的树) |
| `Lc`, `hα` | `Λ` 的第三项 $\hat\Omega(\hat\Omega(1))$ 的分支, 坐标取一族上升序列 | 树侧 (只用 `CohWGl.Ω̂`, `ofHB`) |
| `FE` 作前提 | 不带它只得到 `raise-Lc→wdec` | 选择 (同壁垒定理的形式: 推出非构造原理) |

**按 `AGENTS.md` 归类: 摆脱侧, 提供信息.** 没有新构造子, 没有节点, 没有闭包定理, 没有 `Lab`. 否定定理划出世界不能有的操作 (`raise-Lc→WLPO`), 分界由可满足的一侧 (`raiseFin`, `raise-nat`, `growA`) 给出. 没有攀爬模块, 所以没有加深.

## 账

**定义级切片** (口径同 `htfeed/locslice_htfeed.py`; 脚本在临时目录 `cohw/locslice_cohw2.py`). 没有闭项, 所以四层表 (层 1 定义, 层 2 +折叠/闭项/FGH, 层 3 +合法) 对 ψ₀Λ 为空; 对照作者的标杆 (`EboLean3` 层 3 为 1513) 与树侧现状 (HtFeed 665, HtTowerF 996, HtTowerN 1062), 本路**没有**新增层 1–3 的行数. 下面是各定理的独立切片.

| 切片 | 行数 (去共用) | 按模块 |
|---|---|---|
| `raise-Lc→WLPO` | 357 (334) | CohWGl 161, CohW2Need 98, HtTowerTy 75, BTBO 23 |
| `raise-Lc→wdec` | 344 (321) | CohWGl 161, CohW2Need 85, HtTowerTy 75, BTBO 23 |
| `raiseFin`, `raise-nat` | 338 (315) | CohWGl 161, CohW2Need 79, HtTowerTy 75, BTBO 23 |
| `lim-layer`, `Lg-lim-layer`, `Lg-hα` | 386 (363) | CohWGl 205, HtTowerTy 90, CohW2Lim 50, BTBO 23, CohW2Need 18 |
| `growA`, `⊞⁰-fst` | 249 (226) | CohWGl 123, HtTowerTy 70, BTBO 23, CohW2Grow 20, CohW2Need 13 |
| 全部 | 535 (512) | CohWGl 205, CohW2Need 147, HtTowerTy 90, CohW2Lim 50, BTBO 23, CohW2Grow 20 |

文件级 (代码块里非空非注释行): `CohW2Need` 169, `CohW2Lim` 61, `CohW2Grow` 28, 入口 5; 共 263.

## 审计

- **导入闭包** (`importclosure.py`, `--only` 表同 `CohW`): `CohW2` (22 个模块, 本地 13), `CohW2Need` (19, 本地 10), `CohW2Lim` (20, 本地 11), `CohW2Grow` (20, 本地 11), 都是退出码 0, 禁用表 0, `--only` 之外 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `CohW2Need:raise-Lc→WLPO` 88/0/0, `raise-Lc→wdec` 83/0/0, `raiseFin` 25/0/0, `raise-nat` 75/0/0, `CohW2Lim:lim-layer` 65/0/0, `Lg-lim-layer` 81/0/0, `Lg-hα` 65/0/0, `CohW2Grow:growA` 17/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58.
- **禁用构造**: 四个文件无 `postulate`, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不用 `--cubical`; 函数外延只作 `raise-Lc→WLPO` 的前提 `FE`.
- **从头编译** (删去本路自己的 `.agdai`, 堆上限 6G): 入口退出码 0 (2.0 秒, 0.39G).
- 行数脚本不含绝对路径 (从仓库根目录运行).

## 时间线

接 `CohW` 之后读过 `src/OCF/BTBO.lagda.md` 的可数序数层布劳威尔树与 $\psi$ 的折叠 (作者的成品, 不是记号), 用来判断 "按路径比较层号" 的路线; 没有打开 `EBO`, `Correspond`, `Label`, 也没有读任何基本列规则.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CohW2 where

open import OCF.Align.CohW2Need using (_≺_; wf; irr; ≺→≢; World; RaiseAt; GWo; fin; sel; raiseFin; Lc; Lc-nat; raise-nat; nat; ω⁰; hα; y₀; ℓα; y₀≺ℓα; FE; WLPO; raise-Lc→wdec; raise-Lc→WLPO) public
open import OCF.Align.CohW2Lim using (wc; Lg-wc; brL; lim-layer; Lg-lim-layer; Lg-hα) public
open import OCF.Align.CohW2Grow using (RaiseGrow; ⊞⁰-fst; embA; growA) public
```
