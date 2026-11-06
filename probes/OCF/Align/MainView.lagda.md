# 主线数据类型上的布劳威尔树 View

> 入口. 作者 2026-11-05 对纲领 1 的解释: 中间层不直接用布劳威尔树时, 要有内部的、值上一致的布劳威尔树 View; $\mathbb N$-极限按目标树自己的第一位置合法性步进. 已有的 View ([BrwView](BrwView.lagda.md), [BrwWf](BrwWf.lagda.md), [BrwHW](BrwHW.lagda.md)) 建在 `SumOneTree.D` 上. 这里把它们搬到**主线实际的数据类型**: `HtFeedTree.D` (层是高度树 $H$) 与下标塔一路的 `HtTowerFTree.D` (世界成对, 多一个节点 `nμ`). 不改任何已有定义, 不读记号, 不用 `Funext`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> **判决: PARTIAL.**
>
> 1. **对一切层的骨架 (定理).** `MainViewGen.Skel`: 对 `HtFeedTree.D₊` 的一切参数 (主线的每一层 `D L`) 一条定义的 View 与部分良基. 和的五个构造子的读法对一切层相同; 层与层之间只差两个**段** (`SegI`: `ni` 节点, `SegK`: `nκ` 节点) 与它们的下降. `HtTowerFTree.D` 上同形 (`MainViewTower.TSkel`), 段是三个, 多出的就是 **`SegM`** (`nμ` 段).
> 2. **`HtFeedTree` 第 0 层 (定理, 无条件).** View, 部分良基, 值一致 (`sum azero`, 互相 $\le$ 与逐点字面相等), 经 View 的 FGH 与 `sum azero x` 上的 FGH 逐点相等; 对主线闭项 `HtFeedClosed.TΛ Λ lΛ`, 一切合法的 $\Lambda$ (`fgh-TΛ`).
> 3. **`HtFeedTree` 第 1 层 (条件定理, 条件同 SumOne).** 值定义为 `toBᴴ l x = LayerTrOne.toB l (π x)`, `π` 是到 `SumOneTree` 第 1 层的逐构造子改名. 在 `HWᴴ x = HW (π x)` 下有 View; **在这个 View 上部分良基无条件**; 读出的 `B₁` 与 `toBᴴ` 互相 $\preccurlyeq$. 前提可满足 (`HW-Ωᴴ`).
> 4. **主线折叠的输出 (定理, 部分).** 对一切合法的 $\Lambda$, 闭项折叠 (`HtFeedClosed.At`, $S=\cdot\omega$) 在目标第 1 层上: 不变量 `Good` 在 `⊕`, `Step`, `cv`, 沿第 0 层坐标的 `Run` 下保持; 一切**层为 `hz` 的输入节点**的输出 (`keep` 与 `rise` 两种) 都 `HWᴴ`, 条件是节点的分支动作跨世界保持状态关系 (`HB`), 对 `Ωd` 型节点这化为动作本身的性质, 闭项的动作 `Act` 有它. 闭项实例: $\Lambda=$ `hs hz` 时一步 `ΔΩ` 在目标第 1 层的整个输出 `HWᴴ`, View 适用 (`HW-ΔΩ₁`, `view-ΔΩ₁`).
> 5. **`HtTowerFTree` (定理 + 暂停).** 第 0 层: View, 良基, 值一致, FGH 一致, 无条件 (`nμ` 一行是空的). 第 1 层: `nμ` 不出现 (`no-nμ₁`); **第 1 层的 View 暂停**: 成对的世界要读法提供高度分量的合法性 `LgB`, 改名到 `SumOneTree` 的做法不再适用 (`MainViewTower` §4, 判断). `nμ` 要的额外的东西是 `SegM` 的居民, 前提是第 2 层以上的读法 (目标树的第三种 $\Omega$-极限), 仓库里没有.
>
> **暂停, 不是否定:** `nκ` 段的 `HW` (同 `BrwHW` 2, 与 `KVal` 的 `κ⊑` 是同一个缺口, 本篇把 `nκ` 节点的 `HWᴴ` 留在合法性里, 即 View 的显式前提); 层 $\ge 1$ 的输入在目标第 1 层上的 `Run` (`rise` 链在第 1 层上跑, 要把 `RunR` 推广到第 1 层的输入, 同 `BrwHW` 2(b)); `HtTowerFTree` 第 1 层的读法; 第 2 层以上的读法.

## 1 设计

| 件 | 定义 | 文件 |
|---|---|---|
| 骨架 | `Skel` 的参数: 目标签名 `Sig`, 下标的世界 `wd`, 值 `val`, 合法性 `Lgl`, 读法 `Sm q b y`; 九条方程 (`e-n0`, `e-n1`, `e-⨾`, `e-nw`, `e-val`, `e-top` 是 $\equiv$, 实例里都是 `refl`; `e-0`, `e-nl` 是 $\approx$; `fst` 是第一位置); 合法性的七条结构律 | [MainViewGen](MainViewGen.lagda.md) |
| 段 | `SegI`, `SegK` (`HtFeedTree`); 加 `SegM` (`HtTowerFTree`) | 同上, [MainViewTower](MainViewTower.lagda.md) |
| 良基 | `Dec`: 值上的良基秩 `_<ᵣ_`, 后继 `R-s`, 极限 `R-l`, 每个段一条下降 | 同上 |
| 第 0 层 | `Sm q b y = sum b y`, `Lgl = ⊤`, 秩 `SubA` | [MainViewZero](MainViewZero.lagda.md) |
| 第 1 层 | `ι₀` (坐标), `π` (改名), `toBᴴ = toB ∘ π`, `HWᴴ = HW ∘ π`; `ni` 段的部分 `nw p x ⨾ Jι …`, `nκ` 段的部分 `nw p x ⨾ (HtFeedTree.Cut … ⨾ u (q·p) lc)` | [MainViewOne](MainViewOne.lagda.md) |
| 折叠 | `RS`, `ΔR` (经 `π` 的 `R2`), `Shᴴ`, `Good`; `Node` (层为 `hz` 的输入节点), `N1` (`Ωd` 型) | [MainViewHW](MainViewHW.lagda.md) |

**`π` 为什么够.** `HtFeedTree` 第 1 层的节点种类 `StH W k (hs hz)` 只有 `ss hself` (节点层是 `hz`), `NZ (hs hz) = ⊤`; 与 `SumOneTree` 的 `Strict k one`, `NZ one` 一一对应. `ni` 分支的坐标类型不同 (`HtFeedTree.D₀` 对 `SumOneTree.D azero`), `π` 把 `SumOne` 的坐标经 `ι₀` 喂回分支. 反方向不需要: View 的部分直接造在主线类型里 (`Jι` 的输出是主线的树, 坐标仍取 `SumOne` 的第 0 层树, 正是 `π` 喂给分支的那些), 所以没有往返, 不要 `Funext`.

## 2 定理

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `Skel.WithSeg.view`, `Skel.WithSeg.Dec.wf` | MainViewGen | 对一切层: 给定读法、方程、两个段及其下降, 有 View 与部分良基 | **定理** (对一切 `D₊`) |
| `view₀ᴴ`, `wf₀ᴴ`, `view₀ᴴᵂ` | MainViewZero | 主线第 0 层: View, 部分良基 | **定理, 无条件** |
| `rd₀≈ᴴ`, `rd₀≅ᴴ` | MainViewZero | 读出的 `A` 与 `sum azero` 互相 $\le$; 逐点字面相等 | 定理 |
| **`fgh₀≡ᴴ`**, **`fgh-TΛ`** | MainViewZero | 经 View 的 FGH 等于 `sum azero x` 上的 FGH; 对主线闭项 `TΛ Λ lΛ`, 一切合法 $\Lambda$ | **定理** |
| `test-ω`, `test-ω+1` | MainViewZero | $f_\omega(2)=8$, $f_{\omega+1}(1)=2$ 经 View 算出 | **有限测试** |
| `JIπ`, `Jleπ`, `πCut`, `CKsπ`, `tailP≡`, `ps-Spπ` | MainViewOne | 部分的值与段的值一致 ($\approx$); 秩不升 ($\sqsubseteq$); 两个 `tailP` 相等 | 定理 |
| **`view₁ᴴ`** | MainViewOne | 主线第 1 层: 一切 `HWᴴ` 的树有 View, 值一致对 `toBᴴ` | **条件定理** (`HWᴴ`) |
| **`wf₁ᴴ`**, `view₁ᴴᵂ` | MainViewOne | 在这个 View 上部分良基, 不要别的条件 | **定理** (在 View 上无条件) |
| `rd₁≈ᴴ` | MainViewOne | 读出的 `B₁` 与 `toBᴴ` 互相 $\preccurlyeq$ | 定理 (前提同 View) |
| `HW-Ωᴴ` | MainViewOne | 主线的 $\Omega_1$ 差树 `Ωd (hs hz)` 在一切世界上 `HWᴴ` | 定理 (前提可满足) |
| `⊕R`, `StepR`, `cvR`, **`RunR`**, `HW-Run` | MainViewHW | 对一切 $\Lambda$: 状态关系在 `⊕`, `Step`, `cv`, 沿第 0 层坐标的 `Run` 下保持 (跨世界) | 定理 |
| **`Node.HW-RunNi`**, `keep-R2`, `HW-RKi` | MainViewHW | 层为 `hz` 的输入节点在目标第 1 层的输出 `HWᴴ` (两种比较结果), `keep` 时跨世界 `R2` | 条件定理 (`HB`, `HBh`, `Good Y`) |
| `N1.HW-RunNi₁`, `hA-Act` | MainViewHW | `Ωd` 型节点: `HB` 化为动作的性质; 闭项的 `Act` 有它 | 定理 |
| **`HW-ΔΩ₁`**, `view-ΔΩ₁` | MainViewHW | $\Lambda=$ `hs hz`: 一步 `ΔΩ` 在目标第 1 层的输出 `HWᴴ`, View 适用 | **定理** (闭项) |
| `TSkel` | MainViewTower | `HtTowerFTree.D₊` 上的骨架, 三个段 (`SegM` 是 `nμ` 的) | 定理 (对一切 `D₊`) |
| **`Zero.view₀ᵀ`**, `wf₀ᵀ`, `rd₀≈ᵀ`, `rd₀≅ᵀ`, **`fgh₀≡ᵀ`** | MainViewTower | 下标塔第 0 层: 同主线第 0 层, 世界成对 | **定理, 无条件** |
| `no-nμ₁` | MainViewTower | 下标塔第 1 层没有 `nμ` | 定理 |
| 下标塔第 1 层的 View | MainViewTower §4 | 读法要提供 `LgB`; 两种做法的代价 | **暂停** (判断) |
| `nκ` 段的 `HWᴴ`; 第 1 层输入的 `Run` | — | 同 `BrwHW` 2 (a)(b) | **暂停** |

## 3 每个新类型要的东西

- **`HtFeedTree` 第 0 层:** 无. 读法就是主线的 `sum`, 九条方程八条是 `refl`. 节点种类与 `nκ` 的标记都是空类型, 段是空函数.
- **`HtFeedTree` 第 1 层:** 一个值的读法 (本篇定义为 `toB ∘ π`) 与条件 `HWᴴ` (与 SumOne 的 `HW` 是同一件事, 经 `π`). 比 SumOne 多出的只有两件技术件: 坐标改名 `ι₀`, 以及两个 `tailP` 不定义相等 (引理对 `aW ≡ aW′` 一般化).
- **主线折叠:** 目标成对 (高度, 字面世界) 让 `cv` 的关系一行 (SumOne 要按 `cmpF` 分两种结果). 读坐标的节点不再是一个特定的项 (`CvFoldInst.Kn`), 是对一切层为 `hz` 的输入节点的一般定理, 条件 `HB` 只说分支动作.
- **`HtTowerFTree`:** 第 0 层无. 第 1 层: 世界的高度分量的合法性 `LgB` 要由读法提供, 这是 `HtFeedTree` 没有的 (§4 of MainViewTower). **`nμ`:** 一个段 `SegM` (类型在 `TSkel`), 它要第 2 层以上的读法, 目标树要有按世界高度分量分支的第三种 $\Omega$-极限.

## 4 第一个障碍

两个, 平行:

1. **第 1 层输入在目标第 1 层上的 `Run`.** $\Lambda$ 比 `hs hz` 大时, `ΔΩ` 里有层 $\ge$ `hs hz` 的节点, 在目标 `hs hz` 上 `rise`, 链在第 1 层上跑状态自己的差 (第 1 层的树, 含折叠以前产出的读坐标的节点). 要的是 `RunR` 在第 1 层输入上的版本: 输入之间要一个结构的跨世界关系 (`ni` 分支对形状相同的坐标相关), 输出也要满足它 (链的下一项是输出), 所以不变量要从 `R2` (值) 换成结构关系, 再证结构关系推出 `R2`. 这是 `KValSound.snd` 在目标第 1 层上的同形物 (`BrwHW` 2(b) 已指出). 判断: 不含 `nκ` 的输入可以做, 规模两三百行; 含 `nκ` 的输入碰到第 2 个.
2. **`nκ` 段.** 同 `BrwHW` 2(a), 与 `KVal` 的 `κ⊑` (`hi` 档) 是同一个缺口: 分支对层的值单调. 本篇没有新进展, 把它留在 View 的合法性里.

## 5 未做

- 第 2 层以上: 骨架给出 View 的形状, 但仓库里没有第 2 层以上的值的读法 (目标树). 写它是新的读法定义 (目标树要能按更低层的值分支), 不是搬运.
- 第 1 层的 FGH (要 $\Omega$-极限的基本列).
- `HtTowerFTree` 第 1 层的读法 (MainViewTower §4).

## 6 翻译账

| 模块 | 记号读来的字段或形状 | 树逼出的 | 类 |
|---|---|---|---|
| `MainViewGen` | 无 | 和的读法对一切层相同, 层之间只差节点的段 (由 `BrwViewZero`, `BrwViewOne` 的 `vw` 同形逼出); 方程取 $\equiv$ 让实例计算成原来的项 (FGH 一致要字面相等) | 提供信息 |
| `MainViewZero` | 无 | 读法是主线的 `sum`; 度量是值的结构 (同 `BrwWfZero`) | 提供信息 |
| `MainViewOne` | 无. `Jι` 照 `BrwViewOne.J`, 部分照 `BrwViewOne`/`BrwViewKappa` | `π` 由 "节点种类一一对应" 给出; 坐标改名只走一个方向由 "不用 `Funext`" 逼出; `aW ≡ aW′` 由两个 `tailP` 不定义相等逼出 | 提供信息 |
| `MainViewHW` | 无. 方法照 `BrwHWFold` | 目标成对让 `cvR` 变成一行; 一般的节点定理的条件 `HB` 由 `BNi` 的形状 (两次 `Ai`) 逼出 | 提供信息 |
| `MainViewTower` | 无 | 第三个段 `SegM` 由 `nμ` 逼出; 第 1 层的障碍 (`LgB` 要读法提供) 由成对的世界逼出 | 提供信息 |

**按 `AGENTS.md` 归类: 提供信息.** 没有新构造子, 没有改树、折叠或任何已有定义, 没有 `Lab`, 没有序数值验收 (不爬站). 新的定义只有读法 `toBᴴ = toB ∘ π` (第 1 层的值) 与验收用的关系 (`Shᴴ`, `RS`, `ΔR`, `Good`), 都不进数据树与折叠. 骨架是对结构参数的一步定理 (每个构造子一行), 新用到的字段: 和的五个构造子只用读法的方程, 节点只经段.

## 7 审计

**导入闭包** (`importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRuleSpec --only OCF.Align.TLRuleSum --only OCF.Align.TLRule --only OCF.Align.SumOne --only OCF.Align.BrwMid --only OCF.Align.LayerTr --only OCF.Align.NoCumLit --only OCF.Align.HtGen --only OCF.Align.HtFeed --only OCF.Align.HtOut --only OCF.Align.HtTower --only OCF.Align.CvFold --only OCF.Align.BrwView --only OCF.Align.BrwWf --only OCF.Align.BrwHW --only OCF.Align.MainView`), 都是退出码 0, 禁用表 0, `--only` 之外 0: `MainView` 47 个模块 (本地 36, 库 11), `MainViewGen` 14 (本地 6), `MainViewZero` 28 (本地 17), `MainViewOne` 36 (本地 25), `MainViewHW` 40 (本地 29), `MainViewTower` 25 (本地 14). 闭包里没有 `CvFold` 一族.

**定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词): `MainViewGen:view` 31/0/0, `MainViewGen:wf` 50/0/0, `MainViewZero:view₀ᴴᵂ` 99/0/0, `MainViewZero:fgh₀≡ᴴ` 121/0/0, `MainViewZero:fgh-TΛ` 216/0/0, `MainViewOne:view₁ᴴ` 218/0/0, `MainViewOne:view₁ᴴᵂ` 232/0/0, `MainViewOne:rd₁≈ᴴ` 257/0/0, `MainViewHW:HW-ΔΩ₁` 366/0/0, `MainViewHW:view-ΔΩ₁` 373/0/0, `MainViewTower:view₀ᵀᵂ` 153/0/0, `MainViewTower:fgh₀≡ᵀ` 175/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明定义没有受记号启发.

**禁用构造:** 六个文件里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, `Funext`; 选项都是 `--safe --without-K --lossy-unification`. 从头编译 (删本路自己的 `.agdai`), 堆上限 6G, 各模块退出码 0.

代码行 (agda 块里非空非注释): `MainViewGen` 122, `MainViewZero` 100 (含有限测试 6), `MainViewOne` 200, `MainViewHW` 178, `MainViewTower` 213, 入口 8; 合计 821.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MainView where

open import OCF.Align.MainViewGen using (ps; module Skel) public
open import OCF.Align.MainViewZero using (view₀ᴴ; wf₀ᴴ; view₀ᴴᵂ; rd₀≈ᴴ; rd₀≅ᴴ; fgh₀ᴴ; fgh₀≡ᴴ; fgh-TΛ; test-ω; test-ω+1) public
open import OCF.Align.MainViewOne using (D₁; ι₀; π; toBᴴ; HWᴴ; Jι; JIπ; Jleπ; tailP≡; πCut; CKsπ; segI; segK; view₁ᴴ; wf₁ᴴ; view₁ᴴᵂ; rd₁ᴴ; rd₁≈ᴴ; HW-Ωᴴ) public
open import OCF.Align.MainViewHW using (Shᴴ; ι-Sh; module Main; module One; HW-ΔΩ₁; view-ΔΩ₁) public
open import OCF.Align.MainViewTower using (psᵀ; module TSkel; module Zero; no-nμ₁) public
```
