# 新塔: 否定一路的入口

> 不含记号. 本路是 `NewTwr` (构造一路) 的配对**否定**一路 (手册 §5.2), 前缀 `NegNewTwr`. 对着接口 [NewTwrIf](NewTwrIf.lagda.md) ("接口定稿 2026-11-05 17:39 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 分篇: [NegNewTwrCum](NegNewTwrCum.lagda.md) (部分和对角的字面第一位置, 一般引理), [NegNewTwrFeed](NegNewTwrFeed.lagda.md) (最终坍缩的种类结构上的回灌), [NegNewTwrShape](NegNewTwrShape.lagda.md) (塔的形状, 盲区, 最终层里的种类), [NegNewTwrBase](NegNewTwrBase.lagda.md) (基世界), [NegNewTwrBridge](NegNewTwrBridge.lagda.md) (用到构造一路的 `NewTwrK.N₀`, 只读导入构造文件). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FE₀` 只在条件定理 `NegNewTwrFeed.updΛ⁺→WLPO` 里作前提.
>
> **判决: 接口没有被否定 (它的记录都有实例, 不含会撞墙的律). 接口文件头关于 "不落回固定类型" 的两条说法不是接口的后果 (反模型, 定理); 构造一路的最终坍缩在现有实例下没有一个结点被回灌, 且在基世界里起步 (形状定理; 值的后果是判断).**
>
> 1. **嫌疑 (i): 最终坍缩的回灌 (定理).** `step KΛc` (最终层的种类结构) 上 "升第 1 站读回分量里的一份底拷贝, 留另一份" 推出分离子 (`updΛ⁺-sep`; `FE₀` 下 WLPO), 两半各自可满足. 接口明说不含这条律, 本路说明这是被逼的. 跨站拷贝 (`no-emb→`) 与世界映射 (`no-wmatch`) **不落在接口上**: 最终层里没有嵌入拷贝的种类 (`final-kinds`, 定理), 折叠没有种类结构之间的世界映射 (判断, 同 `NegGenFold` 第 3 条). 另: GenFold 接口 §8 的 `FbBd` 对一切 `GenK` 成立 (`fbBd-any`, 盲).
> 2. **嫌疑 (ii): 读回经 `injL` 进下一站 (定理).** 接口的塔用 `⊞` 接读回 (`emb B_s ⊞ injL B_s r_s`), 不撞 `no-two-nxt`/`trap`. 但对角是部分和, 后站的读回**不是**对角的字面第一位置: 第 0 站的读回含 $\Omega$-结点时, 对一切 $j\ge2$, 纯于第 $j$ 站且含 $\Omega$-结点的高度都不是 $\Lambda_B$ 的第一位置 (`tw-not-below`; 一般引理 `CumTrap.Diag.Bad.not-below`, 推广 `stage-not-below`); 构造一路的 `N₀` 上成立 (`N₀-inc-not-below`). `no-faithfulB` 的对象 (到 `Ht` 的下降) 不在接口里; 接口自己引用 `no-faithful` 的那条说法见第 4 条.
> 3. **嫌疑 (iii): 盲 (定理, 反模型).** 接口没有 "读回进了闭项" 或 "不封顶" 的律 (文件头自述). 本路补三个反模型: 常数下降 (`NC`: 层号与对角不长, `constB`, `constΛ`; 闭项 $0$, `TC`); 不求值的下降 `rdT` 给出截断塔 `KU` 的层号与对角 (`rdT-B`, `rdT-Bᴧ`): 接口的塔不区分有没有求值; 经 `Ht` 再 `T⁺` 的坍缩也是 `CollK` (`viaHt`).
> 4. **嫌疑 (iv): 固定类型 (定理).** 接口文件头 "[定理, 构造文件] 每站的下降值域…都不是 `Ht` 的收缩": 对接口的一般 `NewTw` 不成立. 常数下降时**每站**值域定义相等于 `Ht` 且有左逆 (`codC`, `retC`); `b₀ = 1` 时第 0 站值域是 `Ht`, 对一切下降 (`stage0-Ht`). 构造一路取 `b₀ = 2` 并逐站留着字面的 $2$ (`NewTwrK.twB`, `cod-no-ret`), 所以那条说法对 `N₀` 成立; 它是对 `N₀` 的定理, 不是接口的. 最终层的类型确实不是 `Ht` 的收缩 (`hasΛ⁺`, `no-ret-final`, 对照).
> 5. **补充义务 (主审转告): 固定值域与基世界.** 接口里唯一与站无关的值域是 `CollK.col : … → A`: 它是闭项本身的类型 (纲领 1: 闭项是布劳威尔树), 不是中间值域, 不封顶 (判断; 能落回的中间类型在 `viaHt` 那样的实现里, 接口不排除). 站的世界: 构造一路的站求值在 `(w₀ (genLev X) , hz)`, 最终坍缩在 `(w₀ GΛ , hz)` (只读观察), 两者里 `step` 的一切种类的界之下只有 `bot` (`stage-only-bot`, `final-only-bot`, 定理). 与第 1 条合读: 最终层里**没有** `step KΛc` 的新种类 (`final-kinds`), 层号对角的每个结点在 `GΛ` 下有损 (`final-lossy`, 起点无 $\Omega$-结点; `N₀-lossy`), 有损一支读当前世界的分支. [判断] 最终坍缩在基世界里读对角的每个 $\Omega$-结点, 只见底支 (对照 `code-botK`); 站的求值里第 $X$ 级本身的旧种类同样只见底支, 新种类 (每站的内容) 有回灌. 没有对 `Run` 全程的不变式, 没有 `ord` 的比较.
>
> **对纲领与目标.** 纲领 3: 推出分离子/WLPO 的只有点更新的 "留" (裸下标比较), 条件 `FE₀`; 接口不要这条律. 纲领 1: 一切定理对 `HB`/`Lev`/`KΛc`, 反模型给出合法闭项 (`NC` 的 `TC`). 目标 "让树自足": 本路给出的树侧判据是 (a) **部分和对角只把第 1 站的读回作字面第一位置, 更后的站只能在值上进入** (`tw-not-below`); (b) **最终层的种类全是旧种类, 且在现有实例下全有损** (`final-kinds`, `final-lossy`): 要让对角的结构进闭项, 最终坍缩要么给读回分量的种类找一种不 "升一份留别份" 的回灌 (`updΛ⁺-sep` 划出的边界, "一起升" 未否定), 要么换掉基世界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegNewTwr where

import OCF.Align.NegNewTwrCum
import OCF.Align.NegNewTwrFeed
import OCF.Align.NegNewTwrShape
import OCF.Align.NegNewTwrBase
import OCF.Align.NegNewTwrBridge
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `split⊞`, `free⊞`, `CumTrap.pureR`, `pureL`, `Diag.cum-mono` | Cum | `⊞` 的第一位置; 纯性 | 定理 |
| **`CumTrap.Diag.Bad.below`**, **`not-below`** | Cum | 部分和对角: 第 $m$ 个增量含 $\Omega$-结点 ⇒ 第 $j>m+1$ 站的含 $\Omega$-结点的纯高度不是第一位置 | 定理 (否定) |
| `κΛ`, `PtUpdBΛ`, **`updΛ-sep`**, `PtUpdBΛ⁺`, **`updΛ⁺-sep`** | Feed §1 | `KΛc`/`step KΛc` 上点更新 (升 + 留) ⇒ 分离子 | 定理 (否定) |
| `updΛ⁺→WLPO` | Feed §1 | 同上 ⇒ WLPO | 条件 (`FE₀`) |
| `upΛ`, `stayΛ`, `halfΛR`, `halfΛK`, `halfΛ⁺R`, `halfΛ⁺K` | Feed §1 | 两半各自可满足 | 定理 (前提实例) |
| `genΛ`, `genΛ⁺`, `ldΛ⁺`, `flΛ⁺`, **`lossyΛ`**, **`lossyΛ⁺`**, `newΛ⁺` | Feed §2 | 现有实例在读回分量种类上有损 | 定理 (`refl`) |
| **`fbBd-any`**, `fbBd₁` | Feed §3 | GenFold 接口 §8 `FbBd` 对一切 `GenK` 成立 | 定理 (盲) |
| `hasΛ⁺`, `no-ret-final` | Feed §4 | 最终层类型不是 `Ht` 的收缩 | 定理 (对照) |
| `Sh` (`B`, `r`, `inc`, `δ`, `Bᴧ`, `ΛB`, `Lf`, `TN`) | Shape §1 | 接口文件 "塔的形状" 的定义 | 定义 |
| `rdC`, `clC`, `NC`, **`constB`**, **`constΛ`**, **`codC`**, **`retC`**, `TC` | Shape §2 | 常数下降: 每站值域是 `Ht`, 有左逆; 不长; 闭项 $0$ | 定理 (反模型) |
| **`viaHt`**, `viaHt-factor` | Shape §2 | 经 `Ht` 的坍缩是 `CollK` | 定理 (反模型) |
| **`stage0-Ht`** | Shape §2 | `b₀ = 1` ⇒ 第 0 站值域是 `Ht`, 对一切下降 | 定理 |
| `rdT`, `NT`, **`rdT-B`**, **`rdT-Bᴧ`** | Shape §3 | 不求值的下降给出截断塔 `KU` | 定理 (反模型) |
| `AllK`, `all⊞`, `allι`, `allUp`, `allMap`, `allFree`, `OKΛ`, `OK⁺`, `Lossy` | Shape §4 | 每个 $\Omega$-结点的种类满足 $P$ | 定义; 定理 |
| **`Fin.final-kinds`** | Shape §4 | 一切 `NewTw`: 最终层只有起点与读回分量的旧种类, 无新种类, 无嵌入拷贝 | 定理 |
| **`Fin.final-lossy`**, `final-lossy⁺` | Shape §4 | 起点无 $\Omega$-结点: 对角每个结点在 `genΛ`/`genΛ⁺` 下有损 | 定理 |
| **`NB.tw-not-below`**, `NB.inc-not-below`, `nfT`, `nfδT`, `incT-not-below` | Shape §5 | 读回不是对角的字面第一位置; 前提实例 | 定理 (否定; 前提实例) |
| `only-botG`, `only-botKcG`, `only-botΛG`, **`stage-only-bot`**, **`final-only-bot`**, `final-top-bot` | Base | `GenK` 的基世界 (站求值, 最终坍缩) 里只有 `bot` | 定理 |
| `B≡`, `Bᴧ≡`, **`N₀-lossy`**, **`N₀-kinds`**, **`N₀-inc-not-below`** | Bridge | 用到构造一路的 `N₀` | 定理 |

## 每条律为什么是构造一路需要的

- **`CollK`, `CollGenTy`** (接口 §2): 最终坍缩的类型; 构造一路 `NewTwrColl.collG` 实现它, 内部是 `GenFoldRun` 在 `step KΛc` 上, 起始世界 `(w₀ G , hz)`. 它要 `GenK KΛc` 的 `fbA` 给每个种类一个回灌或 "有损". `updΛ⁺-sep` 说读回分量的种类不能用 "升一份留别份" 去填; `final-kinds`, `final-lossy`, `final-only-bot` 说现有的填法下最终层的结点都有损, 起始世界只有底坐标.
- **`RdK`, `RdTower`** (接口 §1): 每站的下降; 接口文件头的类型论证 (步 2) 与 "[定理, 构造文件] … 不是 `Ht` 的收缩" 都对着它. `codC`, `retC`, `stage0-Ht` 说这些说法要具体的下降与起点.
- **`NewTw`** 与 "塔的形状" (接口 §3 与文件头): 构造一路的闭项 `NewTwrK.TN` 是 `Twr N₀` 的闭项 (`B≡`, `Bᴧ≡`). `tw-not-below` 对着 "读回进了闭项" 的字面读法; `rdT-B` 对着 "新塔" 与旧截断塔的区别.
- **GenFold 接口 §8 `FbBd`**: `NewTwrColl` §3 给 `GΛ` 造了 `bdΛ : FbBd GΛ` 作 "A-回灌绑到种类上" 的前提实例; `fbBd-any` 说它对一切 `GenK` 成立, 不绑.

## 前提实例

- `updΛ-sep`, `updΛ⁺-sep`: 两半 `halfΛR`/`halfΛK`, `halfΛ⁺R`/`halfΛ⁺K`; 分离子经典地成立 (判断); `FE₀` 在 Agda 里证不出也否证不了 (与 `ColimWNeg`, `NegGenFoldUpd` 同档).
- `CumTrap.Diag.Bad`: 实例 `incT-not-below` (旧截断塔, `nfT`), `N₀-inc-not-below` (构造一路的塔, 前提 `λ ()`).
- `final-lossy`: 起点无 $\Omega$-结点, 实例 `b₀ = 2` (`fr₀`), `b₀ = 1` (`NC`, `NT`).
- `stage0-Ht`: `NC`, `NT` 的起点是 1.
- 接口记录: `RdK`/`RdTower` (`rdC`, `rdT`), `CollK` (`clC`, `viaHt`), `NewTw` (`NC`, `NT`); `CollGenTy` 的前提 (`genΛ⁺`, `ldΛ⁺`, `flΛ⁺`; 构造一路的 `GΛ`, `LdΛ`, `flΛ`).

## 只否定什么, 不否定什么

- **否定** (编译的): `KΛc`/`step KΛc` 上对一切世界一致的 "升一份底拷贝, 留另一份" (分离子; `FE₀` 下 WLPO); 部分和对角里第 $j\ge m+2$ 站的含 $\Omega$-结点的纯高度作字面第一位置; 基世界里非底坐标在界之下. 反模型否定的推断: "满足 `NewTw` 的塔每站值域不是 `Ht` 的收缩"; "满足 `CollK` 的坍缩不经 `Ht`"; "新塔的形状说明有求值"; "`FbBd` 说明回灌升了这个种类的界".
- **不否定**: 接口的任何记录或定义; 构造一路的 `N₀` 的值 (没有 `ord` 定理); "一起升" 的回灌; 不在基世界里起步的最终坍缩; 对角在值上越过每一站. 路线状态: 本路**没有关闭任何路线**.

## 判断 (单列)

- **最终坍缩没有回灌.** 依据: `final-kinds` (层里无新种类), `final-lossy` (对角结点在 `GΛ` 下全有损), `GenFoldRun` 的定义 (旧种类在第 0 层走 `RKa (fbA G κ)`, 有损一支 `ω⋅ (… u q₀ lW …)` 读当前世界的分支; 新种类的回灌只对 `nc (inj₂ tt)`), `final-only-bot` (起始世界只有底坐标), 构造一路 `NewTwrObs.keepΛ` (A-回灌不动读回分量). 读法: 闭项看到的是对角在底支上的值, 每个 $\Omega$-结点乘 $\omega$. 要写成定理, 须对 `Run` 全程写 "世界的读回分量不变" 的不变式, 或直接比 `ord TN`. 建议构造一路先对 `N₀` 的第 0, 1 项做 `ord` 的比较.
- **站的求值.** 新种类 (坐标 `HB (Lev X)`) 有回灌, 读回进 `HB (step (Lev X))` (`NewTwrRd`), 这是新塔与旧塔的真区别 (`NewTwrK.rd-head`); 第 $X$ 级本身的旧种类有损地读, 在基世界里只见底支 (`stage-only-bot`). 所以每站读到的是 "第 $X$ 级之上一级" 的新结点, 第 $X$ 级的内部结构只经底支.
- **读法不按来历读下标** (主审 R2): 本路的读法只用种类所在的分量与世界里的界, 不用 "这个下标是哪一站算出来的".

## 审计

- **编译.** 删本路六个模块的 `.agdai` (精确模块名 `OCF.Align.NegNewTwrCum`, `OCF.Align.NegNewTwrFeed`, `OCF.Align.NegNewTwrShape`, `OCF.Align.NegNewTwrBase`, `OCF.Align.NegNewTwrBridge`; 入口此前没有接口) 后从入口编译, 依赖用共享接口, `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/NegNewTwr.lagda.md +RTS -M6G -RTS`, 退出码 0, 峰值常驻约 0.70G, 用时约 4 秒. 对着的接口: `NewTwrIf` 定稿 17:39 版 (无变更记录). `NegNewTwrBridge` 导入的构造文件是 17:43–17:44 的 `NewTwrK`, `NewTwrEv`.
- **导入闭包** (`importclosure.py`, 不加 `--only`): 六个模块都退出码 0, 禁用表命中 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词; `--html` 由导入本入口与 `OCF.Align.Om1HnAccept` 的 scratch 模块生成, 6G, 退出码 0): `not-below` 34/0/0, `updΛ⁺-sep` 140/0/0, `updΛ⁺→WLPO` 146/0/0, `lossyΛ⁺` 100/0/0, `fbBd-any` 16/0/0, `no-ret-final` 82/0/0, `retC` 101/0/0, `viaHt` 200/0/0, `stage0-Ht` 98/0/0, `rdT-Bᴧ` 178/0/0, `final-kinds` 111/0/0, `final-lossy` 143/0/0, `tw-not-below` 118/0/0, `incT-not-below` 147/0/0, `final-only-bot` 106/0/0, `stage-only-bot` 89/0/0, `N₀-lossy` 371/0/0, `N₀-inc-not-below` 379/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58.
- **禁用构造**: 六个文件没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`; 函数外延 `FE₀` 只作 `updΛ⁺→WLPO` 的前提; 没有 UIP 前提.

## 文件与行数

| 文件 | 代码行 / 总行 | 内容 |
|---|---|---|
| `NegNewTwrCum` | 73 / 112 | `split⊞`, 部分和对角的第一位置 |
| `NegNewTwrFeed` | 103 / 175 | `step KΛc` 上的点更新, 有损实例, `FbBd` 盲, 对照 |
| `NegNewTwrShape` | 186 / 286 | 塔的形状, 反模型, 最终层的种类, 读回不是第一位置 |
| `NegNewTwrBase` | 40 / 74 | 基世界里只有 `bot` |
| `NegNewTwrBridge` | 39 / 62 | 用到构造一路的 `N₀` |
| `NegNewTwr` | 7 / 本文件 | 入口 |
