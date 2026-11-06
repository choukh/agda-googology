# 新塔 (入口与判决): 每一处都不落回固定类型

> 不含记号. 目标 (作者原话): "写出 ψ₀Λ 的候选闭项". 本路 (前缀 `NewTwr`) 是 [GenFold](GenFold.lagda.md) 接手清单第 1、2 条的**构造**一路. 否定一路前缀 `NegNewTwr`, 共用接口 [NewTwrIf](NewTwrIf.lagda.md) (接口定稿 2026-11-05 17:39; 变更记录见接口文件头). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提. 无条件闭项与证书无模块参数.
>
> **判决: PARTIAL (类型条件全满足; 值没有定理; 读法 (判断) 远低于 ψ₀Λ, 低于 GenFold 的 `TG`).**
>
> - **(a) 交了.** 无条件闭项 `NewTwrK.TN : A`, 证书 `Lg-TN`, FGH `fghN`. 每站的下降值域是本站读回所在的类型 `HB (Lev B_s)` (不是 `Ht`), 值经 `injL` 原样进下一站层号; 层号对角在 `KΛc` 里; 最终坍缩是 GenFold 的一般折叠在 `step KΛc` 上折到第 0 层, `sum` 成 `A`. 闭项的构造里没有一处的值经过 `Ht`, `T⁺` 或 `rd₂` (切片, 见审计).
> - **(a′) 形状定理 (对一切 $s$, `refl`, 非盲).** 每站的下降就是第 $X_s$ 级之上的求值 (`rd-suc`); 求值输出原样进下一站层号 (`B-suc-ev`) 与层号对角 (`Bᴧ-suc`), 对角原样是闭项的层 (`TN-def`); 每站下降的头是新种类的 $\Omega$-结点, 每站都不是 $2$ (`rd-not-two`, 排除 `dnC`/`dnGenC` 一类). 类型事实 (关于实例 `N₀`, 不是接口的性质, 见否定一路 `codC`): 第 $s+1$ 站值域 `≡ HB (step (Lev X_s))` (`cod-suc`), 第 $s+2$ 站有坐标类型为 `HB (Lev X_s)` 的种类 (`coord-new`), 每站值域与最终层都不是 `Ht` 的收缩 (`cod-no-ret`, `fin-no-ret`). 这些只说形状与类型, 不说大小 (手册 §3.3).
> - **(b) 值: 没有定理.** 不是 ψ₀Λ 已写出. 第一个障碍是编译陈述 (`lossy-rd`, `base-bot`, `keepΛ`, `onlyA-rd₁`): 最终坍缩里层号对角的一切 $\Omega$-结点的种类都没有回灌, 世界里它们的界不被任何回灌改变; 新种类的回灌只喂底种类的结点. 读法 (判断) 见下.
>
> **对纲领与目标.** 纲领 1: 闭项是 `A` (布劳威尔树) 的元素, FGH 在树上算. 纲领 2: 无公理; 塔对站号结构递归 (层号与合法同时), 求值是 GenFold 的一般折叠 (对数据结构递归), 新读回 `rdG` 对数据结构递归. 纲领 3: 折叠里唯一的比较是 `cmpB` (公共上界是最高层); 回灌只在可判定下标上点更新 (`GenFoldInst.upd`, `updL`), 读回分量有损; 没有 "升一份留别份". 纲领 4: 导入闭包与切片干净 (审计). 目标 "让树自足": 塔对 `NewTw` 一条定义; 这一站新用到的字段是 `step` 的新种类本身作求值读回的种类 (`rdG` 把过第 1 层的结点读成坐标为 `HB T` 的 $\Omega$-结点, 不经 `encH`) 与 `TopG.top` (把 `HB T` 的 $\Omega$-结点写成闭包数据, `toDᵀ`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NewTwr where

import OCF.Align.NewTwrIf
import OCF.Align.NewTwrRd
import OCF.Align.NewTwrColl
import OCF.Align.NewTwrEv
import OCF.Align.NewTwrK
import OCF.Align.NewTwrObs
import OCF.Align.NewTwrCmp
```

## 接口 (`NewTwrIf`, 只有类型)

```text
LvV b = Σ (HB (Lev b)) LgB ; RdK K = ∀ b → LgB b → LvV b ; RdTower = ∀ s → RdK (Kc s)
record CollK T : col : (h : HB (step T)) → LgB h → A ; lgCol
CollGenTy = ∀ {T} (G : GenK T) → LgDn T → FbLg G → CollK T
record NewTw : rd : RdTower ; b₀ : HB S₀ ; lb₀ ; cl : CollK KΛc
```

接口里没有 `Ht`, `H₀`, `S₁`, `T⁺`, `rd₂`, `DnTower`, `DnLim`, `EvSys`, `FoldAtK` (骨架总审 §5 的要求, 定稿时已满足). 律的定义域写在接口文件头: `RdK` 与 `CollK.lgCol` 各只有一个下标; 塔里只用分量注入与 `⊞-fst`.

## 类型论证 (从层号到闭项)

| 步 | 值 | 类型 | 依据 |
|---|---|---|---|
| 0 | $b_0=2$ | `HB S₀` | `B-zero` |
| 1 | $B_s$ | `HB (Kc s)`, $B_{s+1}=\mathrm{hs}\,X_s$ | `B-suc` |
| 2 | 第 $s$ 站下降 | `HB (Lev B_s)`; $s+1$ 时 `≡ HB (step (Lev X_s))` | `cod-suc`, `rd-suc` |
| 2′ | 求值的层, 世界, 数据 | `HB (step (Lev X))`, `Wd (step (Lev X))`, `DK (Lev X)` | `NewTwrEv.evN` 的类型 |
| 2″ | 求值的读回 | `rdG : … → HB (step T)` | `NewTwrRd` |
| 3 | 增量 | `injL B_s (…) : HB (Kc (s+1))` | `Twr.inc` |
| 4 | 层号对角 | `Bᴧ s : HB KΛc`, `ΛB = hl Bᴧ` | `Twr.Bᴧ` |
| 5 | 最终层 | `up ΛB : HB (step KΛc)` | `Twr.Lf` |
| 6 | 最终坍缩 | `GenFoldRun KΛc GΛ …`, 第 0 层, `sum` | `NewTwrColl.collΛ`, `TN-def` |
| 7 | 闭项, FGH | `A`, `ℕ → ℕ` | `TN`, `fghN` |

"不再有固定上界": [定理, **关于实例 `N₀`**] `N₀` 的每站值域与最终层都有坐标为 `Ht` 的种类, 到 `Ht` 的任何映射无左逆 (`cod-no-ret`, `fin-no-ret`); `N₀` 的值域类型依赖上一站算出的值 (`cod-suc`, `coord-new`). [判断] 类型族 `s ↦ HB (Lev B_s)` 没有与 $s$ 无关的公共类型上界 (除最终层). **这些不是接口的性质** (否定一路, 已由主审复核): 常数下降时每站值域定义相等于 `Ht` 且有左逆 (`NegNewTwrShape.codC`, `retC`), $b_0=1$ 时第 0 站值域是 `Ht` (`stage0-Ht`), 任何保合法的 `HB (step T) → Ht` 接 `T⁺` 都是 `CollK` (`viaHt`); 接口文件头已加文字更正.

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `toDᵀ`, `qy`, `lWy`, `flatT`, **`rdG`**, `rdG-fst`, **`Lg-rdG`** | Rd | 第 2 层读回进 `HB (step T)`, 对一切 $T$; 合法由形状给出 | 定义; 定理 |
| `At` (`ΔΩ`, `ΨΩ`, `Tψ`, `Lg-Tψ`), `one⊞`, **`collG`**, `GΛ`, `LdΛ`, `flΛ`, **`collΛ`**, `bdΛ` | Coll | 最终坍缩 = 一般折叠到第 0 层再 `sum` (决定性实验, `KΛc` 上) | 构造; 合法是定理; 停机由检查器 |
| `two`, `LX`, `lLX`, `oLX`, `eLX`, `W₀X`, `lW₀X`, `ΩX`, `EvN.out₂`, `out₂N`, **`evN`**, `lg-evN`, **`evN-head`**, `ρ′`, `ρ`, **`rdN`** | Ev | 每站下降, 值域 `HB (Lev b)` | 构造; 定理 (`refl`) |
| **`Twr`** (`B`, `lB`, `inc`, `B-fst`, `Bᴧ`, `ΛB`, `Lf`, `TN`, `Lg-TN`, `fghN`, `stage-in`), `ordN` | K §1 | 对一切 `NewTw` 的塔 | 定义; 合法是定理 |
| `N₀`, **`TN`**, **`Lg-TN`**, **`fghN`** | K §2 | 无条件闭项 | 构造; 无条件 |
| `X`, `B-zero`, **`B-suc`**, `rd-zero`, **`rd-suc`**, **`B-suc-ev`**, **`Bᴧ-suc`**, **`TN-def`**, `rd-head0`, `rd-head`, **`rd-not-two`** | K §3 | 形状 (对一切 $s$) | 定理 (`refl`) |
| **`cod-suc`**, **`coord-new`**, `twB`, **`cod-no-ret`**, `hasΛ`, **`fin-no-ret`** | K §4 | 类型事实 | 定理 |
| **`lossy-rd`**, **`base-bot`** | K §5 | 读回分量的种类无 A-回灌; 基世界里顶坐标是 $0$ | 定理 (`refl`) |
| `Kp`, `keepSL`, `keepKc`, `keepAt`, `keepSℕ`, **`keepΛ`** | Obs §1 | `GΛ` 的一切 A-回灌不动读回分量 | 定理 |
| `OnlyA`, `onlyA-nbA`, **`onlyA-rd₁`**, `aKΛ` | Obs §2 | `rd₁` 的读回只含底种类的 $\Omega$-结点 (一切 $T$) | 定理 |
| **`coll≡ev₀`**, `LX≡`, `W₀X≡`, `ΩX≡`, **`out₂≡`** | Cmp | `collG` 与骨架总审的 `SkelDxGen.Gen0.ev₀` 定义相等; 求值到第 2 层与 GenFold 定义相等 | 定理 (`refl`) |

## 闭项与 FGH 的类型原文

```text
NewTwrK.TN      : A                 -- NT.TN = col collΛ (up (hl NT.Bᴧ)) NT.lLf ; NT = Twr N₀
NewTwrK.Lg-TN   : Lg TN
NewTwrK.fghN    : ℕ → ℕ             -- FLv.FGH (ordN TN)
NewTwrK.N₀      : NewTw             -- record { rd = rdN ; b₀ = hs (hs hz) ; lb₀ = tt ; cl = collΛ }
NewTwrColl.collG : CollGenTy
NewTwrColl.collΛ : CollK KΛc
NewTwrEv.rdN    : RdTower           -- rdN s b lb = hs (ρ′ b) , lρ′ b ; ρ′ (hs X) = evN X
NewTwrEv.evN    : ∀ {S : KS} (X : HB S) → HB (step (Lev X))
```

## 前提实例

- `NewTw`: `N₀` (无条件). `GenK KΛc`, `LgDn KΛc`, `FbLg`, `FbBd`: `GΛ`, `LdΛ`, `flΛ`, `bdΛ` (由 `GenFoldInst` 的 `genKc`, `ldKc`, `flKc`, `bdKc` 组装).
- 求值: 层 `LX X`, 世界 `W₀X X`, 数据 `ΩX X` 取 `GenFoldK` 的 (对一切 $X$).
- `cod-no-ret` 的 `HasHt`: `hasTw (twB s)` (对一切 $s$, 起点 $2$ 使每站层号留着字面的 $2$); `fin-no-ret`: `hasΛ`.

## 读法 (全部是判断; 按骨架总审的要求不用 (R2), 上界只从树形与折叠的回灌算)

| 对象 | 读法 (判断) | 依据, 测到哪里 |
|---|---|---|
| 最终坍缩 `collΛ` 能取到新坐标的种类 | 只有底种类 (第 0 站的 `S₀`, 坐标 `A`) 与沿 `inj₁ tt` 链的拷贝 (A-回灌), 以及 `step KΛc` 的新种类 (回灌值只含底种类结点) | `lossy-rd`, `keepΛ`, `onlyA-rd₁` (定理); 对折叠全程的不变式没写 |
| 层号对角 $\Lambda_B$ 的 $\Omega$-结点在折叠里 | 全部有损, 只在起始 (基) 世界的坐标上取分支, 即底支 | `lossy-rd`, `base-bot` (定理); 否定一路 `NegNewTwrShape.final-lossy` (每个结点都有损, 未复核); "只在基世界取" 是对折叠全程的判断 |
| `TN` | 有效的层是 $\Lambda_B$ 的每个 $\Omega$-结点都换成底支后的可数树 (没有 $\Omega$-结点留下); 每站增量的底支是有限次后继与 ℕ-极限的组合, 所以读 $\psi_0(\Omega_{\alpha})$, $\alpha$ 是一个小的可数序数 ($\omega^k$ 量级, 判断). **远低于 ψ₀Λ, 也低于 GenFold `TG` 的读法** | 上面两行; 没有 `ord TN` 的任何比较 |
| 层号对角 $\Lambda_B$ 本身 (作为输入) | 类型上读 $\le\Lambda$ (`LvKt` 的 R1 类型读法) | 不进闭项的值: 折叠只见底支 |

**结论 (判断).** 类型条件 (值域随站变, 最终坍缩不落回 `Ht`, 对角在 `KΛc`) 全部满足, 而值反而更低: 类型变大本身不给强度. 强度卡在最终折叠 (以及每站求值) 对 "坐标是高度的种类" 没有回灌 (骨架总审的 C6).

## 第一个障碍

1. **[定理] 最终坍缩里读回种类没有回灌, 界不动.** `lossy-rd : ∀ s c κ → fbA GΛ (suc s , (inj₂ c , κ)) ≡ inj₂ tt`; `keepΛ`: 一切 A-回灌的 `rsA` 在每个读回分量 `inj₂ c` 上是恒等; `base-bot`: 基世界里头种类的顶坐标是 $0$. `GenFoldRun` 对 `fbA κ = inj₂ tt` 的旧种类在第 0 层取 "当前世界的分支, 重复 $\omega$ 次", 在更高层保留, 读回 `rd₁` 又只读当前世界 (`SkelDxGen.nc-old-drop` 同型).
2. **[定理] 新种类的回灌只喂底种类.** `onlyA-rd₁`: 对一切 $T$, `rd₁` 的输出的 $\Omega$-结点都是 `aK` 的. 所以即使把层号对角放进 `step KΛc` 的新种类 (有回灌的那一个), 回灌的坐标也只含底种类结点: `GenFoldRun` 的回灌层固定在第 0, 1 层, 只在 $T=S_0$ 时与坐标的级一致 (判断).
3. **缺的东西 (判断, 未写).** (i) 每个种类 $\kappa$ 的 "级层" $\ell_\kappa$ 与读回 `D ℓ_κ → E κ` (层 $c$ 的数据读进 `HB (Lev c)`, 过第 $k\lhd c$ 层的结点读成 `Lev c` 里沿路径 $k\lhd c$ 的种类的 $\Omega$-结点), 让坐标是高度的种类在第 0 层目标下有对级的回灌; (ii) 升这些种类的界: 点更新撞 `upd₁-sep`; "一起升" 在 `FBA` 的字面律下要一个 $R:A\to A\to A$ 使 $a\lhd R\,a\,v$ 恒成立且 $a\lhd v\Rightarrow v\lhd R\,a\,v$, 并保合法, 我没有找到也没有否定 (形状接近 `HtTowerNeg.no-joinA`, 判断); 不经 `FBA` 而改写回灌的折叠要新的 `Run`.

报错原文: 无 (第 1, 2 条是编译过的定理, 第 3 条是没写的东西).

## 采纳骨架总审 (主审转告) 的哪些

- (1) 读法不用 (R2), 上界只从树形与回灌算: 采纳 (上表).
- (2) GenFold 的下降丢掉参数: 本路的下降同样只读层号 (`ρ′ (hs X) = evN X`), 照实写在 `NewTwrEv` 头; 没有改.
- (3) `Gen0.ev₀` 作坍缩字段的实例: 本路的 `collG` 是独立写的同一个式子, `coll≡ev₀` (`refl`) 证两者定义相等; 闭项用 `collG` (导入闭包更小).
- (4) C6 (站与最终坍缩的世界不是基世界, 回灌升坐标为下标的种类的界): 未满足; 本路把它写成编译陈述 (第一个障碍 1, 2), 没有写 "一起升" (理由见第一个障碍 3).
- (5) 接口里不出现 `Ht`/`H₀`/`S₁`/`Sk`/`T⁺`/`rd₂`/`DnTower`/`DnLim`/`EvSys.evH`/`FoldAtK.H`: 定稿时已满足, 未改接口.

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 / 脚手架 |
|---|---|---|
| `RdK` 值域 `HB (Lev b)` | GenFold 接手清单第 2 条: 下降值域随站变 | 树逼出 (读回所在的类型) |
| `rdG` (第 2 层读进 `HB (step T)`), `toDᵀ` | `rd₂` 的推广, 去掉 `Ht` 与 `encH` | 树侧 (新种类坐标就是 `HB T`; `HB T` 的 $\Omega$-结点写成 `nc` 是 `Ωd` 的 $\Omega$-行) |
| `flatT` | 坐标不一定合法, 升界要合法 | 脚手架 (同 `encH`) |
| `ρ b = hs (ρ′ b)` 外包后继 | 让下一站层号的头是后继, 求值那一支定义相等地走到 | 脚手架 (不改读法, 判断) |
| $b_0=2$ | 让每站层号留着字面的 $2$ (`twB`) | 选择 (只为类型事实; 否定一路 `stage0-Ht` 说明 $b_0=1$ 时第 0 站值域就是 `Ht`) |
| `Twr` | `LvKtTower.Tower` 去掉 `FoldAtK.H`, `T⁺`, `cum` | 树侧 |
| `collG` | `HtTowerFClosed.At` 换成 `GenFoldRun` | 树侧 (与 `SkelDxGen.Gen0.ev₀` 同) |
| `keepΛ`, `onlyA-rd₁` | 第一个障碍 | 第 4 层的形状定理, 不改前 3 层 |

归类 (判断): 提供信息. 新定义没有读自基本列规则的字段; 闭包定理没有专属前提; 不用 `Lab`. 信息是: 类型条件满足之后值反而下降, 两条编译定理把原因钉在折叠的回灌上 (只在第 0, 1 层, 只对底种类与 `step` 的新种类). 第 4 层没有改前 3 层.

## 采纳否定一路 (`NegNewTwr`, 主审转告, 已复核) 的哪些

- `codC`, `retC`, `stage0-Ht`, `viaHt`: "不落回 `Ht`" 是关于 `N₀` 的定理, 不是接口的性质; 采纳 (上文与接口的文字更正).
- `rdT-B`, `rdT-Bᴧ` (不求值的下降 `hs (top b)` 使新塔逐站等于截断塔 `KU`): 接口的塔分不出有没有求值; 本路 "求值进了闭项" 只对 `N₀` 写 (`rd-suc`, `B-suc-ev`, `Bᴧ-suc`), 采纳.
- `final-only-bot`, `final-kinds`, `N₀-lossy`: 与本路的 `lossy-rd`, `base-bot`, `keepΛ` 同一结论 (最终坍缩里层号对角的结点没有一个被回灌, 判断); 两路独立得到.
- `fbBd-any` (GenFold §8 的 `FbBd` 对一切 `GenK` 成立, `toE` 取 `bot`): 所以 `NewTwrColl.bdΛ` 不说明回灌绑在种类上; 它只是前提实例, 不作证据.
- `updΛ⁺-sep` (在 `step KΛc` 上 "升一份留别份" 推出分离子): 本路没有用点更新于坐标下标; 第一个障碍 3 (ii) 的升界只能 "一起升" 或带公共上界的更新.
- `not-below`, `N₀-inc-not-below`: 后站的增量不是对角的字面第一位置; 本路只声称部分和是最终层的第一位置 (`stage-in`), 不声称增量是.

## 审计

- **编译.** 七个模块 `OCF.Align.NewTwrRd`, `NewTwrColl`, `NewTwrEv`, `NewTwrK`, `NewTwrObs`, `NewTwrCmp`, `NewTwr` 删自己的 `.agdai` (逐个写精确路径) 后从入口编译, 依赖用共享接口: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/NewTwr.lagda.md +RTS -M6G -RTS`, 退出码 0, 约 4.5 秒, 峰值常驻约 0.85G. 接口 `NewTwrIf` 首次编译 17:39 退出码 0; 加文字更正后重编退出码 0.
- **导入闭包** (`importclosure.py`, 不加 `--only`): 八个模块都退出码 0, 禁用表命中 0. 闭包里有 `HtTowerFClosed` (`T⁺`) 与 `HtTowerFTree` (`Ht`): 经 `GenFoldIf → DnFoldIf → KcFoldTower`, 不可避免 (只要用 `GenK`/`DK`); 所以 "闭项不经 `Ht`" 不是编译器级的保证, 是下一条切片的结论.
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词; `--html` 由 scratch 模块 `NTSlice` (导入 `OCF.Align.NewTwr` 与 `OCF.Align.Om1HnAccept`) 生成, 8G, 退出码 0, 峰值约 2.2G): `NewTwrK:TN` 98/0/0, `Lg-TN` 100/0/0, `fghN` 116/0/0, `N₀` 311/0/0, `NewTwrEv:rdN` 271/0/0, `evN` 254/0/0, `NewTwrColl:collΛ` 247/0/0, `collG` 186/0/0, `NewTwrRd:rdG` 93/0/0, `Lg-rdG` 105/0/0, `NewTwrK:rd-not-two` 285/0/0, `B-suc-ev` 278/0/0, `cod-no-ret` 299/0/0, `lossy-rd` 100/0/0, `NewTwrObs:keepΛ` 106/0/0, `onlyA-rd₁` 84/0/0, `NewTwrIf:NewTw` 69/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用 `NT = Twr N₀` 的实参, 所以 `N₀` 单列为根.
- **闭项不经 `Ht` (切片).** 行数脚本对前 3 层的闭包 (含手工列的模块内定义) 检查 `rd₂`, `rdp₂`, `evAt`, `evB`, `T⁺`, `TΛ`, `encH`, `toD₁` 与 `HtTowerFFold`/`HtTowerFClosed`/`HtTowerFRead` 的块: **无**. (第一版经 `GenFoldEv.EvAt` 的 `open … using (rd₂; …)` 一行在语法上碰到 `rd₂`; 本版在 `NewTwrEv` 里重写了求值的层, 世界, 数据与 `out₂`, 与 GenFold 定义相等, `NewTwrCmp.LX≡`, `W₀X≡`, `ΩX≡`, `out₂≡`.)
- **禁用构造**: 八个文件里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, 函数外延, UIP 前提.

## 四层行数表

`probes/Survey/scripts/newtwr/locslice_newtwr.py` (同 `genfold/locslice_genfold.py` 口径: 定义级切片, agda 块非空非注释行; 模块应用的实参与参数化模块的模块内定义手工列为根, 见脚本头).

| 层 | 无条件 `TN`: 本路新增 / 树侧全部 / 记号 |
|---|---|
| 1 定义 | 18 / 357 / 0 |
| 2 折叠 (读回, 一般折叠, 实例, 下降, 塔, 对角, 闭项, FGH) | 217 / 1264 / 0 |
| 3 证书 | 221 / 1268 / 0 |
| 4 律, 形状, 类型事实, 障碍, 对照 | 336 / 1576 / 0 |

对照 (同口径): 前 3 层树侧 1268, **低于标杆 1513**; GenFold `TG` 2613, `TD` 2580, `Tkc` 1861. 少的原因: 闭项不经 `T⁺`/`HtTowerFFold` (两种种类的折叠) 与截断版的塔 (`LvKtInst`); 一般折叠 `GenFoldRun` 与读回 `GenFoldRd` 的 `rd₁` 部分是主体. 读法比 `TG` 低 (判断), 所以行数少不说明更省.

## 文件与行数

| 文件 | 代码行 / 总行 | 内容 |
|---|---|---|
| `NewTwrIf` | 28 / 108 | 接口 |
| `NewTwrRd` | 91 / 135 | 第 2 层读回进 `HB (step T)` |
| `NewTwrColl` | 52 / 93 | 最终坍缩 (一般折叠到第 0 层) |
| `NewTwrEv` | 63 / 107 | 每站下降 (求值 + `rdG`) |
| `NewTwrK` | 110 / 203 | 塔, 闭项, 形状, 类型事实, 障碍 |
| `NewTwrObs` | 68 / 109 | `keepΛ`, `onlyA-rd₁` |
| `NewTwrCmp` | 28 / 47 | 与 `SkelDxGen.Gen0`, `GenFoldK` 的定义相等 |
| `NewTwr` | 9 / 本文件 | 入口 |
| `probes/Survey/scripts/newtwr/locslice_newtwr.py` | — | 行数脚本 |

## 接手清单

1. **对级的回灌 (第一个障碍 3 (i)).** 先写 "层 $c$ 的数据 ↔ `HB (Lev c)`" 的读回与写入 (对 $c$ 的构造子递归), 在 `S₀` 与 `step S₀` 上与 `rd₁`/`toD₁` 对照; 再写一个折叠, 对每个旧种类 $\kappa$ 在第 0 层目标下按 $\kappa$ 的级回灌.
2. **升界 (第一个障碍 3 (ii)).** 先编译一条小实验: 是否存在合法的 $R:A\to A\to A$, $a\lhd R\,a\,v$ 恒成立, $a\lhd v\Rightarrow v\lhd R\,a\,v$ (若不存在, "一起升" 必须离开 `FBA` 的字面律); 交否定一路对准.
3. **最终坍缩不从基世界起步 (C6, 主审与否定一路的建议).** 最便宜的一步: 给 `At` 加一个起始世界参数, 用随站长高的世界 (读回分量的界取该级的级顶, `KcFoldTop.top` 的形状) 起步, 看 `base-bot` 一类陈述换成什么; 这不是回灌, 只是固定坐标 (判断: 层号对角的结点会在固定的大坐标上取分支, 仍没有迭代), 交否定一路对准.
4. **值.** 对 `N₀` 的前两站做 `ord` 比较 (否定一路建议); 在第 0 站 (`evN {S₀} (hs hz)`) 上与 `GenFoldK.evB hz` (读进 `Ht` 的同一个求值, `NewTwrCmp.out₂≡`) 比较 (`rdG` 与 `rd₂` 只差读回的落点).
