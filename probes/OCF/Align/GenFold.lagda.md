# 对一般种类结构的数据树与折叠 (入口与判决)

> 不含记号. 目标 (作者原话): "写出 ψ₀Λ 的候选闭项". 本路 (前缀 `GenFold`) 是 [DnFold](DnFold.lagda.md) 接手清单第 2 条的**构造**一路: 对一般种类结构的数据树与折叠, 使第 2 站起的下降有内容. 否定一路前缀 `NegGenFold`, 共用接口 [GenFoldIf](GenFoldIf.lagda.md) (接口定稿 2026-11-05 16:59; 变更记录: 只增 §6 `LgDn`, §7 `FbLg`, §8 `FbBd`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提. 无条件闭项与证书无模块参数.
>
> **判决: PARTIAL.**
>
> - **(a) 交了.** 数据树 `DK T` 与折叠 `GenFoldRun.Run` **对一切种类结构 $T$ 一条定义** (层 `HB (step T)`, 世界 `Wd (step T)`, 一个闭包结点 `nc κ` 对一切种类); `evSysG : EvSysK T` 对一切带 `GenK T`, `LgDn T`, `FbLg` 的 $T$ (接口 `EvSysK` 第一次有实例); 这三样对 `Lev x` (对 $x$ 结构递归) 与 `Kc s` (对 $s$ 递归) 都有实例. 第 1 站的决定性实验 `evK₁ : EvSysK (Kc 1)` 编译通过. 塔上的下降 `dnG` 在**每一站** (层号是后继时, 第 0 站与一切第 $s+1$ 站都是) 经一般折叠求值; 无条件闭项 `GenFoldK.TG : A`, 证书 `Lg-TG`, FGH `fghG`.
> - **(a′) 读回进了闭项 (形状定理, 对一切 $s$, 非盲).** 第 $s+1$ 站的回灌输出就是在层 $2\boxplus\Omega_{\mathrm{top}}(\mathrm{Lev}\,X_s)$ 上的求值 (`Hs-ev`), 这个层的后继就是 $2\boxplus$ 读回 (`layer-rts`); 数据 $\Omega_L$ 的头是读回的新种类的闭包结点 (`ΩX-head`), 折叠在第 2 层**保留**它 (`out₂-kept`), 读回 `rd₂` 把它读成 `Ht` 的 κH 的 $\Omega$-结点, 于是**每一站的输出的头都是 κH 的 $\Omega$-结点** (`Hs-head`, 对一切 $s$ 与第 0 站), 所以每一站都不是 $2$ (`not-dnC`: 排除 `NegDnFoldBlind.dnC` 与 `NegGenFold.dnGenC` 这种每站输出 $2$ 的下降). 这条只说形状, 不说大小 (手册 §3.3).
> - **(b) 值: 没有定理.** 没有 `ord TG` 的界. **不是 ψ₀Λ 已写出.** 读法见下 (判断).
>
> **对纲领与目标.** 纲领 1: 闭项是 `A` (布劳威尔树) 的元素, FGH 在树上算; 求值的输出由读回的形状给出合法 (`Lg-rd₂`, 对一切数据). 纲领 2: 无公理; 折叠对数据结构递归 (节点经 `AccY`), 实例对种类结构的构造子递归, 检查器接受停机. 纲领 3: 折叠里唯一的比较是 `cmpB` (公共上界是最高层); A-回灌的升界只在**能对下标判定的分量**上点更新 (`upd` 对 `ℕ`, `updL` 对 `⊤ ⊎ _` 的左分量, 对构造子匹配), 不对坐标下标判定 (否定一路 `upd₁-sep`, `updT-sep` 否定的正是后者). 纲领 4: 导入闭包与切片干净 (审计). 目标 "让树自足": 闭包结点与 $\Omega_L$ 的 $\Omega$-行对一切种类一条; `GenK`, `LgDn`, `FbLg`, `FbBd` 对 `S₀`/`step`/`sup` 各一行 (同 `NegKcFoldDec.TopK` 的模式); 这一站新用到的字段: `TopG.topBd` (闭包分支的结点证据), `GenK.aK`/`frE-mono` (第 1 层读成 `HB T` 的底种类), `step` 的第二分量 (新种类升界不碰并的分量).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GenFold where

import OCF.Align.GenFoldIf
import OCF.Align.GenFoldTree
import OCF.Align.GenFoldRd
import OCF.Align.GenFoldRun
import OCF.Align.GenFoldInst
import OCF.Align.GenFoldEv
import OCF.Align.GenFoldK
import OCF.Align.GenFoldCmp
```

## 接口 (`GenFoldIf`, 只有类型)

```text
StH, NZ, NZ₁, AccY                         -- 对一切种类结构 S
DG₊ S Kd V Z  : n0 n1 _⨾_ nl ni nw, nc κ z (∀ W′ ≥ W → LgW W′ → DG₊ W′)    -- 一个闭包结点对一切种类
DataG.D S Z L W ; ZK T L (inj₁ _) = NZ L ; ZK T L (inj₂ _) = NZ₁ L ; DK T = DataG.D (step T) (ZK T)
TopG S (top, topBd) ; FBA S κ (tpA, rsA, rs≤, rsLg, tp-rs) ; GenK T (tpK, w₀, lw₀, aK, frE, frE-lg, frE-mono, fbA)
FoldTy T Λ : Tg, Df, St (d, z, z₁), Ig, RunTy ; EvGenTy T = GenK T → EvSysK T ; DnGenTy ; K₁ = Kc 1
只增 §6 LgDn T ; §7 FbLgAt, FbLg ; §8 FBABd (toE, tp-bd, rs-bd), FbBdAt, FbBd
```

律的定义域与 "为什么不撞 `no-wmatch`" 写在接口文件头: 数据树的种类就是层的种类结构 `step T` 的种类, 世界就是 `Wd (step T)`, 新种类坐标里的 $\Omega$-结点的种类就是 `inj₁ κ` (定义相等); 没有种类结构之间的世界映射, 没有两个种类被认成同一个.

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `S→⊲`, `Kup`, `Sk`, `zkS`, `zΩ`, `accL`, `drp`, `sum`, `toD₀`, **`Om.Ωd`**, `Pre`, **`Int`**, `topStepG` | Tree | 数据树工具; $\Omega_L$ 的 $\Omega$-行对一切种类一条; 输入改写 (闭包行不走前缀) | 定义; 定理 |
| `nbA`, **`rd₁`**, `rd₁-fst`, **`Lg-rd₁`**, `drp₁`, `toD₁`, `encH`, `Lg-encH`, **`rd₂`**, `rd₂-fst`, **`Lg-rd₂`** | Rd | 第 1 层读成 `HB T`, 第 2 层读成 `Ht` (新种类闭包读成 κH 结点), 合法由形状给出 | 定义; 定理 |
| **`Run`**, `Rpt`, `RunNi`, `Ai`, `BNi`, `Chn`, `RKi`, **`RunC`**, `RKc`, `RKk`, `κc₁`, `κΔ₁`, `RKa`, `κcA`, `κΔA` | Run | 一般折叠 (以 `T`, `GenK`, `LgDn`, `FbLg`, $\Lambda$ 为模块参数) | 定义 (停机由检查器) |
| `genS₀`, `genStep`, `genSupNo`, `genSupℕ`, **`genLev`**, `genNxt`, **`genKc`**; `ld*`, `fl*`, `bd*` | Inst | 接口记录对构造子递归的实例 | 构造; 定理 |
| **`no-swap₁`** | Inst | `Kc 1` 里旧站种类的 A-回灌搬到读回分量的底种类上, `rs-bd` 不成立 | 定理 (否定, 只否定这一次搬) |
| `EvAt.evAt`, **`lg-evAt`**, **`evSysG`**, **`evK₁`**, `evS₀`, `fb-old`, `fb-rd`, `fb-new`, `lay-S₀` | Ev | `EvSysK T` 的实例, 第 1 站实验 | 构造; 定理 (`refl`) |
| `LX`, `ΩX`, **`evB`**, `lg-evB`, **`dnG`**, **`TG`**, **`Lg-TG`**, **`fghG`**, `TG∞` | K | 塔上的下降与无条件闭项 | 构造; 无条件 |
| `Hs0-ev`, **`Hs-ev`**, **`layer-rts`**, `rts-head`, **`ΩX-head`**, **`out₂-kept`**, `evB-head`, **`Hs-head`**, **`not-dnC`** | K | 输出是在 $2\boxplus$ 读回 的层上的求值; 头是 κH 的 $\Omega$-结点; 每站不是 $2$ | 定理 (`refl`, 对一切 $s$, 对一切 $X$) |
| `σ`, `σ⁻`, **`τ`**, **`ρ`**, `τ-nμ`, `τ-nκ`, `ρ-nc₂`, `Ωd-κH`, `lay≡`, `wd≡` | Cmp | `HtTowerFTree.D` 与 `DK S₀` 逐结点互译 | 定义; 定理 (`refl`) |

## 闭项与 FGH 的类型原文

**无条件 (无模块参数):**

```text
GenFoldK.TG      : A          -- KG.TΛ∞ω, KG = KD dnG dnL₀
GenFoldK.Lg-TG   : Lg TG
GenFoldK.fghG    : ℕ → ℕ      -- FLv.FGH (ord TG)
GenFoldK.TG∞     : A          -- KG.TΛ∞
GenFoldK.dnG     : DnTower    -- dnG s (hs X) lb = 常数 evB X; 其余构造子取 dn₀ (截断版)
GenFoldK.evB     : ∀ {S : KS} (X : HB S) → Ht
GenFoldEv.evSysG : ∀ {T : KS} (G : GenK T) → LgDn T → FbLg G → EvSysK T
GenFoldEv.evK₁   : EvSysK K₁   -- K₁ = Kc 1
```

**条件版**: 折叠 `GenFoldRun` 以 `(T, G : GenK T, Ld : LgDn T, fl : FbLg G, Λ, lΛ : LgB Λ, one⊲)` 为模块参数; 一切参数的实例见下.

## 前提实例

- `GenK`, `LgDn`, `FbLg`, `FbBd`: 对一切 `Lev x` (`genLev x`, …) 与一切 `Kc s` (`genKc s`, …); 第 1 站 `G₁ = genKc 1`.
- 折叠的 $\Lambda$: 合法且第 1 层是第一位置的层; 实例 `LX X = 2 ⊞ Ωtop (Lev X)` (`lLX`, `oLX`), 对一切 $X$.
- 求值的世界 `W₀X X = (w₀ (genLev X) , hz)`, 合法 (`lW₀X`).
- `FBA` 实例里 `fbA κ = inj₁ _` 的种类: `S₀` 的种类, `step` 的旧种类沿用, `sup ℕ` 的分量, `Kc (s+1)` 的旧站分量; 都满足接口 §8 的 `rs-bd` (升界之后 $v$ 在**这个**种类的界之下).

## 读法 (全部是判断)

| 对象 | 读法 (判断) | 依据, 测到哪里 |
|---|---|---|
| `evB X` | $\Omega_{2\boxplus\Omega_{\mathrm{top}}(\mathrm{Lev}\,X)}$ 折叠到第 2 层, 读成 `Ht` | `Hs-ev`, `ΩX-head`, `out₂-kept`, `Hs-head` (形状定理); 无值定理 |
| `TG`, `TG∞` | **不读 ψ₀Λ.** 每站输出都在 `Ht` 里 (接口 `EvSys.evH` 的类型), 闭项是 `T⁺` 作用在 `Ht` 的高度上, 所以与 `Tkc`, `TD` 落在同一个上界之下 (`KcFold` 的读法 $\psi_0(\Omega_{\Omega_{\omega+1}})$ 量级, 粗界) | 下降的值域是 `Ht` (类型事实); 没有 `ord` 的比较 |
| 一般折叠的值与 `HtTowerFFold` 的差 | 不走前缀, 回灌每格只折叠一个坐标的分支: 两种种类时值不会更高 | `GenFoldCmp` 头 (判断, 无定理) |

## 第一个障碍

1. **并的世界的点更新 (定理在否定一路; 本路的写法).** 旧种类的 A-回灌要把这个种类的界升到给定的值, 别的分量不动. 并 `sup I F` 的世界是逐分量的族, 在分量 $i$ 处换掉要对下标判定 "是不是 $i$". 下标是 `ℕ` 或 `⊤ ⊎ _` 的左分量时有 (`upd`, `updL`); 下标是坐标时 (`Lev (hΩ κ g)` 的 `E κ`, `Kc (s+1)` 的读回分量 `inj₂ c`), 本路给 `fbA κ = inj₂ tt` (有损: 当前世界的分支重复 $\omega$ 次). 否定一路的 `upd₁-sep`, `updT-sep` (主审转告): 在 `Kc 1` 与 `Lev X₀` 上, 对一切世界一致的点更新同时 "升" 一份底拷贝, "留" 别的分量的底拷贝, 推出分离子; "一起升" (`upAll₁`) 可以. **本路没有写 "一起升" 的回灌** (下一步).
2. **下降的值域是 `Ht`.** `EvSys.evH : … → Ht`. 每站的输出都要读进只有两个种类的 `Ht` (`rd₂`): 旧种类的闭包在第 2 层有损地读 (当前世界的分支), 新种类的闭包读成 κH 结点, 坐标经 `encH : H₀ → HB T` (对一切 $y$ 合法, 但 $\Omega$-结点只取底坐标的分支). [判断] 这是闭项被 `Ht` 的量级封顶的原因; 要越过它, 下降的值域要随站变大 (不是本接口能改的).
3. **前缀走法.** `HtTowerFFold` 的 `Walk`/`Walk₁`/`Cut` 对坐标的路径递归; 一般种类的坐标类型是抽象的 `E κ`, 要对每个种类给路径的递归 (又一个对构造子递归的记录). 没有写.
4. **值.** 没有 `ord TG` 与任何参照树的比较.

报错原文: 无 (障碍是没写的东西与否定一路的定理).

## 四层行数表

`probes/Survey/scripts/genfold/locslice_genfold.py` (根表的前半段取 `dnfold/locslice_dnfold.py`, 同口径; 模块应用 `KG = KD dnG dnL₀`, 参数化模块 `GenFoldRun`, `GenFoldRd`, `EvAt`, `EvX`, `Tree`, `Om` 的定义手工列为根).

| 层 | 无条件 `TG`: 本路新增 / 树侧全部 / 记号 |
|---|---|
| 1 定义 | 96 / 634 / 0 |
| 2 折叠 (含一般折叠, 读回, 实例, 下降) | 704 / 2553 / 0 |
| 3 证书 | 743 / 2613 / 0 |
| 4 律, 形状, 实验, 互译 | 974 / 3072 / 0 |

对照 (同口径): 前 3 层树侧 2613, 超过标杆 1513 (照实报告); `TD` (DnFold) 2580, `Tkc` 1861. 本路新增的前 3 层 743 行里, 一般折叠 (`GenFoldRun`) 与读回 (`GenFoldRd`) 是主体; `HtTowerFTree`/`HtTowerFFold` 的两种种类折叠仍在闭包里 (塔的 `T⁺` 用它).

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 / 脚手架 |
|---|---|---|
| 一个闭包结点 `nc κ` 对一切种类, 分支对一切更大的世界 | `nκ`/`nμ` 推广; 坐标式的分支要对一切种类升界 (障碍 1) | 树逼出 |
| $\Omega$-行对一切种类一条 (`topBd`) | `TopG` (同 `NegKcFoldDec.TopK`) | 树侧 |
| `ZK` (旧种类 `NZ`, 新种类 `NZ₁`) | `step` 的两类种类 | 沿用 |
| 折叠的节点部分 (`RunNi` … `RKi`) | `HtTowerFFold` 照抄 | 沿用 |
| 闭包: 新种类回灌 (第 0, 1 层), A-回灌 (第 0 层, 可判定分量), 有损 (其余), 保留 | `RKμ`, `KG.RKy` 推广 | 树逼出; 有损那一支是脚手架的代价 |
| 不走前缀 (`Int`, 保留, 回灌) | 坐标路径的递归没写 | 选择 (改值, 判断) |
| `rd₁` 的底种类 `aK`, `frE` | 第 1 层读成 `HB T` | 树逼出 |
| `rd₂` 读进 `Ht`, `encH` | `EvSys.evH` 的类型 | 脚手架 (障碍 2) |
| `upd`, `updL` | 并的世界在可判定下标上点更新 | 树逼出 (否定一路划出边界) |
| `FBABd` (接口 §8) | 否定一路 `fba-swap`: `FBA` 不提 κ | 否定逼出 |
| 下降读层号不读输入 | `DnK` 的函数对一切输入, 输入当层用要合法 | 树逼出 (判断) |

归类 (判断): 攀爬与摆脱各半. 提供信息的标志: 数据树与折叠对一切种类结构一条 (闭包结点, $\Omega$-行); 实例对 `S₀`/`step`/`sup` 一行一个; 障碍 1 与否定一路的 `updT-sep` 配对, 划出 "点更新只在可判定下标上". 加深翻译的标志: 无新构造子读自基本列规则; 闭包定理没有专属前提; 不用 `Lab`. 第 4 层没有改前 3 层.

## 审计

- **编译.** 九个模块删自己的 `.agdai` (精确模块名) 后从入口编译, 依赖用共享接口, `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/GenFold.lagda.md +RTS -M6G -RTS`, 退出码 0, 峰值常驻约 1.06G, 用时约 7 秒.
- **导入闭包** (`importclosure.py`, 不加 `--only`): 九个模块都退出码 0, 禁用表命中 0.
- **切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词; `--html` 由导入 `OCF.Align.GenFold` 与 `OCF.Align.Om1HnAccept` 的 scratch 模块生成, 8G, 退出码 0): `TG` 302/0/0, `Lg-TG` 307/0/0, `fghG` 320/0/0, `dnG` 336/0/0, `evB` 247/0/0, `lg-evB` 249/0/0, `evSysG` 217/0/0, `evK₁` 270/0/0, `Run` 156/0/0, `rd₂` 101/0/0, `Lg-rd₂` 112/0/0, `genLev` 83/0/0, `Hs-head` 384/0/0, `not-dnC` 386/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用的实参: `TG` 的数与 `Tkc`, `TD` 相同 (302), 实参 `dnG` 单列为根 (0).
- **禁用构造**: 九个文件里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, 函数外延, UIP 前提.

## 文件与行数

| 文件 | 代码行 / 总行 | 内容 |
|---|---|---|
| `GenFoldIf` | 133 / 239 | 接口 |
| `GenFoldTree` | 175 / 248 | 数据树工具, $\Omega_L$, 输入改写 |
| `GenFoldRd` | 157 / 213 | 读回 `rd₁`, `rd₂`, `drp₁` |
| `GenFoldRun` | 199 / 275 | 一般折叠 |
| `GenFoldInst` | 215 / 310 | `GenK`/`LgDn`/`FbLg`/`FbBd` 的实例, `no-swap₁` |
| `GenFoldEv` | 63 / 114 | `EvSysK` 的实例, 第 1 站实验 |
| `GenFoldK` | 94 / 160 | 下降, 闭项, 形状定理 |
| `GenFoldCmp` | 77 / 118 | 与两种种类的数据树互译 |
| `GenFold` | 10 / 本文件 | 入口 |
| `probes/Survey/scripts/genfold/locslice_genfold.py` | — | 行数脚本 |

## 接手清单

1. **"一起升" 的回灌.** 否定一路说点更新在坐标下标上撞分离子, 一起升可以. 在 `sup` 上写一个 "一切分量一起升" 的 `FBA` 变体 (升界的值要能搬到每个分量: 每个分量要有自己的 A-读法, 底种类 `aK` 已经有), 替换 `genSupNo` 的有损一支.
2. **下降的值域.** `Ht` 封顶 (障碍 2). 让求值读回进随站变大的类型 (例如读进 `HB (Lev X)` 自身, 再经塔的 `injL`), 要一个新的塔接口 (不是 `KD`, 它的下降值域是 `Ht`).
3. **前缀走法.** 对每个种类的坐标给路径递归的记录 (`A` 的路径, `HB _` 的路径), 恢复 `Walk`/`Cut`.
4. **值.** 先在第 0 站 (`evB hz`, 层在 `Ht`) 上与 `HtTowerFClosed.TΛ` 比较.
