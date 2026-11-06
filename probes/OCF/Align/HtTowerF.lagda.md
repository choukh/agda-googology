# 两种种类的折叠: 层的分支取遍高度

> 攀爬 (前一步的摆脱侧结果是 [HtTower](HtTower.lagda.md): 它说明这一站要加的是 "以高度为坐标的种类", 世界要带它的界, 回灌要读回层与丢掉高分量). 入口. **判决: HOLDS (对 `step S₀` 这一站); 对一切级: 未走通, 缺的东西写成了类型 (`Need`).** 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延. 定义不读记号, 没有验收文件, 没有打开 `EBO`, `Lab`, 标签.
>
> 一句话: 层取 `HB S₁`, `S₁ = step S₀`: 两种 $\Omega$-分支, 旧种类坐标是 `A`, **新种类坐标是 `H₀` 的高度** (第二数类的布劳威尔树). 世界成对 $(A, H_0)$. 数据树多一个闭包 `nμ` (升高世界的高度分量). 折叠 ([HtTowerFFold](HtTowerFFold.lagda.md)) 照 `HtFeedFold` 写, 新种类的闭包: 目标在读回层 (第 1 层) 及以下就**回灌**, 界由第 1 层输出经 `rd` 读回, 输出丢掉升高的分量 (`drp₁`, 不用并); 目标更高就**沿高度坐标走到目标的界** (`Walk₁`, 走进旧种类的 $\Omega$-极限时用旧种类的闭包), 再保留. 闭项 `T-Ω₂`, `T-Ω₂+1`, `T-Ω₂·2`, `T-Ω₂ω`, `T-Ω₂²` 的高度都用到新种类, 合法性由形状给出 (`Lg-sum` 一次调用). 增长: **新种类的闭包站严格高于前缀站的任意可数子族** (`Supμ-Ω₂`), 同 `HtFeedGrow.Sup` 一档; 旧种类闭包的站也有 (`Sup-Ω₂`, `Sup-Ω₂+Ω`).
>
> **没有做到的:** 一切级一个折叠 (缺 `Need`, 见第一个障碍); 新种类上的回灌算子 (第 2 层输出读回 `HB S₁`, 对应 `HtOut.Fb`); 跨实例的比较; 值. 强度都是判断.

## 设计

| 件 | 定义 | 文件 |
|---|---|---|
| 层 | `Ht = HB S₁`, 种类 `κA` (坐标 `A`), `κH` (坐标 `H₀ = HB S₀`); 第一位置、合法、比较用 `HtTowerTy` 的 (`cmpB`) | [HtTowerFTree](HtTowerFTree.lagda.md) |
| 世界 | `Wd₂ = A × H₀`, `_≤_` = `step S₀` 的世界序 | 同上 |
| 节点 | `StH W k L` (三种, 同 `HtFeedTree`); `NZ` (非零层), **`NZ₁`** (第 2 层及以上) | 同上 |
| 数据树 | `D₊`: `HtFeedTree` 的七个 + **`nμ`** (分支对一切更大的世界); `nκ` 在 `NZ`, `nμ` 在 `NZ₁` | 同上 |
| $\Omega_L$ | `Ωd (hΩ κH g) = 1 ⨾ nμ (W′ ↦ 过层 g(W′ 的高度界) 的节点)` | 同上 |
| 走法 | `Cut₀` (沿 `A`), **`Cut₁`** (沿 `H₀`; `hLim` 处接旧种类的闭包); `Int` 多一行 `nμ` (`IW₁`) | 同上 |
| 读回 | `rd : D₁ → H₀` (同 `HtOutRead.rd`, 世界成对), `Lg-rd`, `rd-fst`; **`drp₁`**: 第 1 层的树换掉高度分量 | [HtTowerFRead](HtTowerFRead.lagda.md) |
| 折叠 | 旧种类闭包抽成 `KG` (分支的数据 `ud` 与折叠 `ur`); `RunM` (新种类闭包: 层 0, 1 回灌, $\ge2$ 保留); **`Walk₁`** (沿高度坐标, `hLim` 段交给 `KG`); 状态多 `z₁`; 模块参数 `one⊲` | [HtTowerFFold](HtTowerFFold.lagda.md) |
| 闭项 | `TΛ Λ lΛ o`; `T⁺ h = TΛ (1 ⊞ h)`; 五个闭项与 `fgh` | [HtTowerFClosed](HtTowerFClosed.lagda.md) |
| 增长 | `G`, `Sta` (同 `HtFeedGrow`), **`W₁`/`L4₁`** (新种类闭包第一格非零), **`Stμ.Supμ`**; 实例 | [HtTowerFGrow](HtTowerFGrow.lagda.md) |
| 缺的 | `KMatch`, `Need`, `need-1` | [HtTowerFNeed](HtTowerFNeed.lagda.md) |
| 测试 | `same d 2` 的形状比较 | [HtTowerFTest](HtTowerFTest.lagda.md) |

**为什么回灌不要并.** 新种类的回灌在目标层 $0$, $1$ 上输出. 第 0 层的树不看世界 (`drp`); 第 1 层的树不看高度分量 (`drp₁`, 对树归纳; 类型层的理由同 `HtTowerStrat.θ-indep`). 所以界升高以后输出可以落回目标的世界, 不需要目标世界与升高后的世界的字面公共上界 (`HtTowerNeg.no-joinᴮ` 说它一般不存在).

**为什么 `Walk₁` 在 `hLim` 处要旧种类的闭包.** 沿高度坐标从 $h(c_0)$ 走到 $\mathrm{h\Omega}\,h$, 中间的坐标是 $\Omega$ 那么多个 $h(c)$. 在第 0 层目标上这一段必须回灌 (第 0 层的树没有 `nκ`), 在别的目标上必须走到目标的 `A` 界再保留. 这正是旧种类闭包的折叠, 所以交给 `KG`, 分支是 "从 $h(c_0)$ 走到 $h(c)$" (对 $h(c)$ 结构递归, 停机检查直接过).

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `accL`, `accᴸ` | HtTowerFTree | 层良基, 对一切 `HB S₁` 的高度 | 定理 |
| `Cut₀`, `Cut₁`, `Int`, `IW₀`, `IW₁` | HtTowerFTree | 走法与输入的改写 | 定义 |
| `sum-fst`, `Lg-sum` | HtTowerFTree | 第 0 层的和保第一位置, 合法 | 定理, 无前提 |
| `rd-fst`, **`Lg-rd`**, `Lg-nbA` | HtTowerFRead | 第 1 层的树读回成合法的 `H₀` 高度, 前提只有底合法 | 定理 |
| `drp₁` | HtTowerFRead | 第 1 层的树换掉高度分量 | 定义 |
| `Run` 一族, `KG`, `RunM`, `Walk₁` | HtTowerFFold | 折叠, 对一切合法且以第 1 层为第一位置的 $\Lambda$ | 定义 (停机检查通过) |
| `TΛ`, `Lg-TΛ`, `T⁺`, `Lg-T⁺` | HtTowerFClosed | 闭项与合法 | 定义; 合法性是定理 |
| `T-Ω₂`, `T-Ω₂+1`, `T-Ω₂·2`, `T-Ω₂ω`, **`T-Ω₂²`**, `Lg-T-Ω₂²`, `fgh` | HtTowerFClosed | 高度用到新种类的闭项, 无参数 | 定义; 合法性是定理 |
| `Lg-Ω₂ω`, `Lg-Ω₂²` | HtTowerFClosed | 高度合法 (后者经 `cont→Lg`) | 定理 |
| `L2`, `L3`, `L4`, `pre<`, `pre≤s`, `s<κ`, **`Sup`** | HtTowerFGrow | 对一切 $\Lambda$ 与节点族 (旧种类闭包的站) | 定理 |
| **`L4₁`**, `s<μ`, **`Supμ`** | HtTowerFGrow | 对一切 $\Lambda$ 与节点族: 新种类闭包的站严格高于前缀站的任意可数子族 | 定理 |
| `μSup`, `μSupμ`, `ΩSup` | HtTowerFGrow | 最外是新种类 / 旧种类的 $\Omega$-极限 | 定理 |
| **`Supμ-Ω₂`**, `Sup-Ω₂`, `Sup-Ω₂+Ω` | HtTowerFGrow | 代入 $\Lambda=1\boxplus\Omega_2$, $\Omega_2+\Omega$ | 定理 |
| `need-1` | HtTowerFNeed | `Need` 在 $k=1$ 时成立 | 定理 (`refl`) |
| `a5`, `a6`, `b9`, `b10`, `c4`, `c5`, `d4`, `d5` | HtTowerFTest | 见下 | 有限测试 |

**`Supμ` 说什么, 不说什么.** 新种类闭包的站 `Xμ = 1 ⨾ (nl nd ⨾ nμ …)` 在第 0 层的输出, 回灌第一格非零: 第一格沿读回路径 $[\omega^H, \mathrm{rd}(\omega^H, z_1))$ 走 (`Walk₁`), $z_1$ 是第 1 层到此为止的输出 (由 `Stp` 非零), 对 $z_1$ 的形状归纳 (`L4₁`). 与 `HtFeedGrow.Sup` 同档: 一个折叠实例之内, 不说跨实例, 不说值.

## 闭项与读法

**读法都是判断** (纸面, 按 `HtFeed` 的读法: `TΛ Λ` 读 $\psi_0(\Omega_\Lambda)$, $1\boxplus\Omega_2=\Omega_2$ 作下标). `Cut₁` 在 `hLim` 处取前缀 (不是差), 值不忠实, 读法默认它不改上确界, 也是判断.

| 闭项 | 高度 | 读法 (判断) |
|---|---|---|
| `T-Ω₂` | `1 ⊞ Ωtop S₀` | $\psi_0(\Omega_{\Omega_2})$; 与 `HtOut.T-fbω` 同读法 (见 `HtTower` 的判断), 形状在深度 5 分开 (测试) |
| `T-Ω₂+1` | `1 ⊞ hs Ω₂ᴴ` | $\psi_0(\Omega_{\Omega_2+1})$ |
| `T-Ω₂·2` | `1 ⊞ Ω₂ ⊞ Ω₂` | $\psi_0(\Omega_{\Omega_2\cdot2})$ |
| `T-Ω₂ω` | `1 ⊞ hl (n ↦ Ω₂·n)` | $\psi_0(\Omega_{\Omega_2\cdot\omega})$ |
| `T-Ω₂²` | `1 ⊞ hΩ κH (x ↦ Ω₂·x)` | $\psi_0(\Omega_{\Omega_2^2})$ |

按读法, `T-Ω₂+1` 起高于此前一切闭项 (`HtOut` 最高读 $\psi_0(\Omega_{\Omega_2})$); 最高的 `T-Ω₂²` 读 $\psi_0(\Omega_{\Omega_2^2})$. 都没有定理: 没有参照树, 没有跨高度的比较.

**有限测试** ([HtTowerFTest](HtTowerFTest.lagda.md), `same d 2`): `T-Ω₂` 对 `T-Ω₂+1` 深度 5 同, 6 不同; `T-Ω₂` 对 `T-Ω₂·2` 深度 9 同, 10 不同; `T-Ω₂·2` 对 `T-Ω₂ω` 深度 4 同, 5 不同; `T-Ω₂` 对 `HtOut.T-fbω` 深度 4 同, 5 不同. 只说明折叠在这些层上不塌成同一棵树.

## 第一个障碍

1. **一切级一个折叠.** 这一站的折叠是对 `S₁` 写的: 两种种类, 读回层是数字层 $1$, 读回 `rd` 把第 1 层的节点与旧种类闭包读成 `H₀` 自己的种类 (坐标原样). 推广到 `HtTower` 的塔 `U`, 第 $k$ 个新种类的读回层是 `θ k`. 低于它的层只用分量 $j<k$ 的种类, 读回要把这些种类搬成 `L k` 的种类, 坐标可以来回换. 写成类型:
   ```text
   record KMatch (S S′ : KS) : Set where
     field km : K S → K S′ ; to : ∀ κ → E S κ → E S′ (km κ) ; fr : ∀ κ → E S′ (km κ) → E S κ
           fr-to : ∀ κ c → fr κ (to κ c) ≡ c
   Need = ∀ k j → j <ᴺ k → KMatch (step (L j)) (L k)
   ```
   `need-1` ($k=1$) 是 `refl`. **$k\ge2$ 没有构造, 未走通, 没有否定定理.** 判断: `L k` 由 `Lev` 造出, 要经 `Lev (ι i h)` 与 `Lev h` 的对应; 二者不是定义相等的 (相等要函数外延), 要逐级造种类结构的同构. 另外还缺世界的对应 (`Wd U → Wd (L k)` 保 `Bd`), 没有写成类型. 此外折叠本身 (`Walk₁` 对一般的种类递归, 各种类各一个 `Cut`) 要对 `KS` 的构造方式 (`step`, `sup`, `Lev`) 递归, 也没有写.
2. **新种类上的回灌.** 对应 `HtOut.Fb`: 以 `HB S₁` 为最高层折叠, 读第 2 层的输出成 `HB S₁` 的高度 (`rd₂`; 要 `toD₁ : H₀ → D₁` 喂进第 1 层节点的分支). 没有写.
3. **值, 跨实例.** 同 `HtFeed`, `HtOut`.

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 世界成对 $(A,H_0)$ | 新种类的坐标比较要字面公共上界 | **树逼的** (壁垒; `no-joinᴮ`) |
| `nμ` 的分支对一切更大的世界 (不只升高度分量) | `Cut₁` 在 `hLim` 处要在升高 `A` 分量的世界里取分支 | 树逼的 (判断, 没有否定定理) |
| `NZ₁`: `nμ` 只在第 2 层及以上 | `rd` 把第 1 层读成 `H₀`, `H₀` 没有新种类 | **树逼的** (`rd` 的 `nμ` 一行必须是空的) |
| `Ωd (hΩ κH g)` | 同 `nκ` 那一行 | 形状受旧树影响 (沿用) |
| `Cut₁`, `Walk₁` 在 `hLim` 处用旧种类的闭包 | 中间坐标有 $\Omega$ 那么多; 第 0 层目标要回灌 | **树逼的** (判断: 第 0 层的树没有闭包) |
| `hLim` 段的分支取前缀, 不取差 | 旧种类的分支只单调, 不连续 | 选择 (值不忠实) |
| `hLim` 段的 `KG` 基世界取当前世界, 不取 $c_0$ | 高度的第一位置不能搬到更小的 `A` 世界 | 树逼的 (判断) |
| 新种类闭包: 层 $\le1$ 回灌, $\ge2$ 保留 | 读回层是第 1 层 (种类就是层); 同 `HtFeedFold` 对旧种类的 "层 0 回灌" | 树侧, 形状沿用 `HtFeedFold` |
| `drp₁` | 输出落回目标世界, 没有并 | **树逼的** (`no-joinᴮ`) |
| 状态多 `z₁` | 回灌的第一个界 | 沿用 `z` 的做法 |
| 模块参数 `one⊲` | 回灌要第 1 层目标是 $\Lambda$ 的第一位置 | 树逼的 (同 `HtOut.top⁺`) |
| `KG` (旧种类闭包对分支用法抽象) | `HtFeedFold` 逐个改写, 不改语义 | 重构 |
| 折叠本体, `S = ω⋅` | `HtFeedFold` | 形状受旧树影响 (沿用) |
| `rd`, `nbA`, `toD` | `HtOutRead` | 沿用 |

**按 `AGENTS.md` 归类: 攀爬, 提供信息.**
- 加深的三个标志: 新构造子或节点字段读自基本列规则: **没有** (`nμ` 是 `nκ` 的同形物, 由新种类机械给出; 回灌/保留的分界由读回层给出, 不读任何基本列规则). 闭包定理新增专属前提: **没有** (`Sup`, `Supμ` 对一切 $\Lambda$ 与节点族; `one⊲` 是折叠的模块参数, 不是闭包定理的前提, 同 `HtOut` 的 `top⁺`). 只能用 `Lab` 验收: **不是**.
- 提供信息的三个标志: 对结构参数的一步定理: **有** (`Supμ` 对 $\Lambda$ 与节点族, 新用到的字段是 `nμ` 的回灌, 经 `rd` 与 `Walk₁`; `L4₁` 对第 1 层的树归纳). 序数值验收: **没有**. 否定定理划出字段: **有**, 在前一篇 (`no-joinᴮ` 逼出 `drp₁` 与世界的界).
- 翻译与摆脱: 新加的结构 (第二个世界分量、`nμ`、`Walk₁`) 都由新种类的坐标是高度机械逼出, 不按 $\Omega_2$ 的算术写. 每加一个种类要加一份 `Cut`/`Walk`/闭包折叠, 这一站是手写的 (约 260 行, 见账); 要一切级一个定义, 先要 `Need`.

## 账

**定义级切片** (口径同 `htfeed/locslice_htfeed.py`: 计 agda 非空非注释行, 记号模块除外; 脚本在临时目录 `httower/locslice_httowerf.py`, 读 `agda --html` 的输出).

| 路线 | 层 1 (类型) | 层 2 (+折叠, 闭项, FGH) | 层 3 (+合法性) | 加增长 |
|---|---|---|---|---|
| HtFeed, 一种种类, 高度给定; 闭项到 $\Omega^{\Omega^\omega}$ (读法) | 51 | 661 (去共用 578) | 665 (去共用 582) | 892 (净增 227) |
| HtOut, 一种种类, 高度由回灌生成; 闭项读 $\psi_0(\Omega_{\Omega_2})$ | 51 | 643 (去共用 560) | 649 (去共用 566) | 892 (净增 243) |
| **HtTowerF, 两种种类; 闭项到 $\psi_0(\Omega_{\Omega_2^2})$ (读法)** | 225 (去共用 202) | 988 (去共用 905) | 996 (去共用 913) | 1347 (净增 351) |

- 层 1 按模块: HtTowerTy 121, HtTowerFTree 45, CumReadCF 36, BTBO 23. 层 1 大是因为层的类型 `HB (step S₀)` 要 `step`, 而 `step` 的新种类的界下比较就是 `cmpB`, 坐标合法就是 `LgB` (`HtTower` 的账同).
- 层 2 按模块: HtTowerFFold 291, HtTowerFTree 264, HtTowerTy 147, HtTowerFRead 75, Free.Level 56, HtTowerFClosed 54, HtTowerCont 38, CumReadCF 36, BTBO 27.
- 层 3 多 8 行 (`Lg-TΛ`, `Lg-T⁺`, `Lg-T-Ω₂²` 是 `Lg-sum` 的调用).
- 增长净增 351 行 (HtTowerFGrow 327, TLRuleSpec 24); 其中新种类闭包的站 (`W₁`, `L4₁`, `Stμ`) 约 80 行, 其余是 `HtFeedGrow` 的改写.
- 新种类专用的代码 (按定义块粗分, 文件级代码行): 折叠里 `Walk₁`, `WRp₁`, `RunM`, `RKμ`, `RKμk`, `Kp₁`, `Kb₁`, `κc₁`, `κΔ₁`, `Cl₁` 约 105 行; 树里 `Cut₁`, `IW₁`, `NZ₁` 一族, `Int` 的 `nμ` 一行约 60 行; 读回 (`rd`, `drp₁`, `nbA`) 84 行. 约 250 行; 其余是 `HtFeedTree`, `HtFeedFold` 改成成对世界与 `KG` 的抽象.
- `Need` 的独立切片 240 行 (多数是 `HtTowerTy`).
- 文件级 (代码块里非空非注释行): `HtTowerFTree` 276, `HtTowerFRead` 84, `HtTowerFFold` 313, `HtTowerFClosed` 74, `HtTowerFGrow` 365, `HtTowerFNeed` 35, `HtTowerFTest` 33, 入口 7; 共 1187.

## 审计

- **导入闭包** (`importclosure.py`, `--only` 表同 `HtTower`): `HtTowerF` (26 个模块, 本地 16), `HtTowerFTree` (11, 本地 4), `HtTowerFRead` (12, 本地 5), `HtTowerFFold` (13, 本地 6), `HtTowerFClosed` (18, 本地 9), `HtTowerFGrow` (22, 本地 12), `HtTowerFNeed` (14, 本地 7), `HtTowerFTest` (25, 本地 16; 经 `HtOutFeed` 进来 `HtFeed*`, `HtOut*`) 都是退出码 0, 禁用表 0, `--only` 之外 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `HtTowerFClosed:fgh` 233/0/0, `HtTowerFClosed:Lg-T-Ω₂²` 219/0/0, `HtTowerFClosed:TΛ` 187/0/0, `HtTowerFFold:Run` 168/0/0, `HtTowerFFold:Walk₁` 168/0/0, `HtTowerFRead:Lg-rd` 90/0/0, `HtTowerFRead:drp₁` 72/0/0, `HtTowerFGrow:Supμ-Ω₂` 287/0/0, `HtTowerFGrow:Sup-Ω₂+Ω` 291/0/0, `HtTowerFNeed:need-1` 67/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用.
- **禁用构造**: 八个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 不用 `--cubical`, 不用函数外延; 都带 `--safe --without-K --lossy-unification`.
- **从头编译** (`--ignore-interfaces`, 堆上限 6G): 入口退出码 0 (31 秒, 1.3G); `HtTowerFTest` 退出码 0 (28 秒, 1.1G).

## 时间线

写定义前读过: `HtTower*` (本路前一篇), `HtFeedTree`, `HtFeedFold`, `HtFeedClosed`, `HtFeedGrow`, `HtOutRead`, `HtOutFeed`. 没有打开 `EBO`, `Correspond`, `Label`, 也没有读任何基本列规则. 读法是手算的纸面判断.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerF where

open import OCF.Align.HtTowerFTree using (S₁; H₀; Ht; Wd₂; κA; κH; _≤_; StH; NZ; NZ₁; D₊; D; accL; Ωd; Cut₀; Cut₁; Int; sum; Lg-sum) public
open import OCF.Align.HtTowerFRead using (D₁; rd; rd-fst; Lg-rd; drp₁) public
open import OCF.Align.HtTowerFClosed using (TΛ; Lg-TΛ; T⁺; Lg-T⁺; Ω₂ᴴ; T-Ω₂; T-Ω₂+1; T-Ω₂·2; T-Ω₂ω; T-Ω₂²; Lg-T-Ω₂²; fgh) public
open import OCF.Align.HtTowerFGrow using (module G; module μSt; module ΩSt; Sup-Ω₂; Supμ-Ω₂; Sup-Ω₂+Ω) public
open import OCF.Align.HtTowerFNeed using (KMatch; Need; need-1) public
```
