# 相干的世界: 下标塔的对角要的世界

> 摆脱侧 (结构), 没有攀爬. 入口. 接 [HtTowerN](HtTowerN.lagda.md) 的第一个障碍 (对角要相干的并). **判决: PARTIAL.** 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延. 定义不读记号, 没有验收文件, 没有打开 `EBO`, `Lab`, 标签.
>
> 1. **做到: 链上相干的极限 `U⋆` (定理).** 世界**由扩张生成**: 底世界加每一级的扩张数据, 第 $k$ 级的世界 `pj k w` 是一级一级粘出来的 ([CohWTy](CohWTy.lagda.md) 的 `colim`, 对一切链). 用在 `HtTowerNStage.L′` 上得 `U⋆` ([CohWL](CohWL.lagda.md)): **`coh`**: 第 $k+1$ 级的世界投影到第 $k$ 级就是第 $k$ 级的世界, `refl`. 每一级 `L′ k` 与每个 `step (L′ j)` 进 `U⋆` 都有 `KMatch`/`WMatch` (`kmU`, `wmU`, `needU`, `wmatchU`); 跨级相干 `rcoh→`/`rcoh←` 是对一切带包含的链、一切 $j\le k$ 的一条定理; **`yes-wmatch`**: `no-wmatch` 的两个前提在 `U⋆` 上同时成立. `cmpB`, 合法, 第一位置一行不新写.
> 2. **做到: `U⋆` 里的塔与对角 (定理).** `θ⋆ (k+1) = hΩ (ν⋆ k) (c ↦ θ⋆ k ⊞ ι⋆ k c)`, `Λ⋆ = hl θ⋆`, **`Lg-Λ⋆`** 由一步定理 `Lg-θ⋆s` 给出 ([CohWTower](CohWTower.lagda.md)); 层良基 `accB` 对一切种类结构.
> 3. **新的否定: `Lev` 里的拷贝不相干 (定理).** `L′ (k+1)` 的 `Lev` 部分对每个高度新造一个种类结构, 里面是低级种类的拷贝, 世界在独立的位置. **`no-cross→`/`no-cross←`** (`step S₀` 的新种类的链上一份与 `Lev` 拷贝一份), **`no-crossA→`/`no-crossA←`** (底种类的两份), 推论 **`no-route`** (经任何种类结构都读不通); 拷贝确实出现在 `Λ⋆` 之下 (`κL-layer`, 合法世界里) ([CohWNeg](CohWNeg.lagda.md)). 所以 `U⋆` 只让链相干, 不够折叠用 (判断).
> 4. **做到: 一个世界对一切层号的 `SL⋆` (定理), 对角就是 `Λ`.** 把世界从种类结构里拿出来: 先造种类与坐标 (`KE`, `H⁰`, `LFReTy` 的层号块 `LH`, `Lv`), 再定世界 $\mathrm{GW}=\prod_{y}H^0(\mathrm{Lv}\,y)$, 最后对层号递归定界、合法、比较 ([CohWGl](CohWGl.lagda.md)). 一切层号的并 `SL⋆` 的世界是 `GW` 本身. **`glob`**: 任一种类的界只由它的读回层与世界在那一层的分量决定 (对一切层号、一切种类); **`cross`**: 读回层相等的两个种类在每个世界里界相同, `no-cross` 那一对在这里是 `refl` (`cross-ex`). 每个层号进并的世界对应是恒等 (`wmS`). `LFReTower` 的 $\hat\Omega$, 塔, **`Λ`**, 第 $n$ 个不动点照抄, 合法 (`Lg-Λ`, `Lg-Λn`), 由形状给出.
> 5. **没做到: 折叠, 闭项, 增长.** 没有写 `U⋆` 或 `SL⋆` 上的折叠, 没有对角处的闭项 (序数树), 没有 `HtFeedGrow.Sup` 一档的增长. **未走通 (没有开始写), 不是否定.** 第一个障碍见下: `SL⋆` 上 "把一层的界换掉, 其余不动" 要判定层号相等 (`upd→wdec`, 条件定理, [CohWUpd](CohWUpd.lagda.md)).

## 设计

| 件 | 定义 | 文件 |
|---|---|---|
| 链 | `Chain`: 各级 `F k`, 扩张数据 `X k`, 粘合 `gl k : Wd (F k) → X k → Wd (F (k+1))` | [CohWTy](CohWTy.lagda.md) |
| 链的极限 | `colim C`: 种类 $\Sigma_k K(F\,k)$, 世界 $\mathrm{Wd}(F\,0)\times\prod_k X\,k$, 第 $k$ 级的世界 `pj k` (递归粘出), 界/第一位置/合法/比较都经 `pj` 交给各级 | 同上 |
| 带包含的链 | `Incl`: `M k : KMatch (F k) (F (k+1))`, 界经 `gl` 双向保持; `Le`, `Mle` | 同上 |
| `U⋆` | `XL k = HB (L′ k) × Wd (Lev (Ωtop (L′ k)))`, `glL k w x = (true ↦ (w, β); false ↦ v)`, `U⋆ = colim chainL`; 包含 `inclL` (界是恒等) | [CohWL](CohWL.lagda.md) |
| 塔与对角 | `ν⋆ k = (k+1, (true, new))`, `θ⋆`, `Λ⋆ = hl θ⋆`; `old⋆`, `up₁`; `StB`, `AccB`, `accB` | [CohWTower](CohWTower.lagda.md) |
| 拷贝 | `κ0⋆ = (1, (true, new))`, `κL = (2, (false, (1, new)))`; `κA0 = (0, tt)`, `κAL = (2, (false, (1, old)))`; 世界 `wA`, `wB`, `wC`, `wD`, `wE` | [CohWNeg](CohWNeg.lagda.md) |
| 只有种类与坐标 | `KE` (种类, 坐标), `H⁰ S`, `stepᵉ`, `supᵉ`; 层号块 `LH`, `Lv : LH → KE` (`LFReTy` 的四行, 底是空结构) | [CohWGl](CohWGl.lagda.md) |
| 一个世界 | `GW = (y : LH) → H⁰ (Lv y)`, $w\,y$ 是层号 $y$ 的新种类的界 | 同上 |
| 每层的种类结构 | `Lv⋆ y`: 种类、坐标是 `Lv y` 的, 世界 `GW`; 字段 `Bd⋆`, `Pr⋆`, `LgW⋆`, `Le⋆`, `rf⋆`, `tr⋆`, `Bd↑⋆`, `cmp⋆`, `LgE⋆`, `lgBd⋆`, `bot⋆`, `botBd⋆` 对层号递归; `cv : H⁰ (Lv x) → HB (Lv⋆ x)` | 同上 |
| 并 | `SL⋆`: 种类 $(y, \kappa)$, $\kappa$ 是 `Lv (ls y)` 的; 世界 `GW`; `kmS`, `wmS` (恒等), `ιS` | 同上 |
| 相干 | `lvl`, `E-lvl`, **`glob`**, `globPr`, `mvL`, `same-lvl`, **`cross`**, `κa`, `κb`, `cross-ex` | 同上 |
| 塔 | `node`, `ofHB`, `ν`, `Ω̂`, `tw`, **`Λ`**, `it`, `fix`, `Λn` | 同上 |
| 改一层 | `Upd` (`upd`, 律 `at`, `off`), **`upd→wdec`** | [CohWUpd](CohWUpd.lagda.md) |

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `coh-pj` | CohWTy | 第 $k+1$ 级的世界就是第 $k$ 级的世界粘上第 $k$ 份扩张 | 定理 (`refl`, 对一切链) |
| `kmC`, `wmC` | CohWTy | 每一级进链的极限: 种类、世界的对应, 界双向定义相等 | 定理 (对一切链, 一切 $k$) |
| `ιc-⊲`, `Lg-ιc` | CohWTy | 第 $k$ 级的高度进极限保第一位置 (投影世界), 保合法 | 定理 |
| **`rcoh→`**, **`rcoh←`**, `wmLe` | CohWTy | 带包含的链: 一切 $j\le k$, 第 $j$ 级种类与它在第 $k$ 级的像在同一个世界里界相同; 同一个投影 `pj j` 服务一切拷贝 | 定理 (对一切带包含的链, 对 $j\le k$ 的证明递归) |
| **`coh`** | CohWL | `proj₁ (pjL (k+1) w true) ≡ pjL k w` | 定理 (`refl`) |
| `kmU`, `wmU`, `needU`, `wmatchU` | CohWL | 每个 `L′ k` 与每个 `step (L′ j)` 进 `U⋆` | 定理 (一条定义对一切 $k$, $j$) |
| **`tri`** | CohWL | 对一切 $j<k$: 先投影到 `L′ k` 再用 `wmatch′`, 等于直接投影到 `step (L′ j)` | 定理 (对 $q$ 递归) |
| `rcohL→`, `rcohL←` | CohWL | `rcoh` 的实例 | 定理 |
| **`yes-wmatch`**, `same-bd` | CohWL | `no-wmatch` 的两个前提在 `U⋆` 上同时成立, 世界对应 `pjL 2` | 定理 |
| `θ⋆-st`, `Lg-θ⋆s`, `Lg-θ⋆`, **`Lg-Λ⋆`**, `θ⋆⊲Λ⋆` | CohWTower | 塔一个接一个是第一位置, 合法是对 $k$ 的一步定理, 对角合法 | 定理 |
| `Lg-old⋆`, `Lg-up₁` | CohWTower | 旧高度 (`HtFeed`, `HtTowerF` 的层) 进 `U⋆` 保合法 | 定理 |
| `accB`, `accΛ⋆` | CohWTower | 层的节点种类可达, 对一切种类结构 | 定理 |
| `same-S`, `same-E` | CohWNeg | `κ0⋆`, `κL` 是同一个种类结构 `step S₀` 的新种类, 坐标类型相同 | 定理 (`refl`) |
| **`no-cross→`**, **`no-cross←`** | CohWNeg | 合法的 `U⋆` 世界里, `κ0⋆` 的界推不出 `κL` 的, 反之亦然 | 否定, 定理 |
| **`no-crossA→`**, **`no-crossA←`** | CohWNeg | 底种类的链上一份 `κA0` 与 `Lev` 拷贝 `κAL` 同样 | 否定, 定理 |
| `satA`, `satB` | CohWNeg | 反例里的界各自成立 (前提可满足) | 定理 |
| **`no-route`**, `no-route←` | CohWNeg | 对任何 $S'$, $\kappa'$, 坐标映射与世界映射, 不能一头保 `κ0⋆`、另一头保 `κL` 的界 | 否定, 定理 |
| `Lg-c₂`, `lgE`, **`κL-layer`**, `Lg-κL-layer` | CohWNeg | 合法世界 `wE` 里, 最外是 `κL` 的合法层是 `Λ⋆` 的第一位置 | 定理 |
| `Lv⋆`, `SL⋆`, `cmpL⋆` | CohWGl | 每个层号与一切层号的并都是 `KS`, 世界都是 `GW`; 比较是 `cmpB` | 定义 (停机检查通过); 比较是定理 |
| `kmS`, `wmS`, `ιS-⊲`, `Lg-ιS` | CohWGl | 每个层号进并, 世界对应是恒等 | 定理 |
| **`glob`**, `globPr` | CohWGl | 任一种类的界 (第一位置) 只看读回层与 $w$ 在那一层的分量 | 定理 (对一切层号、种类) |
| **`cross`**, `cross-ex` | CohWGl | 读回层相等、坐标对上的两个种类, 在每个世界里界相同; `no-cross` 那一对的形状是 `refl` | 定理 |
| `Ω̂-suc`, `Ω̂-⊲`, `Lg-Ω̂`, `tw-st`, `Lg-tw`, **`Lg-Λ`**, `fix-form`, `Lg-fix`, **`Lg-Λn`** | CohWGl | $x\mapsto\Omega_x$ 合法是一步定理; $\Lambda$ 与第 $n$ 个不动点合法; $\hat\Omega(\Lambda)$ 的形状 | 定理 |
| **`upd→wdec`** | CohWUpd | `GW` 上 "恰好换一层" 的更新推出层号相等的弱可判定 | 条件定理 (不是否定) |

**否定的范围.** `no-cross`, `no-crossA`, `no-route` 只说 `U⋆` 里这两对种类 (链上一份与 `Lev` 部分坐标 $1$ 的分量里的一份); 不说读回必须把一份读成另一份 (判断, 见第一个障碍), 不否定 `rcohL` (链相干是定理), 不否定 "`Lev` 部分也相干" 的设计 (`SL⋆` 就是一个). `upd→wdec` 不否定 `Upd` (经典地它存在), 只说造它至少要对层号做判定; 判断: `LH` 有函数分支, 这样的判定在 `--safe --without-K` 里写不出.

## 闭项与读法

没有闭项 (没有折叠). 高度的读法都是**判断**, 沿用前文:

| 高度 | 读法 (判断) | 依据 |
|---|---|---|
| `θ⋆ (k+1)` | $\Lambda_k$ 之上的第一个 $\Omega$, $\Lambda_0=\Omega_2$, $\Lambda_{k+1}\approx\Omega_{\Lambda_k+1}$ | 同 `HtTowerU.θ` (`L′` 与 `L` 同读法, `HtTowerN` 的判断) |
| `Λ⋆` | $\Lambda=\sup_k\Lambda_k$, $x\mapsto\Omega_x$ 的第一个不动点 | 同 `HtTowerU.Λᵁ` |
| `SL⋆` 的 `Λ` | 同上, $\Lambda=\sup_n \hat\Omega^n(0)$ | 同 `LFReTower.Λ` |
| `Λn n` | 第 $n+1$ 个不动点 | 同 `LFReTower.Λn` |

目标闭项若有, 读法 $\psi_0(\Omega_\Lambda)$ ($=\psi_0(\Lambda)$, $\Lambda$ 是 $x\mapsto\Omega_x$ 的第一个不动点); 本轮**没有**这个闭项, 也没有任何强度的定理.

## 第一个障碍

1. **`U⋆` 不够: `Lev` 的拷贝 (定理 + 判断).** 链相干之后, 每一级的 `Lev` 部分仍是 `sup` 的独立分量. 读回 `Lev` 部分的种类 (坐标是 `HB (Lev x)`) 时, 第 1 层输出里的底种类节点要在拷贝自己的 `A` 世界里有界, 而它们是在链上的 `A` 世界里造出来的 (`no-crossA`); 更高的拷贝同样 (`no-cross`, `no-route`). 拷贝真的在 `Λ⋆` 之下 (`κL-layer`). 判断: 折叠要么在 `Lev` 的种类上不回灌 (强度不够), 要么要 `SL⋆` 那样按层号存界的世界.
2. **`SL⋆` 上的折叠: 改一层的界 (条件定理 + 判断).** `HtTowerFFold` 的走法与闭包在 "当前世界换掉一个分量" 的世界上取分支 (`Cut₁` 的 $(w_A,b)$, `KG` 的 $(c,\beta)$, `RunM` 的 $(w_A,v_1)$). `SL⋆` 的世界是层号上的函数, 恰好换一层要判定层号相等 (`upd→wdec`). 所以 **相干 (按层号存界) 与可改 (按位置存界) 在现有的世界形状下不能兼得**: 按位置存 (`sup`, `U⋆` 的 `Lev` 部分) 有 `no-wmatch`, `no-cross`; 按层号存 (`SL⋆`) 改一层要判定. 两边各有一条编译过的结果; "不能兼得" 本身是判断, 不是定理. 可试的出路 (判断, 没有试): (a) 折叠的分支只取 "一切更大的世界", 走法不造世界, 只在给定的世界里取界之下的坐标; (b) 世界沿当前层的层号路径存成元组 (路径上的位置可判定), 跨路径的同一层号用 `glob` 对齐; (c) 统一升高一切层的界 (不挑出一层; 要一切层的界同类型).
3. **一切级一个折叠 (判断).** 即使世界可改, 每个种类要一份走法与闭包 (`HtTowerF` 对两种种类手写了约 250 行). `SL⋆` 的种类都是某个层号的新种类 (底是空结构, `A` 是 `H⁰ (Lv lz)`), 坐标都是 `H⁰ (Lv ℓ)` (`E-lvl`), 所以走法可以写成对层号与坐标的一条递归; 停机度量 (层号) 没有试. 这一条在第 2 条之后.

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 链的极限, 世界由扩张生成 | 读回要同一个种类的各份拷贝界相同, 积世界做不到 | **树逼的** (`HtTowerNStage.no-wmatch`; 相干的形状是 `HtTowerN` 第一个障碍的原话) |
| `XL`, `glL` | `L′ (k+1)` 的世界形状 (`⊕ₖ` 的 `Bool` 族) | 机械给出 |
| `θ⋆` 不经 `up` | 坐标的种类就是第 $k$ 级的种类, 世界是投影 | 树侧; 塔的形状沿用 `HtTowerU.θ` (作者对下标塔的直觉启发) |
| 把世界从种类结构里拿出来 (`KE`, `H⁰`, `GW`) | `Lev` 拷贝不相干; 世界放进每个结构就有几份界 | **树逼的** (`no-cross`, `no-crossA`); 拆成两步是为了 `GW` 不依赖界 (选择, 没有否定定理说必须这样拆) |
| `cv : H⁰ → HB` | 坐标的形状在世界之前定, 比较要用 `HtTowerTy` 的 `cmpB` | 脚手架, 由拆分带来 (约 5 行) |
| `LgW⋆`, `Le⋆` 对层号递归 | 合法与世界序只看不高于本层的分量, 否则 `LgB` 与 `LgW` 循环 | 树逼的 (停机检查) |
| 层号块 `LH`, `Lv`; `node`, `ofHB`, `Ω̂`, `tw`, `Λ`, `fix` | `LFReTy`, `LFReTower` | 沿用 (`Lev` 的形状受作者对下标塔的直觉启发; 定义无记号) |
| 底换成空结构 | `stepᵉ` 的新种类在空结构上就是不带 $\Omega$ 的树 (`A` 的形状) | 树侧, 同 `LFReTy.S⊥` |
| `Upd` 的两条律 | `HtTowerFFold` 造世界的三处 | 树侧 (读自现有折叠, 不是记号) |

**按 `AGENTS.md` 归类: 摆脱侧, 提供信息.** 加深的三个标志: 新构造子或字段读自基本列规则: **没有** (没有新的高度构造子, 没有节点); 闭包定理新增专属前提: **没有闭包定理**; 只能用 `Lab` 验收: **不是** (没有验收). 提供信息的标志: 一步定理 `rcoh` (对一切带包含的链)、`Lg-θ⋆s`、`glob` (对一切层号)、`Lg-Ω̂`; 否定定理划出世界不能有的形状 (`no-cross`, `no-crossA`, `no-route`) 与条件定理 `upd→wdec`. 序数值验收: 没有. 这一轮是摆脱侧的结果, 按 1:1 交替, 它说明下一站 (折叠) 要先定世界怎样改一层.

## 账

**定义级切片** (口径同 `htfeed/locslice_htfeed.py`; 脚本复制自 `htfeed/locslice_lfre.py`, 在临时目录 `cohw/locslice_cohw.py`). 没有折叠, 所以四层表的层 2 (折叠, 闭项, FGH) 为空; 下表的 "层 1" 是种类结构与高度的定义, "层 3" 加高度的合法与比较.

| 路线 | 层 1 (定义) | 层 3 (+合法) | 按模块 |
|---|---|---|---|
| `U⋆`: 链的极限, 塔, `Λ⋆` | 282 (去共用 259) | 318 (去共用 295), 净增 36 | HtTowerTy 160, CumReadCF 36, CohWTy 36, BTBO 23, CohWTower 9, HtTowerNStage 8, CohWL 8 |
| **`SL⋆`: 块, `GW`, 并, $\hat\Omega$, `Λ`, `Λn`** | 279 (去共用 256) | 336 (去共用 313), 净增 57 | CohWGl 181, HtTowerTy 75, BTBO 23; 净增 CohWGl 42, HtTowerTy 15 |
| 对照 `LFRe` (积世界) | 254 (去共用 231) | 321 (去共用 298) | `LFRe` 入口的账 |

- 独立切片: `U⋆` 的对应与相干 (`kmU` … `yes-wmatch`, `coh`) 357 (CohWTy 57, CohWL 41, HtTowerNStage 37, 其余 HtTowerTy 等); 层的良基 `accΛ⋆` 301; 否定与 `κL` 层 429 (CohWNeg 101); `SL⋆` 的对应与相干 (`kmS`, `wmS`, `glob`, `globPr`, `cross`, `cross-ex`) 302 (CohWGl 197); `upd→wdec` 52.
- 相干的世界 (`SL⋆`) 比积世界 (`LFRe` 的 `SL`) 层 1 多 25 行, 层 3 多 15 行: `Lv⋆` 的十二个字段各要对层号写一遍 (`LFRe` 的 `step`, `sup` 是现成的), 加 `cv`.
- 文件级 (代码块里非空非注释行): `CohWTy` 89, `CohWL` 57, `CohWTower` 64, `CohWNeg` 127, `CohWGl` 292, `CohWUpd` 31, 入口 8; 共 668.

## 审计

- **导入闭包** (`importclosure.py`, `--only` 表: `OCF.Free.Level`, `OCF.BTBO`, `OCF.Align.CumReadCF`, `TLRuleSpec`, `TLRuleSum`, `SumOne`, `HtGen`, `HtFeed`, `HtOut`, `HtCross`, `SumVar`, `HtTower`, `LFRe`, `CohW`): `CohW` (24 个模块, 本地 15), `CohWTy` (18, 本地 9), `CohWL` (19, 本地 10), `CohWTower` (20, 本地 11), `CohWNeg` (21, 本地 12), `CohWGl` (18, 本地 9), `CohWUpd` (19, 本地 10), 都是退出码 0, 禁用表 0, `--only` 之外 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `CohWL:U⋆` 79/0/0, `yes-wmatch` 83/0/0, `tri` 96/0/0, `CohWTy:rcoh→` 20/0/0, `CohWTower:Lg-Λ⋆` 96/0/0, `accΛ⋆` 93/0/0, `CohWNeg:no-route` 90/0/0, `no-crossA→` 86/0/0, `Lg-κL-layer` 107/0/0, `CohWGl:SL⋆` 51/0/0, `glob` 52/0/0, `cross` 58/0/0, `Lg-Λ` 70/0/0, `Lg-Λn` 76/0/0, `CohWUpd:upd→wdec` 16/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用.
- **禁用构造**: 七个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 不用 `--cubical`, 不用函数外延; 都带 `--safe --without-K --lossy-unification`.
- **从头编译** (删去本路自己的 `.agdai`, 共用模块用已有接口, 堆上限 6G): 入口退出码 0 (2.5 秒, 0.45G).

## 时间线

写定义前读过: `HtTowerTy`, `HtTowerU`, `HtTowerCont`, `HtTowerStrat`, `HtTowerFNeed`, `HtTowerF`, `HtTowerFTree`, `HtTowerFRead`, `HtTowerFFold`, `HtTowerN`, `HtTowerNStage`, `LFRe`, `LFReTy`, `LFReTower`, `LFReNeg` 的陈述, `probes/README.md` 的 "主线与下一步" 与 "翻译账". 没有打开 `EBO`, `Correspond`, `Label`, 也没有读任何基本列规则. 读法是沿用前文的纸面判断.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CohW where

open import OCF.Align.CohWTy using (Chain; colim; pj; coh-pj; kmC; wmC; ιc; ιc-⊲; Lg-ιc; Incl; Le; Mle; rcoh→; rcoh←; wmLe) public
open import OCF.Align.CohWL using (XL; glL; chainL; U⋆; pjL; coh; inclL; kmU; wmU; needU; wmatchU; tri; rcohL→; rcohL←; κ0⋆; κ1⋆; yes-wmatch; same-bd) public
open import OCF.Align.CohWTower using (ν⋆; ι⋆; θ⋆; θ⋆-st; Λ⋆; Lg-θ⋆s; Lg-θ⋆; Lg-Λ⋆; old⋆; Lg-old⋆; up₁; Lg-up₁; StB; AccB; accB; accΛ⋆) public
open import OCF.Align.CohWNeg using (κL; same-S; same-E; no-cross→; no-cross←; no-route; no-route←; κA0; κAL; no-crossA→; no-crossA←; c₂; κL-layer; Lg-κL-layer) public
open import OCF.Align.CohWGl using (KE; H⁰; LH; Lv; GW; Lv⋆; cv; SL⋆; cmpL⋆; kmS; wmS; ιS; lvl; E-lvl; glob; globPr; cross; κa; κb; cross-ex; ofHB; Ω̂; Lg-Ω̂; tw; Λ; Lg-Λ; fix-form; Λn; Lg-Λn) public
open import OCF.Align.CohWUpd using (Upd; upd→wdec) public
```
