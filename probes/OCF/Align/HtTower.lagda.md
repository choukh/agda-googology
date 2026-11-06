# 高度的高度: 树侧的下标塔

> 摆脱侧 (结构). 入口. **判决: PARTIAL (交付 (b), 加类型层的 (a)).** 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K. 定义不读记号, 没有验收文件, 没有打开 `EBO`, `Lab`, 标签.
>
> 一句话: 把 [HtFeedTree](HtFeedTree.lagda.md) 的高度 `H` 里 "$\Omega$-分支的坐标是 `A`, 在世界 `A` 里比" 抽成一个**种类结构** `KS`, 高度 `HB S` 对一切 `S` 一条定义, 比较 `cmpB` 对一切 `S` 一条定理. 三个构造 `step` (新种类的坐标是旧的合法高度, 世界加一个高度作界), `sup` (并), `Lev` (对高度结构递归得到种类结构, **种类以高度为下标**) 就写出整座下标塔: 一个种类结构 `U` 里, 塔的高度 `θ k` 一个接一个字面地是第一位置, ℕ-对角 `Λᵁ` 合法 (`Lg-Λᵁ`); 合法性是对 $k$ 的一步定理 (`Lg-θs`). 坐标是高度时连续的分支合法 (`cont→Lg`, 对一切 `S`). 四条否定定理划出不能有的形状: 分支不能取遍高度自己 (`no-self`, `no-retract`), 连续要对旧种类的 $\Omega$-极限 (`drop-Ω`), 逐级独立写的塔不能取对角 (`no-naive-diag`), 世界的分量没有字面的并 (`no-joinᴮ`, `no-joinA`).
>
> **没有做到的: 折叠.** 这一轮没有接受 `HB S` 作层的折叠, 所以没有新的闭项 (序数树), 没有增长定理, 塔的读法都是判断. 折叠要的东西与第一个障碍见下.

## 设计

| 件 | 定义 | 文件 |
|---|---|---|
| 种类结构 | `KS`: 种类 `K`, 坐标 `E κ`, 世界 `Wd` (序 `≤w`, 合法 `LgW`), 界 `Bd κ c w`, 第一位置 `Pr κ w c c′`, 界下比较 `cmpK`, 坐标合法 `LgE`, 最小坐标 `bot` | [HtTowerTy](HtTowerTy.lagda.md) |
| 底 | `S₀`: 一种种类, 坐标与世界都是 `A`; `HB S₀` 就是 `H` 的形状 (`toB`) | 同上, [HtTowerU](HtTowerU.lagda.md) |
| 高度 | `data HB S = hz \| hs \| hl (ℕ → HB S) \| hΩ κ (E κ → HB S)` | HtTowerTy |
| 第一位置, 合法, 比较 | `_⊲[_]_` (进 `hΩ κ g` 的坐标要在世界的 $\kappa$-界之下), `LgB` (ℕ-步进在一切世界, $\Omega$-单调在一切合法世界的界下), **`cmpB`** | 同上 |
| 一步 | `step S`: 种类 `K S ⊎ ⊤`; 新种类坐标 `HB S`, 界是世界的新分量 $b$, 第一位置与比较就是 `HB S` 的 `⊲`, `cmpB`; 嵌入 `up` | 同上 |
| 并 | `sup I F`: 种类 $\Sigma_i K(F i)$, 世界逐分量; 嵌入 `ι` | 同上 |
| 级 | `Lev : HB S → KS`: $0\mapsto$ `S₀`, 后继 $\mapsto$ `step`, 两种极限 $\mapsto$ `sup` | 同上 |
| 连续 | `ContB g`: `c-lim`, **`c-Ω`** (旧种类的 $\Omega$-极限处连续), `c-suc`, 起点与后继保合法; `cont→Lg`; `nbᴮ`; `Ωtop S = hΩ new up` | [HtTowerCont](HtTowerCont.lagda.md) |
| 逐级塔 | `Sn k = stepᵏ S₀`, `Ωn k = Ωtop (Sn k)` (对照, 对角不合法) | HtTowerU |
| 下标塔 | `L 0 = S₀`, `L (k+1) = Lev (Ωtop (L k))`; `U = sup ℕ (step ∘ L)`; `θ (k+1) = hΩ (k,new) (c ↦ θ k ⊞ c)`; `Λᵁ = hl θ` | HtTowerU |
| 分层 | `KB k`: 只用分量 $<k$ 的种类; `below-θ`, `indep`, `θ-indep` | [HtTowerStrat](HtTowerStrat.lagda.md) |
| 否定 | `no-self`, `no-retract`, `drop-Ω`, `no-naive-diag`, `naive-illegal`, `no-joinᴮ`, `no-joinA` | [HtTowerNeg](HtTowerNeg.lagda.md) |

**为什么种类结构, 不是一个高度类型.** "一个高度类型, 分支取遍高度自己" 直接写 Agda 的正性检查不收. 换成任何编码 (分支的坐标里有全部高度的收缩) 也不行: `no-retract` 只用高度的良基就推出矛盾. 所以塔必须分级, 每一级只以更低的级作坐标, 并且**不会在一个种类结构里封口**: `U` 里没有以 `HB U` 为坐标的种类. 这与 `HtGen.no-top`, `HtFeedNeg.no-world-top` 同一类现象, 这里是对一切种类结构的定理.

**为什么世界要带每个种类的界.** 新种类的两个坐标要比较 (`cmpB` 走进同一个 $\Omega$-节点的两个分支), 就要它们有字面的公共上界; 新世界的分量 $b$ 就是这个上界. 与 `HtFeedTree` 的世界同一个理由 (壁垒, `HtFeedNeg.no-glob`). 这里没有新证一条 `no-glob`; `no-joinᴮ` 说这个上界不能由两个坐标算出来 (没有字面的并), 只能由世界给.

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| **`cmpB`** | HtTowerTy | 对一切 `S`: 合法高度在一个合法世界里的两个第一位置可比 | 定理 (构造) |
| `⊲ᴮ-tr`, `⊲ᴮ↑`, `z⊲ᴮ`, `lgB⊲`, `⊞-fst`, `⊞-⊲`, `Lg-⊞` | HtTowerTy | 第一位置的传递, 世界变大, 合法遗传, 加法 | 定理 |
| `step`, `sup`, `Lev` | HtTowerTy | 种类结构的三个构造; `step` 的新比较就是 `cmpB` | 定义 (字段是定理) |
| `up-⊲`, `Lg-up`, `ι-⊲`, `Lg-ι` | HtTowerTy | 嵌入保第一位置与合法 | 定理 |
| `cont-mono`, **`cont→Lg`** | HtTowerCont | 对一切 `S` 与一切新种类上的分支 $g$: `ContB g` 推出单调, 推出 `LgB (hΩ new g)` | 定理 |
| `nb-contB`, `up-cont`, `Lg-Ωtop` | HtTowerCont | 对坐标递归的分支连续; 嵌入连续; 第一个 $\Omega$ 合法 | 定理 |
| `toB-⊲`, `Lg-toB`, `Lg-old` | HtTowerU | `HtFeed`, `HtOut` 的合法高度是 `U` 的合法高度 | 定理 |
| `Lg-Ωn` | HtTowerU | 逐级塔的每一级合法 | 定理 |
| `θ-st`, **`Lg-θs`**, `Lg-θ`, **`Lg-Λᵁ`** | HtTowerU | 塔的高度相邻字面第一位置 (一切世界); 一步定理对 $k$; 对角合法 | 定理 |
| `KB-θs`, `below-θ`, `indep`, **`θ-indep`** | HtTowerStrat | 低于 `θ k` 的高度只用分量 $<k$ 的种类, 第一位置不看世界的高分量; 一步定理对 $k$ | 定理 |
| **`no-self`**, `no-retract` | HtTowerNeg | 对一切 `S`, $\kappa$: 分支不能在某坐标上取回自己的节点; 没有全部高度的收缩 | 否定, 定理 |
| **`drop-Ω`** | HtTowerNeg | `gω` 满足 `ContB` 的其余四条, 不满足 `c-Ω`, `¬ LgB (hΩ new gω)` | 否定, 定理 (前提有见证) |
| **`no-naive-diag`**, `naive-illegal` | HtTowerNeg | 逐级塔的相邻两级在并里不是第一位置; 对角不合法 | 否定, 定理 |
| **`no-joinᴮ`**, `no-joinA` | HtTowerNeg | 任一 `S` 的任一合法世界里 (`A` 里同样), 两个合法高度没有合法的字面公共上界 | 否定, 定理 (前提有见证: `Lg-ev`, `Lg-od`, 世界 `azero`) |

**否定的范围.**
- `no-self` 只否定 "某个坐标上分支等于自己的节点"; `no-retract` 是它的推论, 要收缩对一切高度成立. 不否定 "分支取遍低于某个界的高度" (那正是 `Lev` 做的), 也不否定只对合法高度的收缩 (那要 `hΩ κ d` 合法, 不自动成立; 没有试).
- `drop-Ω` 只说 `c-Ω` 不能去掉 (四条字段之外); 不说 `LgB (hΩ new g)` 推出 `ContB g`.
- `no-naive-diag` 只杀 "各级各自取 `Ωtop`, 再在 `sup ℕ` 里取对角"; `θ` 把下一级接在上一级后面就合法. 原因是嵌入 `ι (k+1) ∘ up` 与 `ι k` 不是定义相等的 (没有函数外延也不能证明相等), 各级的高度在并里落在不同的分量.
- `no-joinᴮ` 只说这一对高度没有字面的并; 不说任何两个高度都没有.

## 塔与读法

**读法都是判断** (纸面; `hΩ κ g` 读 $\sup_c g(c)$, 坐标类型的大小读作基数). 没有折叠, 所以下面的 $\psi_0$ 都只是 "如果有一个接受这些层的折叠, 按 `HtFeed` 的读法" 的意思.

| 高度 | 读法 (判断) |
|---|---|
| `HB S₀` 的一切高度 | 下标 $<\Omega_2$ (与 `H` 同) |
| `θ 1` | $\Omega_2$ |
| `HB (L k)` 的一切高度 | 下标 $<\Lambda_k$; $\Lambda_0=\Omega_2$, $\Lambda_{k+1}\approx\Omega_{\Lambda_k+1}$ (`L (k+1)` 是 "低于 $\Lambda_k$ 之上第一个 $\Omega$ 的一切级") |
| `θ (k+1)` | $\approx\Lambda_k$ |
| `Λᵁ` | $\Lambda=\sup_k\Lambda_k$, $x\mapsto\Omega_x$ 的第一个不动点 |
| `HB U` 的一切高度 | 下标 $<\Omega_{\Lambda+1}$ (`Λᵁ`, `hs Λᵁ`, … 都在里面; `no-retract` 说没有以 `HB U` 为坐标的种类) |

与已有闭项的关系 (判断): `HtOut.T-fbω` 的高度 $x_\omega=\sup_n x_n$, $x_{n+1}$ 是第 1 层输出的读回; 按 Buchholz 的读法 $x_\omega$ 是 $x\mapsto\psi_1(\Omega_x)$ 的迭代极限, 而 $\psi_0(\Omega_{\Omega_2})$ 的基本列正是这串迭代, 所以 `T-fbω` 读 $\psi_0(\Omega_{\Omega_2})=\psi_0(\Omega_{\theta 1})$. **塔从 `θ 1` 往上的部分要接受 `HB (step S₀)` 的层的折叠才有闭项**; 这与 `HtOut` 的判断 "$x_\omega$ 之上要第三数类的高度树" 一致, `step S₀` 的新种类就是第三数类的分支.

## 第一个障碍

1. **折叠只认一种闭包.** `HtFeedFold` 的节点、目标、比较都只用到层的 `⊲[_]`, `cmpH`, `StH`, `accL`, 这些对 `HB S` 照搬 (判断, 没有写). 不照搬的是闭包 `nκ`: 它的分支以 `A` 的世界为下标, 保留时沿 `A` 的路径走到目标的世界 (`Cut`, `IW`, `Walk`, `Kp`), 回灌时把第 0 层输出经 `sum` 读成新世界 (`κc`, `κΔ`), 再用 `drp` 丢掉世界 (第 0 层的树不依赖世界). 层里有新种类的分支 (`hΩ (inj₂ tt) g`) 时, `Ωd` 要一个**以新种类坐标为下标的闭包**, 折叠要:
   - (i) 世界换成 `Wd S`, 闭包升高世界的对应分量;
   - (ii) 保留时沿新种类坐标的路径走: 这种路径经过旧种类的 $\Omega$-极限 (`hLim`), 所以走一段要用旧种类的闭包与旧种类的走法 (逐级递归);
   - (iii) 回灌时读第 $\ell$ 层的输出作新的界 (`ℓ` 是这个种类的读回层; `HtOut.rd` 是 `step S₀` 的新种类、$\ell=1$ 的实例), 再丢掉升高的分量. 能丢是因为低于读回层的层不看高分量 (`θ-indep`, 类型层的定理); 不能改用两个世界的并, 因为并不存在 (`no-joinᴮ`, `no-joinA`).
   - (iv) 种类与读回层的对应: `U` 的新种类 $(k,\mathrm{new})$ 对应 `θ k`; `Lev` 内部生成的旧种类没有指定读回层, 它们与 `U` 的低分量种类不是字面相同的 (判断; `Lev` 对 `ι` 不是定义相等的, 同 `no-naive-diag` 的原因). 这一条是 `U` 特有的, 逐级塔 `Sn` 没有 (种类就是数字层).

   这一轮没有写折叠, **未走通, 没有否定定理**; 不是路线已否定. 判断: (i) (ii) (iii) 在 `step S₀` (两种种类, 世界 `A × H`) 上是 `HtFeedTree`, `HtFeedFold`, `HtOutRead` 的逐个推广, 规模约千行; 对一切 `S` 一个折叠, 要先解决 (iv).
2. **值.** 没有任何闭项, 也就没有值或参照树的 $\preccurlyeq$.

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `KS` 的字段 | `HtFeedTree` 里 `H` 对 `A` 的用法 (`hLim : c ⊲ W`, `cmpF`, `lg⊲`, `z⊲`) 抽出来 | 树侧, 不读记号 |
| `HB`, `⊲[_]`, `LgB`, `cmpB` | `H`, `LgH`, `cmpH` 对一切 `S` | 树侧; `cmpB` 是一条定理对一切级 |
| ℕ-步进写在一切世界 (不是世界 $0$) | 一般的 `KS` 没有最小世界 | 选择 |
| $\Omega$-单调写在界下的一切合法世界 | 与 `LgH` 的写法可互推 | 选择 |
| `step` 的新世界分量 $b$ | 新种类坐标的比较要字面公共上界 | **树逼的** (壁垒; `no-joinᴮ`: 上界不能算出来) |
| `step` 保留旧种类 (`K ⊎ ⊤`) | 否则写不出 "新种类的界之上再加旧种类的 $\Omega$" 这类高度 | 选择 (判断, 没有定理) |
| `sup` 的逐分量世界 | 并 | 树侧 |
| `ContB` 的 `c-Ω` | `cont-mono` 走进旧种类的 `hLim` | **树逼的** (`drop-Ω`) |
| `Lev` (种类以高度为下标) | 对高度结构递归 | 定义树侧; **想法受记号启发** (作者 2026-11-05 的直觉: EBO 的下标塔 $\Lambda=\Omega_{\Omega_{\dots}}$ 在树里有对应) |
| `L (k+1) = Lev (Ωtop (L k))` | 下一级 = 上一级之上第一个 $\Omega$ 的一切级 | 定义树侧; 形状受记号启发 ($x\mapsto\Omega_x$) |
| `θ (k+1)` 接在 `θ k` 后面 (`⊞`) | ℕ-对角要相邻项是字面第一位置 | **树逼的** (`no-naive-diag`) |
| 塔不封口 | 分支不能取遍自己 | **树逼的** (`no-self`, `no-retract`) |
| 分层 `KB`, `θ-indep` | 塔的形状的推论 | 树侧 |

**按 `AGENTS.md` 归类: 提供信息; 摆脱侧 (结构), 没有攀爬.**
- 加深的三个标志: 新构造子或节点字段读自基本列规则: **没有** (没有读任何基本列规则; `HB` 是布劳威尔树, 构造子由 `KS` 机械给出). 闭包定理新增专属前提: **没有** (`cmpB`, `cont→Lg`, `Lg-θs`, `KB-θs` 都对任意参数, 无额外前提). 只能用 `Lab` 验收: **不是** (没有验收).
- 提供信息的三个标志: 对结构参数的一步定理: **有** (`cmpB` 对 `S`, 新用到的字段是种类的 `cmpK`; `cont→Lg` 对 `S` 与 $g$, 新用到的字段是 `c-Ω`; `Lg-θs` 对 $k$, 新用到的字段是 `step` 新种类的界与 `sup` 的分量世界; `KB-θs` 对 $k$). 序数值验收: **没有** (没有折叠). 否定定理划出字段: **有** (`no-self`, `drop-Ω`, `no-naive-diag`, `no-joinᴮ`).
- 摆脱了什么: `HtFeed`, `HtOut` 里 "高度的分支只有一种, 坐标是 `A`" 这一点; 每升一级 (`step`) 不加新定理, 也不加维 (对照 `SumClimb` 的每级一维). 没摆脱的: `Lev` 与 `L` 的形状受记号的下标塔启发; 折叠没有写.

## 账

**定义级切片** (口径同 `htfeed/locslice_htfeed.py`: 计 agda 非空非注释行, 记号模块除外; 脚本在临时目录 `httower/locslice_httower.py`, 读 `agda --html` 的输出). 本路没有折叠, 所以四层表的层 2 (折叠, 闭项, FGH) 与层 3 (闭项的合法) 为空; 下表是高度这一层的切片.

| 切片 | 行数 | 按模块 |
|---|---|---|
| 类型层: `KS`, `HB`, `step`, `sup`, `Lev` | 208 (去共用 185) | HtTowerTy 149, CumReadCF 36, BTBO 23 |
| + 塔 `Λᵁ` (`L`, `U`, `θ`) | 243 (去共用 220) | 多 HtTowerU 16, HtTowerTy 17, HtTowerCont 2 |
| + 合法 `Lg-Λᵁ` 与 `cmpB` | 289 (去共用 266) | 多 HtTowerU 11, HtTowerTy 35 |
| + 连续 (`cont→Lg`, `Lg-Ωtop`) | 净增 29 | HtTowerCont 29 |
| + 分层 (`θ-indep`) | 净增 37 | HtTowerStrat 37 |
| + 旧高度嵌入 (`Lg-old`) | 净增 35 | HtTowerU 20, HtFeedTree 15 |
| 否定 (独立切片) | 368 | HtTowerTy 156, HtTowerNeg 146, CumReadCF 36, BTBO 23, 其余 7 |

- 类型层已经含 `LgB` 与 `cmpB`: `step` 的新种类的界下比较就是 `cmpB`, 坐标合法就是 `LgB`, **下一级的类型要上一级的合法性与比较** (同 `HtFeed` 的 "高度的合法性在层 2"). 所以 "+合法" 只多 46 行 (塔的一步定理与 `Lg-ι`, `Lg-up`, `Lg-⊞`).
- 对照: `HtFeedTree` 的 `H`, `LgH`, `cmpH` 的切片 101 行 (一种种类); 这里对一切种类结构, 加上 `step`, `sup`, `Lev`, 类型层 208 行. 每升一级 (任意多级, 含以高度为下标的级) 不再加行.
- 否定各自的切片: `no-retract` 40, `no-joinA` 87, `no-joinᴮ` 119, `drop-Ω` 202, `naive-illegal` 251 (后两条含 `step`).
- 文件级 (代码块里非空非注释行): `HtTowerTy` 215, `HtTowerCont` 47, `HtTowerU` 65, `HtTowerStrat` 54, `HtTowerNeg` 184, 入口 7; 共 572.

## 审计

- **导入闭包** (`importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRuleSpec --only OCF.Align.TLRuleSum --only OCF.Align.SumOne --only OCF.Align.HtGen --only OCF.Align.HtFeed --only OCF.Align.HtOut --only OCF.Align.HtCross --only OCF.Align.SumVar --only OCF.Align.LevelFix --only OCF.Align.LevelNoK --only OCF.Align.HtTower`): `HtTower` (17 个模块, 本地 9), `HtTowerTy` (10, 本地 3), `HtTowerCont` (11, 本地 4), `HtTowerU` (13, 本地 6), `HtTowerStrat` (14, 本地 7), `HtTowerNeg` (15, 本地 7) 都是退出码 0, 禁用表 0, `--only` 之外 0. 本地模块只有 `OCF.BTBO`, `CumReadCF`, `HtFeedTree` (只经 `HtTowerU.toB`) 与本路的文件.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `HtTowerU:Λᵁ` 73/0/0, `HtTowerU:Lg-Λᵁ` 84/0/0, `HtTowerTy:cmpB` 21/0/0, `HtTowerTy:Lev` 58/0/0, `HtTowerCont:cont→Lg` 47/0/0, `HtTowerStrat:θ-indep` 83/0/0, `HtTowerU:Lg-old` 82/0/0, `HtTowerNeg:no-retract` 11/0/0, `HtTowerNeg:drop-Ω` 60/0/0, `HtTowerNeg:naive-illegal` 76/0/0, `HtTowerNeg:no-joinᴮ` 33/0/0, `HtTowerNeg:no-joinA` 30/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明没受记号启发 (见翻译账: `Lev`, `L` 的形状受记号启发).
- **禁用构造**: 六个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 不用 `--cubical`; 都带 `--safe --without-K --lossy-unification`.
- **从头编译** (`--ignore-interfaces`): 入口退出码 0 (23 秒, 1.0G).

## 时间线

写定义前读过: `AGENTS.md`, `probes/README.md` 的 "主线与下一步" 与 "翻译账", `HtFeed`, `HtFeedTree`, `HtFeedFold`, `HtFeedClosed`, `HtFeedGrow`, `HtOut`, `HtOutRead`, `HtOutFeed`, `HtOutGrow`, `HtOutNeg`, `HtGen` 的入口与 `no-top`, `LevelNoK` 的入口, `Survey/RouteSeal.md` 第 5 条, `CumReadCF` 的定义, `GuardBridgeNeg.no-join` 的陈述. 没有打开 `EBO`, `Correspond`, `Label`, 也没有读任何基本列规则. 塔的读法 ($\Lambda_k$, $\Lambda$) 与 Buchholz 的读法是手算的纸面判断.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTower where

open import OCF.Align.HtTowerTy using (KS; S₀; HB; hz; hs; hl; hΩ; _⊲[_]_; LgB; cmpB; _⊞_; step; up; up-⊲; Lg-up; sup; ι; ι-⊲; Lg-ι; Lev) public
open import OCF.Align.HtTowerCont using (ContB; cont-mono; cont→Lg; nbᴮ; nb-contB; up-cont; Ωtop; Lg-Ωtop) public
open import OCF.Align.HtTowerU using (toB; Lg-toB; Sn; Ωn; Lg-Ωn; L; FU; U; θ; θ-st; Lg-θs; Lg-θ; Λᵁ; Lg-Λᵁ; old; Lg-old) public
open import OCF.Align.HtTowerStrat using (KB; KB-θs; below-θ; indep; θ-indep) public
open import OCF.Align.HtTowerNeg using (no-self; no-retract; gω; drop-Ω; no-naive-diag; naive-illegal; no-joinᴮ; Lg-ev; Lg-od; no-joinA; Lg-evA; Lg-odA) public
```
