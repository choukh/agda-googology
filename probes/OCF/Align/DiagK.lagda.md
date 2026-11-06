# 可数层的对角: 每一级一个闭项, 在 `A` 里取对角

> 攀爬加摆脱侧, 与 [CohW](CohW.lagda.md) 并行的另一条路. 入口. **判决: PARTIAL.** 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延. 定义不读记号, 没有验收文件, 没有打开 `EBO`, `Lab`, 标签.
>
> 思路: 不造装下一切级的并 (那是 `CohW`), 而像 `src/OCF/BTBO` 的 $\lim_n\psi^n$ 那样, 每个有限级 $k$ 折叠出一个可数闭项 $t_k:A$, 再在 `A` 里取对角. 相邻两项的字面第一位置由**部分和**给出, 不比较两个折叠实例的值.
>
> 1. **对角 (定理).** 对任意合法的族 $x$, `Dg x = alim (x₀ + … + x_k)` 合法 (`Lg-Dg`), 相邻项字面是第一位置 (`pre-st`), 右边非零则严格 (`pre-strict`, `pre-<`); 回灌形状 $t_{k+1}=t_k+F(t_k)$ 同样合法 (`Lg-Dgᶠ`). 值: $x_k\le$ `Dg x`, `alim x ≤ Dg x`, 上确界加法封闭且严格高于每项时二者互相 $\le$ (`Dg≈sup`); 不封闭时部分和改了值 (`glitch`, 毛刺). [DiagKSum](DiagKSum.lagda.md).
> 2. **候选闭项的形状 (定理 + 条件读法).** `Top.Tᴰ`: 给一族级 (`Tower`) 与 "每一级一个折叠" (`LevelFold`), $T=$ `Dg (k ↦ fold k (top k))`, `Lg-Tᴰ` 对一切 `LevelFold` 成立, `fgh`. 级族 `towerL′` (`L′ (k+1)`, 级顶读 $\Lambda_k$) 上, **若** `fold` 读 $\psi_0(\Omega_\Lambda)$, 则 $T$ 读 $\psi_0\Lambda$ (判断). 合法性是盲的: 常值 $0$ 的折叠也合法 (`Lg-blind`). [DiagKTop](DiagKTop.lagda.md).
> 3. **没做到: $\psi_0\Lambda$ 的无条件闭项.** `towerL′` 的每一级都含 `Lev` 分量, **没有一级有折叠**; 对一切 $k$ 一致的折叠没有写. 未走通, 不是否定. 现成的槽位只有 `towerSn` 的第 0 级 (`HtTowerFClosed.T⁺`, 读 $\psi_0(\Omega_{\Omega_2})$).
> 4. **第一个障碍在级内, 不在并上 (条件定理 + 定理).** 有限多种类、按位置存界的级 `Sn k` 上, 改一个种类的界是定义, 种类相等可判定, 没有拷贝 (`upd`, `at`, `off`, `decK`, `rl-inj`, `wmS`, [DiagKPos](DiagKPos.lagda.md)). 但通向 $\Lambda$ 的级 `L′ (k+1)` 自己就含函数世界 `Lev (Ωtop (L′ k))`; 在它上面 "恰好改一个坐标处的分量" 推出 `HB (L′ k)` 上相等的弱判定 (`updL→wdec`, `updL′→wdec`, [DiagKLev](DiagKLev.lagda.md)). 所以 `CohWUpd.upd→wdec` 的陷阱在可数层的对角里**不消失**: 它不在一切级的并上, 在第 1 级之内就出现.
> 5. **现成族上的实例 (定理).** `Tdg₁ = Dg T-fb`, `Tdg₂ = Dg T-fb₂` 合法, 有 FGH; 读法同 `T-fbω`, `T-fb₂ω` ($\psi_0(\Omega_{\Omega_2})$, $\psi_0(\Omega_{\Omega_3})$), 两者之间没有定理. [DiagKInst](DiagKInst.lagda.md).

## 对协调者转来的两个陷阱

| 陷阱 | 在本路 | 依据 |
|---|---|---|
| `CohWNeg.no-cross`: `Lev` 新拷贝的种类与原种类的世界分量不相干 | 有限级 `Sn` 里没有拷贝: 每个读回位置恰一个种类, 低级嵌进高级只有一条路, 界定义相等 | `rl-inj`, `wmS`, `bnd-up`, `rl-up` (定理) |
| `CohWUpd.upd→wdec`: 按层号存界时改一层要判定 | `Sn` 里按位置存, 改一个分量是定义, 不要判定 (`decK` 可判定) | `upd`, `at`, `off`, `upd-≤`, `lg-upd` (定理) |
| 同上, 在含 `Lev` 的级里 | **避不开**: `L′ (k+1)` 的 `Lev` 分量是坐标上的函数世界, 恰好改一个坐标处的分量推出弱判定 | `updL→wdec`, `updL′→wdec`, `updH₀→wdec` (条件定理) |

判断: 有限级 (`Sn`) 的对角读 $\psi_0(\Omega_{\Omega_\omega})$, 远在 $\psi_0\Lambda$ 之下; 通向 $\Lambda$ 的级必须有以高度为下标的种类 (`no-retract`, `HtGen.no-top`: 单个种类结构不封口), 于是必有函数世界. "回灌时恰好升高一个种类的界, 低层输出落回原世界" (`HtTowerFFold` 的 `RunM`, `drp₁`) 在函数世界上就是 `UpdS`.

## 设计

| 件 | 定义 | 文件 |
|---|---|---|
| 字面的加法 | `TLRuleSpec._⊞_`; `⊞-fst`, `⊞-⊲`, `Lg-⊞`, `⊞-strict`, `⊞-<` | DiagKSum |
| 对角 | `pre x k`, `Dg x = alim (pre x)`; 回灌形状 `itr F a`, `Dgᶠ` | DiagKSum |
| 有限级的位置 | `rl` (读回位置), `bnd` (界的值), `upd`, `decK`; 嵌入 `kmS d k`, `wmS d k` | DiagKPos |
| `Lev` 世界的判别 | `tst`, `w0`, `w1` (对一切高度的 `Lev x`); `UpdS` (律 `atS`, `offS`) | DiagKLev |
| 级族 | `Tower` (`Lvl`, `top`, `ltop`); `towerL′` (`λh k = ι true (Ωtop (L′ k))`), `towerSn` (`Ωn`) | DiagKTop |
| 缺的一块 | `LevelFold Tw`: `fold k Λ lΛ : A`, `lg` | DiagKTop |
| 候选闭项 | `Top.t`, `Top.Tᴰ`, `Top.fgh` | DiagKTop |
| 槽位 | `fromB`, `fold₀` (`HtFeedClosed.TΛ`), `fold₁` (`HtTowerFClosed.T⁺`), `t₀Sn` | DiagKTop |
| 实例 | `Tdg₁`, `Tdg₂`, `fgh₁`, `fgh₂` | DiagKInst |

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `⊞-fst`, `⊞-⊲`, `Lg-⊞`, `⊞-strict` | DiagKSum | 加法的字面第一位置与合法 | 定理 |
| `pre-st`, **`Lg-Dg`**, `pre-strict`, `pre-<`, `pre⊲Dg` | DiagKSum | 部分和的对角合法, 相邻字面第一位置, 非零则严格 | 定理 (对一切族) |
| `Lg-itr`, `Lg-Dgᶠ` | DiagKSum | $t_{k+1}=t_k+F(t_k)$ 的对角合法 | 定理 (对一切保合法的 $F$) |
| `x≤pre`, `pre≤Dg`, `sup≤Dg`, `Dg-least`, **`Dg≈sup`** | DiagKSum | 值: 部分和与上确界; 上确界加法封闭且严格在上时互相 $\le$ | 定理 (`TLRuleSpec._≤_`) |
| **`glitch`** | DiagKSum | 常值 $1$ 的族: `Dg` 不 $\le$ 上确界 | 否定, 定理 (只杀 "部分和总不改值") |
| `bd≡pr`, `at`, `off`, `decK`, `upd-≤`, `lg-upd` | DiagKPos | `Sn k` 的界是存着的值, 按位置改一个, 种类相等可判定 | 定理 (对一切 $k$) |
| `rl-bd`, **`rl-inj`**, `wmS`, `bnd-up`, `rl-up` | DiagKPos | 每个读回位置一个种类; 跨级嵌入界定义相等 | 定理 (对一切 $k$, $d$) |
| `t0`, `t1` | DiagKLev | 每个 `Lev x` 的世界有可判别的底 | 定理 (对一切 `S`, $x$) |
| **`upd→wdec`**, **`updL→wdec`**, `updL′→wdec`, `updH₀→wdec` | DiagKLev | 并的世界上恰好改一个分量推出下标相等的弱判定; 实例 `Lev (Ωtop S)`, 一切 `S`, 一切 `L′ k` | 条件定理 (不是否定) |
| `wd-Ωtop`, `wd-L′`, `wd-L′f` | DiagKLev | `L′ (k+1)` 的世界含 $\prod_{c}\mathrm{Wd}(\mathrm{Lev}(\mathrm{up}\,c))$ | 定理 (`refl`) |
| `Lg-λh` | DiagKTop | 级顶合法 | 定理 |
| **`Top.Lg-Tᴰ`**, `Top.t⊲` | DiagKTop | 对一切级族与一切 `LevelFold`, 候选闭项合法 | 定理 |
| `Lg-blind` | DiagKTop | 常值 $0$ 的折叠也给出合法闭项 | 定理 (合法性的盲区) |
| `fromB-⊲`, `Lg-fromB`, `Lg-fold₀`, `Lg-fold₁` | DiagKTop | 现成折叠接上本路的接口 | 定理 |
| `Lg-Tdg₁`, `Lg-Tdg₂`, `fb₂≤` | DiagKInst | 回灌族的可数层对角合法; 每项在值上 $\le$ 对角 | 定理 |

## 闭项与读法

| 闭项 | 是什么 | 读法 (判断) |
|---|---|---|
| `Top.Tᴰ towerL′ Fd` | 对一切 `Fd : LevelFold towerL′` 合法; **不是闭项** (`Fd` 是参数) | 若 `Fd` 读 $\psi_0(\Omega_\Lambda)$: $\psi_0\Lambda$ |
| `Top.Tᴰ towerSn Fd` | 同上 | 若 `Fd` 读 $\psi_0(\Omega_\Lambda)$: $\psi_0(\Omega_{\Omega_\omega})$ |
| `Top.Tᴰ Tw (dummy Tw)` | 闭项, 合法 | 值是 $0$ (常值 $0$ 的族): 合法性不管值 |
| `t₀Sn` | `T⁺ (Ωn 0)` | $\psi_0(\Omega_{\Omega_2})$ |
| `Tdg₁`, `Tdg₂` | 闭项, 合法, 有 FGH | $\psi_0(\Omega_{\Omega_2})$, $\psi_0(\Omega_{\Omega_3})$ |

$\psi_0\Lambda$ 的读法链: `λh k` 读 $\Lambda_k$ (沿用 `HtTowerU`, `HtTowerN` 的判断); `fold` 读 $\psi_0(\Omega_\Lambda)$ (要求, 没有实例); $\sup_k\psi_0(\Omega_{\Lambda_k})=\psi_0\Lambda$ (纸面); 部分和不改上确界 (`Dg≈sup` 是定理, 但它的前提 "上确界加法封闭, 每项严格在下" 对这些树是判断). 读法链里没有一环是定理.

## 第一个障碍

1. **每一级的折叠 (未走通).** `towerL′` 的第 $k$ 级 `L′ (k+1)` 有两类种类: 链上的 `step (L′ k)` (有限多个新种类, 按位置) 与 `Lev (Ωtop (L′ k))` (以 `HB (L′ k)` 的高度为下标, 世界是函数). `HtTowerFFold` 的写法 (每种类一份走法与闭包, 回灌时升高一个种类的界, 低层输出经 `drp₁` 落回原世界) 在函数世界上要 `UpdS`, 而 `UpdS` 推出弱判定 (`updL→wdec`). 可试的出路 (判断, 没有试): (a) 回灌不改一个分量: 分支只取 "一切更大的世界", 回灌的第 $n$ 格取任意一个界够高的更大世界, 输出不落回原世界, 改由目标在更大的世界里 (要折叠的目标世界随回灌变大, `Tg` 的形状要改); (b) 世界按当前层的路径存元组 (`CohW` 出路 (b)); (c) 种类结构换成不含函数世界的写法 (要先绕过 `no-retract`: 以高度为下标的种类是必需的).
2. **对一切 $k$ 一致的折叠, 即使在 `Sn` 上 (没有写).** `Sn k` 没有上面的障碍 (`DiagKPos`), 但每个种类要一份走法、闭包、读回 (`HtTowerF` 对两种种类手写约 250 行, `HtTowerN` 的 `rd₂` 85 行), 要对位置递归写成一份: 读回层是数字层 $j$, 第 $j$ 种类的读回 `rd_j : D_j → HB (Sn (j-1))` 要 `toD_{j-1}`, 低层不看高分量的 `drp_t`. 判断规模约千行. 即使写出, 对角读 $\psi_0(\Omega_{\Omega_\omega})$, 不是 $\psi_0\Lambda$. 所以没有先写.
3. **值, 跨实例.** 本路不需要跨实例比较就有合法的对角, 但 $t_k$ 之间的值关系 (读法 "$t_{k+1}$ 远高于 $t_k$") 仍没有定理; 字面的严格只到 `pre-strict` 那一档 (只说明不塌缩).

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 部分和作对角 | 合法要相邻项字面第一位置; 两个折叠实例的值比较是开放问题 | **树逼的** (`Lg` 的定义); 值上的代价是毛刺 (`glitch`), 已两边算账 (`Dg≈sup`) |
| 回灌形状 `itr` | BTBO 的 $\lim\psi^n$ | 沿用 `src` 的形状, 不读记号 |
| 按位置的 `bnd`, `upd` | `Sn` 的世界就是元组 | 机械给出 |
| `tst`, `w0`, `w1` | 条件定理要判别分量 | 证明的脚手架 (约 30 行) |
| `Tower`, `λh` | 级顶取 `Ωtop`, 嵌进 `L′ (k+1)` 的链分量 | 沿用 `HtTowerU`, `HtTowerN` (`Lev` 的形状受作者对下标塔的直觉启发, 定义无记号); $\Lambda$ 只是目标 |
| `LevelFold` | 缺的一块写成类型 | 树侧 |
| `fromB` | `HB S₀` 与 `H` 同形 | 脚手架 (约 15 行), 由两套高度类型并存带来 |

**按 `AGENTS.md` 归类: 摆脱侧为主, 提供信息.** 加深的三个标志: 新构造子或字段读自基本列规则: **没有** (没有新构造子, 没有新的树或折叠); 闭包定理新增专属前提: **没有闭包定理**; 只能用 `Lab` 验收: **不是**. 提供信息的标志: 一步定理 `Lg-Dg` (对一切族), `upd`/`off`/`rl-inj` (对一切 $k$); 条件定理 `updL→wdec` 划出 "恰好改一个分量" 在函数世界上的代价; 否定定理 `glitch` 划出部分和的值代价. 攀爬: 没有新强度 (候选闭项是条件的).

## 账

**定义级切片** (口径同 `htfeed/locslice_htfeed.py`; 脚本复制到临时目录 `diagk/locslice_diagk.py`; 层 2 的根是闭项与它的 FGH, 层 3 加合法性定理).

| 闭项 | 层 1 (类型) | 层 2 (+折叠, 闭项, FGH) | 层 3 (+合法性) | 备注 |
|---|---|---|---|---|
| 条件候选 `Top.Tᴰ` (`towerL′`, 根 `fgh`, `Lg-Tᴰ`) | 284 (去共用 261) | 364 (去共用 281) | 385 (去共用 302) | **不含折叠** (折叠是参数 `LevelFold`); 只是对角与级顶的代价 |
| `Tdg₂` (根 `fgh₂`, `Lg-Tdg₂`) | 21 | 1057 (去共用 974) | 1086 (去共用 1003) | 折叠是 `HtTowerF` 的; 本路新加: DiagKSum 28, DiagKInst 8 |
| 对照: 记号侧 `EboLean3` | | | 1513 | 作者的标杆 |

- 条件候选的层 2 按模块: HtTowerTy 171, Free.Level 56, CumReadCF 36, HtTowerCont 31, BTBO 27, DiagKTop 22, DiagKSum 9, HtTowerNStage 8, TLRuleSpec 4. 本路新写的只有 31 行 (层 3 再加 21).
- `Tdg₂` 的层 3 与 `HtTowerN` 的 `T-fb₂ω` (1062) 差 24 行: 可数层的对角只比高度上的对角多部分和.
- 独立切片: `Dg≈sup` 61, `glitch` 44, `off` 201, `rl-inj` 199, `bnd-up` 230 (多数是 HtTowerTy), `updL′→wdec` 278 (DiagKLev 54), `Lg-blind` 95.
- 文件级 (代码块里非空非注释行): `DiagKSum` 86, `DiagKPos` 101, `DiagKLev` 77, `DiagKTop` 77, `DiagKInst` 30, 入口 7; 共 378.

## 审计

- **导入闭包** (`importclosure.py`, `--only` 表: `OCF.Free.Level`, `OCF.BTBO`, `OCF.Align.CumReadCF`, `TLRuleSpec`, `TLRuleSum`, `SumOne`, `HtGen`, `HtFeed`, `HtOut`, `HtCross`, `SumVar`, `HtTower`, `LFRe`, `DiagK`): `DiagK` (39 个模块, 本地 29), `DiagKSum` (16, 本地 6), `DiagKPos` (19, 本地 9), `DiagKLev` (18, 本地 9), `DiagKTop` (30, 本地 20), `DiagKInst` (32, 本地 22), 都是退出码 0, 禁用表 0, `--only` 之外 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `DiagKSum:Lg-Dg` 15/0/0, `Dg≈sup` 19/0/0, `glitch` 16/0/0, `fghᴰ` 26/0/0, `DiagKPos:off` 59/0/0, `rl-inj` 59/0/0, `bnd-up` 70/0/0, `DiagKLev:updL′→wdec` 82/0/0, `DiagKTop:Lg-Tᴰ` 28/0/0, `fgh` 40/0/0, `Lg-blind` 30/0/0, `Lg-fold₁` 201/0/0, `t₀Sn` 211/0/0, `DiagKInst:Tdg₂` 235/0/0, `fgh₂` 253/0/0, `Lg-Tdg₂` 246/0/0, `Lg-Tdg₁` 367/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用.
- **禁用构造**: 六个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 不用 `--cubical`, 不用函数外延; 都带 `--safe --without-K --lossy-unification`.
- **从头编译** (删去本路自己的 `.agdai`, 共用模块用已有接口, 堆上限 6G): 入口退出码 0 (2.5 秒, 0.49G).

## 时间线

写定义前读过: `AGENTS.md`, `probes/README.md` 的 "主线与下一步" 与 "翻译账", `Survey/EBOHandbook.md` 第 3, 4 节, `CumReadCF`, `HtTowerTy`, `HtTowerCont`, `HtTowerF`, `HtTowerFTree`, `HtTowerFFold`, `HtTowerFRead`, `HtTowerN`, `HtTowerNStage`, `HtTowerNFb` (部分), `HtFeed`, `HtFeedTree`, `HtFeedClosed`, `HtOut`, `HtOutRead`, `HtOutFeed` (部分), `HtTower`, `HtTowerU` (部分), `CohW`, `CohWUpd`, `TLRuleSpec` (§1, §2). 没有打开 `EBO`, `Correspond`, `Label`, 也没有读任何基本列规则. 读法是沿用前文的纸面判断.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DiagK where

open import OCF.Align.DiagKSum using (⊞-fst; ⊞-⊲; Lg-⊞; ⊞-strict; pre; Dg; pre-st; Lg-Dg; pre-strict; pre-<; itr; Dgᶠ; Lg-Dgᶠ; x≤pre; pre≤Dg; sup≤Dg; Dg-least; Dg≈sup; glitch; fghᴰ) public
open import OCF.Align.DiagKPos using (rl; bnd; bd≡pr; upd; at; off; decK; upd-≤; lg-upd; rl-inj; kmS; wmS; bnd-up; rl-up) public
open import OCF.Align.DiagKLev using (tst; w0; w1; UpdS; upd→wdec; UpdL; updL→wdec; updL′→wdec; updH₀→wdec; wd-L′f) public
open import OCF.Align.DiagKTop using (Tower; towerL′; towerSn; λh; Lg-λh; LevelFold; module Top; dummy; Lg-blind; fold₀; fold₁; t₀Sn) public
open import OCF.Align.DiagKInst using (Tdg₁; Tdg₂; Lg-Tdg₁; Lg-Tdg₂; fb₂≤; fgh₁; fgh₂) public
```
