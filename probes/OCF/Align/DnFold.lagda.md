# 有内容的下降 (入口与判决)

> 不含记号. 目标 (作者原话): "写出 ψ₀Λ 的候选闭项". 本路 (前缀 `DnFold`) 是 [KcFold](KcFold.lagda.md) 的续作的**构造**一路: 给出有内容的下降 `DnK (Lev (B s))`, 代入 `KcFoldTower.KD`, 让读回进入闭项. 否定一路前缀 `NegDnFold`, 共用接口 [DnFoldIf](DnFoldIf.lagda.md) (接口定稿 2026-11-05 16:13, 变更记录: 无). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP 作前提. 无条件闭项与证书无模块参数.
>
> **判决: PARTIAL.**
>
> - **(a) 交了.** 无条件闭项 `DnFoldK.TD : A` (证书 `Lg-TD`, FGH `fghD`), 是 `KD dnD dnL₀` 的闭项; 下降 `dnD` 第 0 站取恒等 (无损), **第 1 站经求值** (D1: 层号经 `μ′` 搬进 `Ht`, 高度经桥搬进带有限外层世界 $(N,N)$ 的层 `LvH`, 读成数据树, `Run` 求到第 2 层再读回 `Ht`, 对 $N$ 取部分和的 ℕ-极限), 第 2 站起与极限站取截断版的常数. 另一个闭项 `DnFoldDc.TH₁ : A`: 层号在 `Ht` 的第 1 站同形物 `c₁H = hs (hΩ κH (y ↦ 1 ⊞ y))`, 外层世界 $(\omega,\omega_0)$, 读回经求值降到 `Ht` (不经塔).
> - **第 1 站 (接手清单第 1 条) 写出了一半.** `LvOm` 推广到层号在 `Ht` 写成了 (`DnFoldRd`: κA, κH 两种种类一行, 外层世界 `A × H₀`, 读回的可入判定用 `KcFoldBdec.bdecLv (hs hz)`, 公共上界是读的世界), 由它的下降 `dnH : DnK (LvH a c)` 对一切合法的 $a$, $c$ 与第 2 层的证据. **从 `Lev (B 1)` 到带世界的层的桥只能有损**: `Lev` 的种类下标是裸的 `H₀` (`DnFoldObs.levIdx`), 带世界的层的种类下标带可入证据 (`lvhIdx`); 保留可入下标的桥与裸判定等价 (否定一路 `NegDnFoldAdm.Keep.keep→dec`), 外层世界 `A`-分量为 $\omega$ 时撞分离子 (`keepS₁-sep`). 本路取有限外层世界, 判定对下标的构造子递归, 有限下标 $\le N$ 全留下 (`decH-fin′`, `decA-fin′`), 无穷下标全丢.
> - **第 2 站起 (接手清单第 2 条) 未走通.** 第 $s+2$ 站层号的头的坐标是 `HB (Lev X_s)` (`KcFoldTower.Shape.coord-new`), 数据树的层在 `Ht`, 坐标只有 `A`, `H₀` (`ht-coords`); `μ′` 只对 `Kc 1` 写. 接口 §3 的 `EvSys`, `EvSysK` 写了类型 (层的类型推广到 `HB (step K)`), 没有实例.
> - **(b) 值: 没有定理.** `TpPort` 的单调要输入不含 $\Omega$-极限, 本路的回灌输出含 (`Hs0-shape`). 所以没有 `TD` 与 `Tkc` 的值的比较. **不是 ψ₀Λ 已写出.**
>
> **对否定一路的回应 (主审转告).** 接口 §5 的四条忠实律被常数下降 `NegDnFoldBlind.dnC` (每站输出 $2$) 满足, 不能说明读回进了闭项. 本路排除 `dnC` 这类下降的陈述只有**形状定理**, 没有值的界: 第 0 站回灌输出就是读回本身 (`Hs0-rd`, `Hs0-shape`: 含 κH 的 $\Omega$-结点); 第 1 站回灌输出是求值的部分和 (`Hs1`), 求值的输入是读回经桥的像, 读回的新种类结点原样留下 (`rd-kept`), 翻译成数据树后是过第 `LyH (μ′ X₀)` 层的 `ni` 结点, 分支读回数据再经桥翻译 (`tr₁`). 这些只说读回在哪里进了求值的输入, 不说 `Hs 1` 的大小; 第 2 站起与截断版定义相等 (`HsSS`). 第 $s+1$ 站的下降没有左逆 (否定一路 `no-faithfulB`), 本路不写 "可取回" 的读法.
>
> **对纲领与目标.** 纲领 1: 闭项是 `A` (布劳威尔树) 的元素, FGH 在树上算; 求值用两种种类折叠的 `Run`, 读回由形状给出合法. 纲领 2: 无公理; 读回包对层号结构递归, 桥对层号与高度结构递归, 可入判定对下标的构造子递归. 纲领 3: 读回里的判定都在公共上界之下 (`bdecS₁`); 桥的判定是裸的, 只在外层世界有限时写 (有限外层世界的第一位置只有有限个字面的项), 没有对含 $\omega$ 的外层世界判定. 纲领 4: 导入闭包与切片干净 (审计). 目标 "让树自足": `DnFoldRd` 的 $\Omega$-行对一切种类一条 (κA, κH 不分开写), `μ′` 的合法由世界的翻译给出 (`ωW`, `basebot`: 丢掉的种类在基世界里只有底坐标); 这一站新用到的字段是 `Bd↑ S₁` (外层世界的证据搬进当前世界) 与 `KcFoldBdec.bdecLv (hs hz)`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DnFold where

import OCF.Align.DnFoldIf
import OCF.Align.DnFoldEv
import OCF.Align.DnFoldRd
import OCF.Align.DnFoldDc
import OCF.Align.DnFoldMu
import OCF.Align.DnFoldBr
import OCF.Align.DnFoldK
import OCF.Align.DnFoldObs
```

## 接口 (`DnFoldIf`, 只有类型)

```text
LvH a c = LvW {S₁} a c        ; LyH c (逐构造子, hz ↦ 1)            -- 层号在 Ht, 外层世界 A × H₀
DnEv S   (Lw, lLw, o1, Wv, lWv, ev2, tr : HB S → D Lw Wv)          -- (D1) 经求值, 层在 Ht
EvSys    (Lay, Wor, LgWo, Dat, Ok, evH, lgEv) ; DnEvS E S ; EvSysK K = Σ EvSys (Lay ≡ LayK K)   -- (D1′)
DnSq T   (sq, lsq, cs, comb, sq-new : sq (hΩ new g) ≡ comb (n ↦ sq (g (cs n))))             -- (D2) 有损
rdTop T = hs (Ωtop T) ; rdCut T ; FaithRd ; Faith0 ; FaithTower ; DiffTkc                    -- 忠实 (盲, 见上)
RestrK K ; ExactAdm K a                                                                       -- 桥与裸判定的类型
```

律的定义域写在接口文件头. 变更: 无.

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `EvAt.evAt`, `lg-evAt`, **`toDn`**, `evSysHt`, `toDnS`, `ofDnEv` | Ev | 层 $L$ 上的数据树经 `Run` 求到第 2 层读回 `Ht`; 由 `DnEv` 得下降, 合法由读回的形状给出 | 定义; 定理 |
| `bdecS₁`, `Rd.eA`/`eS`/`eM`, `RW.rdW`, `fstW`, `lgW`, **`Rd.pk`**, `trN`, `rdc`, `lgc`, `PΩ.*` | Rd | 层号在 `Ht` 的读回包, $\Omega$-行对一切种类一条, 公共上界之下判定 | 定义; 定理 |
| `LyH-mono`, `lgLyH`, `o1H`, `e2-of`, **`dnH`**, `dnHs`, `dnEvH` | Dc | `DnK (LvH a c)` | 定义; 定理 |
| **`TrShape.tr-top`**, `tr-cut` | Dc | 读回翻译成过前一层的 `ni` 结点, 分支读回数据; 截断的分支是 `n0` | 定理 (`refl`) |
| **`TH₁`**, `Lg-TH₁`, `fghH₁`, `HD₁`, `X₁H`, `c₁H`, `aω` | Dc | 层号在 `Ht` 的第 1 站同形物的闭项 | 构造; 无条件 |
| `Kd1`, `kd1`, **`μ′`**, `ωW`, `basebot`, `μ-⊲`, **`Lg-μ′`**, `one⊲` | Mu | 第 1 站层号搬进 `Ht`, 保合法, 第 1 层总是第一位置 | 定义; 定理 |
| `PE`, `mapP`, `stepPE`, `decA`, `decH`, **`Br.F`**, `Br.G` | Br | 部分种类映射; 有限外层世界的可入判定; 第 1 站的桥 | 定义 |
| `ev₁`, **`dn₁`**, **`dnD`**, **`TD`**, **`Lg-TD`**, **`fghD`**, `TD∞` | K | 代入 `KD` 的下降与闭项 | 构造; 无条件 |
| **`Hs0-rd`**, `Hs0-shape`, **`diffD`**, `faith0D` | K | 第 0 站输出就是读回; 与截断版不同; 第 0 站忠实 | 定理 |
| **`Hs1`**, **`rd-kept`**, **`tr₁`**, `HsSS` | K | 第 1 站输出是求值的部分和, 求值的输入含读回的新种类结点; 第 2 站起同截断版 | 定理 (`refl`) |
| `t-keep`, `t-drop`, `t-dropω` | K | 桥的可入判定: 留 $1\le2$, 丢 $2>1$, 丢 $\omega$ | 有限测试 |
| `levIdx`, `lvhIdx`, `sLH-adm` | Obs | 种类下标: `Lev` 裸, `LvH` 带证据; 数据树结点带证据 | 定理 (类型事实) |
| **`decH-fin′`**, **`decA-fin′`**, `eqH-self`, `eqA-self` | Obs | 有限下标 $\le N$ 都留下 | 定理 |

## 闭项与 FGH 的类型原文

**无条件 (无模块参数):**

```text
DnFoldK.TD      : A          -- KQ.TΛ∞ω, KQ = KD dnD dnL₀
DnFoldK.Lg-TD   : Lg TD
DnFoldK.fghD    : ℕ → ℕ      -- FLv.FGH (ord TD)
DnFoldK.TD∞     : A          -- KQ.TΛ∞ (只有有限站)
DnFoldK.dnD     : DnTower
DnFoldDc.TH₁    : A          -- T⁺ HD₁ lgHD₁
DnFoldDc.Lg-TH₁ : Lg TH₁
DnFoldDc.fghH₁  : ℕ → ℕ
```

**条件版**: 沿用 `KcFoldTower.KD dn dnL` (前提只有下降). 本路的 `dnH a la c lc e2 : DnK (LvH a c)` 的前提 `e2` (第 2 层在 $a$ 里是 `LyH c` 的第一位置) 在 `hs hz ⊲[ a ] c` 时由 `e2-of` 给出.

## 前提实例

- `dnH`: 实例 `dnHs aω laω c₁H lX₁H one⊲c₁` (闭项 `TH₁`); `ev₁ N b lb` 对一切 $N$, 一切合法 $b$ (第 2 层证据由 `one⊲` 给出).
- `Br N`: 一切 $N$; 外层世界 $(N,N)$ 合法 (`laN`).
- `DnEv`, `EvSys`: 实例 `ev₁`, `dnEvH`, `evSysHt`. `EvSysK K`: 没有实例. `DnSq`: 本路没有用 (否定一路有 `dsqC`).

## 读法 (全部是判断)

| 对象 | 读法 (判断) | 依据, 测到哪里 |
|---|---|---|
| `KQ.Hs 0` | 第 1 级的级顶后加 1 ($\Omega_2+1$ 量级), 截断版是 $\Omega_2$ | `Hs0-shape` (定理); 读法沿用 `HtTowerFClosed` 的 $\Omega_2$ |
| `KQ.Hs 1` | 第 1 站层号的**有限下标部分**的级顶的求值, 对 $N$ 取对角: 与 `LvRd.dω` 同量级 (第 $\omega$ 级的求值); 截断版第 1 站是有限级的 | `Hs1`, `rd-kept`, `tr₁` (形状定理); 外层世界 $(N,N)$ 只看见 $\le N$ 的下标 (`decH-fin′`, 测试 `t-dropω`); 无值定理 |
| `TD`, `TD∞` | 与 `Tkc`, `Tkc∞` 同量级 (`KcFold` 的读法 $\psi_0(\Omega_{\Omega_{\omega+1}})$, $\psi_0(\Omega_{\Omega_\omega})$, 粗界). **不读 ψ₀Λ** | 第 2 站起与截断版定义相等 (`HsSS`); 前两站多的是 $+1$ 与有限下标的对角 |
| `TH₁` | 外层世界 $(\omega,\omega_0)$ 只看见下标 $y\lhd_{[\omega]}\omega_0$ (有限与 $\omega_0$ 本身), 层号的可见部分是第 $\omega+2$ 级量级; 读回的求值落在 `Ht` | 无定理, 无测试 |

## 第一个障碍

1. **桥 (第 1 站, 定理 + 判断).** `KD` 的级是 `Lev`, 种类下标裸 (`levIdx`); 求值要数据树, 数据树的结点带当前世界的证据 (`sLH-adm`); 读回包要带世界的层 (`lvhIdx`). 保留下标的桥 ⇔ 裸判定 (`NegDnFoldAdm.Keep.keep→dec`), 外层世界含 $\omega$ 时是分离子 (`keepS₁-sep`). 本路只能在有限外层世界里判定 (判断: 对下标的构造子递归能证实的只有字面有限的项; 含极限的下标要判定函数相等). [判断] 出路是让塔的级本身带外层世界 (读回落在 `LvW a (B s)`, 下一站的层号以 `HB (LvW a c)` 为分量), 那时 `dnH` 直接适用, 不要桥; 这要一个新的塔, 不是 `KD`.
2. **第 2 站起的层 (定理 + 未写).** 层号的坐标是 `HB (Lev X_s)` (`coord-new`), `Ht` 的坐标只有 `A`, `H₀` (`ht-coords`). 要两种种类折叠 (`HtTowerFTree`, `HtTowerFFold`, 400+ 行, 对 `Ht` 专门写) 推广到以种类结构为参数的数据树 (`EvSysK` 的实例). 没有写.
3. **值.** 回灌输出含 $\Omega$-极限, `TpPort` 的单调不适用; 没有值定理.

报错原文: 无 (障碍是没写的东西与否定一路的定理).

## 四层行数表

`probes/Survey/scripts/dnfold/locslice_dnfold.py` (根表沿用 `kcfold/locslice_kcfold.py`, 同口径; 模块应用 `KQ`, `Rd a`, `Br N`, `EvAt L …` 的实参与模块内定义手工列为根).

| 层 | 无条件 `TD`: 本路新增 / 树侧全部 / 记号 | `TH₁`: 本路新增 / 树侧全部 / 记号 |
|---|---|---|
| 1 定义 | 32 / 575 / 0 | 16 / 271 / 0 |
| 2 折叠 (含读回包, 求值, 层号搬运, 桥) | 478 / 2519 / 0 | 275 / 1702 / 0 |
| 3 证书 | 518 / 2580 / 0 | 313 / 1746 / 0 |
| 4 律, 形状, 测试, 障碍 | 707 / 2966 / 0 | 无新增 |

对照 (同口径): `Tkc` 前 3 层树侧 1861, `TD` 2580 (+719: 两种种类折叠的求值 `Run` 与读回 `RdF` 进了闭包, 本路新增 518). 读回包 (`DnFoldRd`) 的结点解释记录把合法性证明作字段, 所以折叠层已经拉进证书的一部分.

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 / 脚手架 |
|---|---|---|
| `LvH`, `LyH`, `DnFoldRd` 的读回包 | `LvOm` 推广, KcFold 接手清单第 1 条 | 沿用; κH 一行与 κA 合成一条 (树侧) |
| 外层世界的关系 $a\le W$ (两个分量) | κH 的证据要高度分量也搬 | 树逼出 |
| `μ′` (层号搬进 `Ht`, 丢掉 `Oth`) | 数据树的层在 `Ht` (`ht-coords`) | 树逼出 (丢掉的部分是脚手架的代价) |
| `ωW`, `basebot` | `μ′` 合法 | 树逼出 |
| 桥 `F`, `G`, 有限外层世界 | `Lev` 与带世界的层的下标定义域不同 (`keep→dec`) | 脚手架 (有损); 判断: 这一层是 `KD` 的级用 `Lev` 带来的 |
| 对 $N$ 的部分和 | 不同 $N$ 的输出之间没有第一位置关系 | 脚手架 (同 `LvKtTower.cum`) |
| 第 0 站恒等, 第 2 站起截断版 | `Lev 1 = S₁`; 第 2 站起没有层 | 选择 |

归类 (判断): 攀爬, 提供信息. 提供信息的标志: `DnFoldRd` 的 $\Omega$-行对一切种类一条 (新用到的字段 `Bd↑ S₁`, `bdecLv (hs hz)`); `Lg-μ′` 用世界的翻译证合法 (新用到 `w0` 的 `basebot`); 障碍 1 指出桥是 `KD` 用 `Lev` 带来的, 与否定一路的 `keep→dec` 配对. 加深翻译的标志: 无新构造子读自基本列规则; 闭包定理没有专属前提; 不用 `Lab`.

## 审计

- **编译.** 九个模块删自己的 `.agdai` (精确模块名) 后从入口编译, 依赖用共享接口, `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/DnFold.lagda.md +RTS -M6G -RTS`, 退出码 0, 峰值常驻约 0.95G, 用时约 6 秒.
- **导入闭包** (`importclosure.py`, 不加 `--only`): 九个模块都退出码 0, 禁用表命中 0.
- **切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词; `--html` 由导入 `OCF.Align.DnFold` 与 `OCF.Align.Om1HnAccept` 的 scratch 模块生成, 退出码 0): `TD` 302/0/0, `Lg-TD` 307/0/0, `fghD` 320/0/0, `TD∞` 287/0/0, `dnD` 523/0/0, `dn₁` 486/0/0, `TH₁` 433/0/0, `Lg-TH₁` 437/0/0, `fghH₁` 451/0/0, `pk` 245/0/0, `Lg-μ′` 128/0/0, `F` 101/0/0, `toDn` 263/0/0, `tr₁` 584/0/0, `decH-fin′` 39/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用的实参: `TD` 的数与 `Tkc` 相同 (302), 实参 `dnD` 单列为根 (0).
- **禁用构造**: 九个文件里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, 函数外延, UIP 前提.

## 文件与行数

| 文件 | 代码行 / 总行 | 内容 |
|---|---|---|
| `DnFoldIf` | 76 / 148 | 接口 |
| `DnFoldEv` | 36 / 71 | 经求值的下降 |
| `DnFoldRd` | 233 / 321 | 层号在 `Ht` 的读回包 |
| `DnFoldDc` | 97 / 161 | `DnK (LvH a c)`, 读回进求值输入的形状, 闭项 `TH₁` |
| `DnFoldMu` | 116 / 169 | 第 1 站层号搬进 `Ht` |
| `DnFoldBr` | 125 / 169 | 部分种类映射, 有限外层世界的判定, 桥 |
| `DnFoldK` | 104 / 181 | `dnD`, 闭项 `TD`, 形状定理, 测试 |
| `DnFoldObs` | 49 / 75 | 障碍的类型事实, 判定的完全性 |
| `DnFold` | 10 / 本文件 | 入口 |
| `probes/Survey/scripts/dnfold/locslice_dnfold.py` | — | 行数脚本 |

## 接手清单

1. **带外层世界的塔.** 让读回落在 `LvW a (B s)` (`KcFoldTop.topW` 已有), 下一站的层号以 `HB (LvW a c)` 为分量 (一个新的 `nxt`), 第 1 站直接用 `dnH`, 不要桥. 先写接口, 检查外层世界 $a$ 从哪里来 (码世界, 世界塔 `WTower`; 否定一路 `mixW`, `seeExact-sep` 划出的界).
2. **第 2 站起的数据树.** 两种种类折叠推广到以种类结构为参数 (`EvSysK K`), 层在 `HB (step K)`; 读回包 `DnFoldRd` 的 $\Omega$-行已对一切种类一条, 要推广的是 `HtTowerFTree` 的 `Cut₀`/`Cut₁`, `Int`, `HtTowerFFold` 的 `KG`/`RunM`.
3. **值.** 先在 `TH₁` 上试 (单个求值, 不经塔): 与 `LvOmClosed.TΩ` 的比较, 或含 $\Omega$-极限输入的 `T⁺` 单调.
4. **忠实的陈述.** 接口 §5 是盲的 (`NegDnFoldBlind`); 要排除 `dnC` 一类, 写成值的界 (`ord`), 本路只有形状 (`Hs0-rd`, `Hs1`, `rd-kept`, `tr₁`).
