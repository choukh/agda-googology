# 读回包 + 第 ω+1 级折叠 (入口与判决): 构造一路

> 不含记号. 作者选定原话: "A3: 读回包 + 第 ω+1 级折叠". 本篇是构造一路; 否定一路前缀 `NegLvRd`, 共用接口 [LvRdIf](LvRdIf.lagda.md) (接口定稿 2026-11-05 14:28, 之后未改). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延; UIP 只以 Hedberg 定理的形式出现在码上 (码的相等可判定), 不作前提. 没有条件定理进闭项或证书; 唯一的条件定理在 `LvRdVal` (前提 `FstMono T⁺`, 第 4 层).
>
> **判决: HOLDS (构造), 值只有条件定理.**
>
> 1. **对坐标推广的读回包 (定理/构造, 无前提).** 读回拆成 "结点的解释" `NdI T L` 与 "对一切解释一条读回" `RG.rdG` ([LvRdPkg](LvRdPkg.lagda.md)); 解释由种类的嵌入 `Emb U T` 给出 ([LvRdEmb](LvRdEmb.lagda.md)), 合法由一步定理 `Lg-nodeA`, `Lg-nodeH` 给出, 对一切嵌入一条证明. 有限级 (`pkgF n`, 与 `FamFoldRead.pkg` 同递归), $\omega$ (`RdΩ`, 对角: 第 $n$ 支的结点用 `pkgF n`, 经并的第 $n+1$ 分量), $\omega+1$ (`RdΩ1`, 过第 $\omega$ 层的结点是新种类, 坐标 `HB Gω` 喂 `trω`) 是同一条读回的三个实例. 翻译 `trKg` 把 "过第 $m$ 层的结点证据" 作参数, 所以输出层可以是极限层.
> 2. **混合高度的下降 (构造).** `dω : Dn Gω`: `HB Gω` 经 `trω` 读成第 $\omega$ 层的树, 用两种种类折叠的求值 `Run` (层 $\Lambda=\omega$) 求到第 2 层, 经第 1 级读回落到 `Ht` ([LvRdFold](LvRdFold.lagda.md) §4). 不逐结点下降, 不判定级数.
> 3. **第 ω+1 级折叠, 读 ω 层的槽 (构造 + 形状定理).** 一条折叠 `GF k₀ L trO inc` 对一切码; 有限级 (`FF n`) 与第 $\omega+1$ 级 (`FΩ`, 码 `kω`, 层 `lyω`) 是它的两个实例. 世界链 `V` 把第 $n+1$ 级级顶折叠输出的读回逐级接到 `kω` 的槽上 (`ωslot-s`), 极限世界 `V∞` 的 `kω` 槽是链上各槽的 ℕ-极限; 第 $\omega+1$ 级折叠从 `V∞` 起, 新种类结点的第 0 项分支读这个槽 (`reads₀`, `fold-reads`). 计算 (有限测试档): 第 $\omega+1$ 级级顶的读回里沿格 $(1,j,3)$ 出现 ω 槽里第 $j$ 级的新种类结点, 种类原样 (`rd1`, `rd2`; 比较器有分辨力 `rd2≢1`).
> 4. **"层号由回灌给出" (形状定理, 在码与界上).** `lvShapeδ`: 外层界是部分和 $B_{s+1}=B_s\boxplus\sigma_0(H_s)$, $H_s$ 是第 $s+1$ 级级顶的回灌输出, $\sigma_0$ 是与站号无关的读法; 第 $s+1$ 站的码在新界之下, 目标是 $B_s$ (`lvlδ`). 常数读法的实例 `lvShape₁` 给出 $B_s=\mathrm{fin}\,s$ (`lvl₁`), 就是有限级折叠所在的坐标. **没有做到的**: 在 `lvShapeδ` 给出的坐标上折叠 (要一般高度处的读回包, 第一个障碍).
> 5. **码的弱化与 `code-≟` 相容 (定理).** `wkLaw` ([LvRdWk](LvRdWk.lagda.md)): `wk-tgt`, `wk-inj`, `wk-≟`, `wk-tr`; 关键引理 `cdB-tr` (复合路径的码是嫁接), `cdB-pB` (码 → 路径 → 码 恒等).
> 6. **瘦身 (切片).** 闭项 `T∞ω1` 的树侧前 3 层 1443 行 (含第 $\omega+1$ 级), 低于标杆 1513; 本路新增 411. 对照: `LvFbFold.T∞c` (只到 $\Omega_\omega$) 同口径 1518. 码的机器在闭项里只剩 `Cd`, `≟C`, `Pc`, `raise` ([LvRdWorld](LvRdWorld.lagda.md)).
> 7. **值 (b).** 定理: 输入一侧 `ΛF ⊏ Λω1` (严格的一切世界字面第一位置). 条件定理: 在 `FstMono T⁺` (`FstMono< T⁺`) 之下 `T∞F ≤ T∞ω1` (`asuc T∞F ≤ T∞ω1`). 没有无条件的值定理, 没有序数值验收.
>
> **对纲领与目标.** 纲领 1: 闭项是 `A` (布劳威尔树) 的元素, FGH 在树上算. 纲领 2: 无公理, 停机由检查器保证 (折叠对层的结构递归, 下降对级数递归). 纲领 3: 不触壁垒: 一切判定是码 (数据) 的相等或同一合法界之下的 `cmpB`; 不比较不同世界里的值, 没有全局三歧; 第 $\omega$ 层是对象层里的 ℕ-极限 `hl`. 纲领 4: 导入闭包与切片干净 (审计). 目标 "让树自足": 读回包的推广是对结构参数 (嵌入 `Emb`) 的一步定理, 新用到的字段是 `bd←`/`cv-vc` (结点的底) 与 `pr→`/`bd→`/`lw→`/`le→` (连续分支); 第 $\omega$ 级不需要新的读回定义, 只是解释的一个实例. 但第 $\omega$ 级的下降用了两种种类折叠的求值, 与有限级的下降 (逐级回灌) 不同法; 这一处的选择是判断.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvRd where

import OCF.Align.LvRdIf
import OCF.Align.LvRdEmb
import OCF.Align.LvRdPkg
import OCF.Align.LvRdWorld
import OCF.Align.LvRdFold
import OCF.Align.LvRdShape
import OCF.Align.LvRdWk
import OCF.Align.LvRdVal
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `Emb`, `idE`, `inj₁E`, `ιE`, `compE`, `lePE` | LvRdEmb | 种类的嵌入与它的实例 | 定义 |
| **`Lg-nodeA`**, **`Lg-nodeH`**, `fst-nodeA`, `fst-nodeH`, `nbAG-mono`, `nbHG-mono` | LvRdEmb | 对一切嵌入: 结点合法, 底是第一位置 | 定理 |
| `NdI`, **`RG.rdG`**, **`RG.fstG`**, **`RG.lgG`** | LvRdPkg | 对一切结点解释一条读回, 合法由形状给出 | 定义; 定理 |
| `trKg`, `TF.trNF`, `NF.ndF`, `NF.fsF`, `NF.lgF` | LvRdPkg | 任意层上的翻译; 过第 $j$ 层的结点经外层嵌入 | 定义; 定理 |
| `pkgF`, `RdF`, **`RdΩ`**, **`RdΩ1`**, `trω`, `trΩ1`, `pkgΩ` | LvRdPkg | 有限级, $\omega$, $\omega+1$ 的包; 接口 `PkgΩ` 的实例 | 构造 |
| `≟C`, `raise`, `mono`, `legal`, `at`, `off`, `RaiseI` | LvRdWorld | 码世界与接口 `Raise` 的实例 | 定理 |
| `GF.fold`, `GF.fold-Ω`, `GF.ch-s`, `GF.ch-lg`, `GF.ch-≤` | LvRdFold | 一条折叠对一切码 | 定义; 定理 |
| `FF`, `dnF`, `Hn`, `ΛF`, `lΛF` | LvRdFold | 有限级, 下降, 级顶, 对角 | 定义; 合法是定理 |
| **`dω`**, `Ev.evω` | LvRdFold | 混合高度降到 `Ht` | 定义; 合法是定理 |
| **`FΩ`**, `incΩ`, `trOω`, `dω1`, `Hω1` | LvRdFold | 第 $\omega+1$ 级折叠与下降 | 定义; 合法是定理 |
| `V`, `lgV`, `slotLim`, `V∞`, `lgV∞` | LvRdFold | ω 槽的世界链与极限世界 | 定义; 合法是定理 |
| **`T∞ω1`**, **`Lg-T∞ω1`**, **`fghω1`**; `T∞F` | LvRdFold | 闭项, FGH; 对照 | 定义; 合法是定理 |
| **`foldΩ1`**, **`shapeΩ1`** | LvRdShape | 接口 `FoldΩ1`, `ShapeΩ1` 的实例 | 定理 |
| **`ωslot-s`**, `fin-zero`, **`reads₀`**, **`fold-reads`** | LvRdShape | ω 槽被逐级升高, 有限码不动, 第 ω+1 级折叠读它 | 定理 |
| `lv1`, `lv2`, `rd1`, `rd2`, `rd2≢1` | LvRdShape | 具体格的计算 | 有限测试 (计算, `refl`) |
| `cdB-tr`, `cdB-pB`, `cdA-pA`, `graft-inj`, `graft-assoc`, `code-ext` | LvRdWk | 码与路径的结构引理 | 定理 |
| **`wk-code`**, `wk-tgt`, **`wk-inj`**, **`wk-≟`**, `wk-tr`, `wkLaw` | LvRdWk | 码的弱化与 `code-≟` 相容; 接口 `WkLaw` 的实例 | 定理 |
| `St.stages`, `B-fin`, `lvl₁`, `lvShape₁` | LvRdWk | 部分和界, 常数读法 | 定理 |
| `σ₀`, **`lvShapeδ`**, **`lvlδ`** | LvRdWk | 层号是此前回灌输出读法的部分和 | 定理 |
| `lay-fst`, **`lay-strict`**, `Hω1-hl` | LvRdVal | 输入一侧: `ΛF ⊏ Λω1` | 定理 |
| `val-mono`, `val-strict` | LvRdVal | 值一侧 | 条件 (`FstMono T⁺`, `FstMono< T⁺`) |

## 闭项与 FGH 的类型原文

```text
LvRdFold.T∞ω1    : A              -- T⁺ Λω1 lΛω1,  Λω1 = ΛF ⊞ Hω1
LvRdFold.Lg-T∞ω1 : Lg T∞ω1
LvRdFold.fghω1   : ℕ → ℕ          -- FL.FGH (ord T∞ω1)
LvRdFold.Hω1     : Ht             -- proj₁ dω1 (Ωtop Gω): 第 ω+1 级级顶, 折叠在 V∞ 里, 经 dω 落到 Ht
LvRdFold.ΛF      : Ht             -- hl cumF, cumF k = Hn 0 ⊞ … ⊞ Hn k
LvRdFold.T∞F     : A              -- 对照, T⁺ ΛF lΛF
```

全部无模块参数, 无前提.

## 前提实例

- `GF`: 模块参数是码, 层, 翻译, 增量 (数据), 不是命题; 实例 `FF n (dnF n)` 与 `FΩ`.
- `St a σ lσ`: 实例 `S₁` ($\sigma=1$), `Sδ` ($\sigma_s=\sigma_0(H_s)$).
- `val-mono`, `val-strict` 的前提 `FstMono T⁺`, `FstMono< T⁺`: 对 `T⁺` 未证也未否定 (`TpMono` PARTIAL, `NegTpMono` 未找到反例); 律的形状对别的 `F` 可满足 (`NegTpMonoBlind.rk-laws`, `TpMonoToy.toy`). 对 `T⁺` 的可满足性未知, 所以只是条件定理.

## 第一个障碍

1. **在 `lvShapeδ` 给出的坐标上折叠.** 层号 $B_s$ 是一般的可数高度 (可含 `A`-坐标的 $\Omega$-结点). 在坐标 $c$ 上折叠要 `Lev c` 的每个种类的读回与翻译; 本路的 `trKg` 把 "过第 $m$ 层的结点证据" `R : ∀ {W} → StH W (ly m) L″` 写成对一切世界成立, 有限层与 `lyω` 都没有 $\Omega$-结点, 所以成立. 否定一路 (主审转告, 未复核) 的 `no-unifΩ` 说 $\Omega$-极限层上非底分支没有对一切世界成立的层证据, 所以照这个参数形状推广到含 $\Omega$-结点的坐标会失败; 那里的层证据要带世界 (判断: 改成 `∀ W → (W 合法) → …` 并在 `trKg` 的 `ni` 处用当前世界的证据).
2. **第 ω+1 级以上.** `RdΩ1` 已写 (第 $\omega+1$ 层读回), 第 $\omega+2$ 级折叠是 `GF cH lyω1 …` 的又一个实例 (码 `cH` 的槽类型是 `Gω1`); 没有写, 下降要 `dω1`, 已有.
3. **值.** 没有无条件的值定理; 卡在 `T⁺` 的单调 (`TpMono` 的开放问题).

报错原文: 无 (障碍是没写的东西).

## 读法 (全部是判断)

| 闭项 | 读法 (判断) | 测到哪里 |
|---|---|---|
| `T∞F` | $\psi_0(\Omega_{\Omega_\omega})$, 与 `LvFbFold.T∞c` 同形 | 有限级的折叠与 `FKc` 同形 (旧种类 `trKg` = `trK` 的推广, 新种类同法回灌); 没有比较两者的定理 |
| `T∞ω1` | $\psi_0(\Omega_{\Omega_{\omega+1}})$ 量级 (粗界, 判断) | `ΛF ⊏ Λω1` (定理); `Hω1` 是第 $\omega+1$ 级级顶经一次回灌折叠与一次求值的下降; 槽里的有限级结点出现在它的读回里 (`rd1`, `rd2`). 上界: 层都在 `HB Gω1` 之内, 判断不超过 $\psi_0(\Omega_{\Omega_{\omega+2}})$ |

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `Emb` 与 `nodeA`, `nodeH` | `FamFoldLift.node` 的字段抽象 | 树逼出 (读第 $\omega$ 层时输出在并里, 种类要再嵌一次) |
| `NdI`, `RG.rdG` | `FamFoldRead.rdN` 把结点交给参数 | 树侧, 一般化 |
| `trKg` (层证据作参数) | `FamFoldRead.trK` 的 `ss Q` 写死后继层 | 树逼出 (极限层 `lyω` 只有 `sl`) |
| `Gω = sup ℕ Sk`, `lyω = hl (ly ∘ suc)` | `HtTowerTy.sup`, 层号 $1+c$ | 树侧 |
| `Cd`, `Pc`, 只放槽的世界 | `LvFbCode` 的码世界瘦身 | 脚手架 (序数值不需要; 去掉 `eqG` 搬运与合法性证明) |
| `GF` (一条折叠对一切码) | `LvFbFold.FKc` 的级数抽成码 | 沿用, 一般化 (回灌形状仍是 `RunM` 的三步) |
| `dω` (经求值的下降) | 两种种类折叠的 `Run` 对任意层有定义 | 树侧选择 (判断: 与有限级的逐级回灌不同法) |
| `V`, `V∞` (ω 槽的链与极限) | `LvFbFold.Vω` 加极限 | 树侧 |
| `wk`, `graft`, `cdB-tr`, `cdB-pB` | `LvFb` 接手清单第 3 条 | 树侧 (码的结构) |
| `St`, `σ₀`, `lvShapeδ` | W1 的部分和 + W2 的码 | 树侧; $\sigma_0$ 的选择是判断 |

归类 (判断): 提供信息. 读回包对坐标的推广写成了对结构参数 (嵌入) 的一步定理, 第 $\omega$, $\omega+1$ 级没有新的读回定义, 只是解释的实例; 第 $\omega$ 级的下降没有照有限级的逐级回灌翻译. 加深翻译的地方: `GF` 的回灌形状照搬 `FK`.

## 审计

- **编译**: 删本路 9 个模块的 `.agdai` (精确模块名 `OCF.Align.LvRd`, `LvRdIf`, `LvRdEmb`, `LvRdPkg`, `LvRdWorld`, `LvRdFold`, `LvRdShape`, `LvRdWk`, `LvRdVal`), 依赖用共享接口, 入口 `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/LvRd.lagda.md +RTS -M6G -RTS`; 结果见交回报告.
- **导入闭包** (`importclosure.py`, 不加 `--only`): `LvRd`, `LvRdFold`, `LvRdShape`, `LvRdWk`, `LvRdVal` 都退出码 0, 禁用表命中 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词): `LvRdFold:T∞ω1` 354/0/0, `Lg-T∞ω1` 358/0/0, `fghω1` 372/0/0, `Hω1` 332/0/0, `V∞` 310/0/0; `LvRdPkg:RdΩ1` 190/0/0; `LvRdShape:shapeΩ1` 325/0/0, `rd2` 326/0/0; `LvRdWk:wkLaw` 95/0/0, `lvlδ` 343/0/0; `LvRdVal:val-strict` 365/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用: `FF`, `FΩ` 打开 `GF`, `OG`, `Ev` 打开 `At`, 都写成 `open` 形式, `GF` 的定义另列为根.
- **分层行数** (`locslice_lvrd.py`): 层 1/2/3/4 树侧全部 328 / 1397 / 1443 / 1886, 本路新增 72 / 381 / 411 / 637, 记号模块 0. 层 4 含 `RdΩ1`, 律, 形状, 值. 上界 (定义所在五个文件的代码行全计): 本路 602, 树侧前 3 层不超过 1443 − 411 + 602 = 1634.
- **禁用构造**: 九个文件里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, `Funext`.

## 接手清单

1. 层证据带世界的 `trKg` (第一个障碍第 1 条), 再写对一般坐标 $c$ (`Lev c`) 的结点解释, 让 `lvShapeδ` 的坐标上有折叠.
2. 第 $\omega+2$ 级: `GF cH lyω1 trOω1 incΩ1` (旧种类: 新种类 `inj₂` 交给过第 $\omega$ 层的结点, 旧 `inj₁` 交给 `trOm`; 增量用 `RdΩ1`, `dω1`).
3. W1 的极限站: 否定一路的 `copy-code` 说沿路径的码弱化进极限有拷贝, `canon` (每个码沿出生那一站进极限) 有相干 (主审转告, 未复核); 本路的 `Stages` 只有后继站, 没有极限站.
4. 值: `FstMono T⁺` 落地后 `val-mono`, `val-strict` 成为无条件定理.
