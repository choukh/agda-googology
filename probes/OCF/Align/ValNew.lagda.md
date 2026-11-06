# 新闭项的值 (入口与判决): `TΛ`, `TΛ₂`, `TΛn` 之间的 `ord` 比较

> 不含记号. 作者选定原话: "值: 新闭项的 ord 比较". 本路 (前缀 `ValNew`, 单路) 接 [ValTK](ValTK.lagda.md) (那里没有无条件比较). 第 4 层: 只新增关系与定理, 不改树, 折叠, 合法性, 不改已有文件. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延 (连前提也没有), 不用 UIP 作前提.
>
> **判决: HOLDS (对 `TΛ` 一族); 跨折叠的闭项 (`TK`, `TN`, `TS`) 没有比较.**
>
> - **无条件定理.** `ValNewStr.TΛn< : ∀ n → asuc (TΛn n) ≤ TΛn (suc n)`, 特例 `TΛ<TΛ₂ : asuc TΛ ≤ TΛ₂`; `ValNewStr.stage< : ∀ n → asuc (col collL (up (tw n)) _) ≤ TΛ` (塔的每一站严格低于对角); `ValNewTw.TΛn-mono : TΛn n ≤ TΛn (k + n)`. 闭项都来自 [FabLFReGen](FabLFReGen.lagda.md), 比较是 `A` 上通常的 `≤` (`TLRuleSpec._≤_`), `ordL` 按构造子把它搬到 `Ordᶜ`.
> - **一步定理 (对一切满足 `NI` 的层, 合法性证明任意).** 记 $T(h)=$ `col collL h lh`. 后继: $T(h)<T(h+1)$ (`HsS.hs-strict`); 极限: $T(f\,n)<T(\mathrm{hl}\,f)$ 对一切 $n$ (`HlS.hl-strict`); 旧种类的 $\Omega$: $T(g\,\bot)<T(\mathrm{hΩ}\,(\mathrm{inj}_1\kappa)\,g)$ (`HΩ.Ω-strict-bot`); 合法性证明无关: $T(h,l)\le T(h,l')$ (`Irr.lg-irr`); 公共下界 $T(0)\le T(h)$ (`base≤`). 前提 `NI h`: 层里没有 `step SL` 的新种类的 $\Omega$-结点; `up` 的像都满足 (`NI-up`), 所以一切 `TΛ` 族的层都满足.
> - **方法 (一条定理管两件事).** 关系 `Mo` = [TpPortSim](TpPortSim.lagda.md) 的互模拟 (两边的结点证据可以不同) + 旧种类闭包结点的同形 (`mc`) + "右边多出一段" (`mz`, `mr`, `me`, `ml0`). 一般折叠 [GenFoldRun](GenFoldRun.lagda.md) 在**两个实例** (最高层不同, 合法性证明不同) 之间保持它 (`ValNewRun.Two.Run-R`), 前提是一切旧种类的 A-回灌有损 (`lossy`, `GL` 有实例 `λ κ → refl`) 与 `NI Λ₁`. 于是 [TpMono](TpMono.lagda.md) 拆开的两条 "跨实例" (`ChangeHs`) 与 "状态变大" (`MonoStepHs`, `MonoHl`) 在这里是同一条 `cross`, **对含旧种类 $\Omega$-极限的层也成立** (TpPort 只到不含 $\Omega$-极限的层, 因为那里的折叠有回灌与前缀行走).
>
> **对纲领与目标.** 纲领 1: 一切比较在布劳威尔树 `A` 上. 纲领 2: 无公理, 停机由检查器 (对关系的推导与 `AccY` 结构递归). 纲领 3: 律只比较同一层、同一世界上的两棵数据树; 节点 "保留还是上升" 两个实例一致是一条定理 (`rk-valid`: 上升当且仅当没有结点证据), 不比较两个 `cmpB` 的结果; 闭包结点两边取同一个世界的分支; 没有异质世界 (判断: 不碰壁垒). 纲领 4: 导入闭包干净 (审计). **目标 "让树自足"**: 这是第一批对 `TΛ` 族的无条件值定理, 关系的每个构造子都读自折叠的字面 (`⊕` 把输出接在状态右边, `Stp` 是 $\omega$ 份, `Rpt` 的第 0 项), 不读记号. 它给出一个树侧判据的雏形: 对没有回灌的坍缩, 值沿层的后继与极限严格增, 且不依赖合法性证明. 它**没有**说值有多大 (见 "界与读法"); 对有回灌的折叠 (`TK`, `TN`, `TS`, 以及 C6 要的那种回灌) 它不适用.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValNew where

import OCF.Align.ValNewRel
import OCF.Align.ValNewRun
import OCF.Align.ValNewTw
import OCF.Align.ValNewStr
import OCF.Align.ValNewOm
```

## 定理表

| 名字 | 文件 | 陈述 (读法) | 档 |
|---|---|---|---|
| `NI`, `NI-⊲`, `NI-up`, `NI-⊞` | Rel §1 | 层里没有新种类的 $\Omega$-结点; 沿第一位置向下封闭; `up` 的像与 `⊞` 保持 | 定义; 定理 |
| `Mo`, `RelA`, `Rl`, `irr` | Rel §2 | 关系 (见上); 对可达证明无关 | 定义; 定理 |
| **`sum-M`**, `pt-M`, `drp-M`, `sum≥`, `pt≥` | Rel §3 | 第 0 层: `RelA a x y → b ≤ b′ → sum b x ≤ sum b′ y`; `drp` 保持 | 定理 |
| `Ωd-M`, `conv`, `Pre-M`, **`Int-M`** | Rel §4, §5 | `NI t` ⇒ $\Omega_t$ 与自己相关; 输入改写保持关系 | 定理 |
| `Val.rk-valid`, `Two.rkT-rel` | Run §1, §2 | 每个实例里 "上升" 只在没有结点证据时出现; 两个实例的决定一致 | 定理 |
| **`Two.Run-R`** (与 `Rpt-R`, `RunNi-R`, `Ai-R`, `Chn-R`, `RKi-R`, `BNi-R`, `RKc-R`, `RKk-R`, `RKa-R`) | Run §3 | 前提 `lossy`, `NI Λ₁`: 相关的数据/前缀/状态/动作 ⇒ 两个实例的折叠在共有目标上输出相关 | 定理 (模块参数 `lossy` 对 `GL` 有实例) |
| **`Two.cross`** | Run §4 | 同上, 读到第 0 层: `sum b (…实例 1…) ≤ sum b′ (…实例 2…)` | 定理 (同上) |
| `Hs.hs-unfold`, `Hs.T≤X`, **`Hs.hs-step`** | Tw §1 | `NI h` ⇒ `col collL h lh ≤ col collL (hs h) lh′` | 定理 |
| `Hl.T≡`, `Hl.hl-unfold`, `Hl.stR`, **`Hl.hl-step`** | Tw §2 | `NI (hl f)` ⇒ `col collL (f n) lfn ≤ col collL (hl f) lf` | 定理 |
| **`Irr.lg-irr`** | Tw §3 | `NI h` ⇒ `col collL h lh ≤ col collL h lh′` (两个合法性证明, 两向) | 定理 |
| **`TΛn≤`**, `TΛ≤TΛ₂`, **`stage≤`**, `TΛn-mono` | Tw §3 | `TΛn n ≤ TΛn (suc n)`; `TΛ ≤ TΛ₂`; `col collL (up (tw n)) _ ≤ TΛ`; `TΛn n ≤ TΛn (k + n)` | **定理, 无前提** |
| `n1≼Ωd` | Str | $1\preceq\Omega_t$ 对一切层 $t$ | 定理 |
| `HsS.c1`, `HsS.i1`, **`HsS.hs-strict`** | Str §1 | `NI h` ⇒ `asuc (col collL h lh) ≤ col collL (hs h) lh′` | 定理 |
| `HlS.c0`, `HlS.i1`, **`HlS.hl-strict`** | Str §2 | `NI (hl f)` ⇒ `asuc (col collL (f n) lfn) ≤ col collL (hl f) lf` | 定理 |
| **`TΛn<`**, **`TΛ<TΛ₂`**, **`stage<`** | Str §3 | `asuc (TΛn n) ≤ TΛn (suc n)`; `asuc TΛ ≤ TΛ₂`; `asuc (col collL (up (tw n)) _) ≤ TΛ` | **定理, 无前提** |
| `drp≤` | Om §1 | `b ≤ b′ → sum b x ≤ sum b′ (drp x)` | 定理 |
| `HΩ.Ω-unfold`, `HΩ.Ω-step`, **`HΩ.Ω-strict`**, **`HΩ.Ω-strict-bot`** | Om §2 | `NI (hΩ (inj₁ κ) g)` ⇒ `asuc (col collL (g c₀) _) ≤ col collL (hΩ (inj₁ κ) g) lh`, $c_0$ = 基世界的顶; 经 `top-base` 换成 `g (bot SL κ)` | 定理 |
| **`base≤`** | Om §3 | 合法且 `NI` 的 $h$: `col collL hz tt ≤ col collL h lh` (结构归纳, 三步) | 定理 |

## 前提与实例

- `ValNewRun` 的模块参数 `lossy : ∀ κ → fbA G κ ≡ inj₂ tt`: 对 `GL` 的实例是 `λ κ → refl` (`ValNewTw.R`). 对 `NewTwrColl.GΛ` (`TN`), `KindLvTw` 的 `GΛ` 加级回灌 (`TK`), `StratTwTw` (`TS`) 没有实例: 那些折叠有回灌.
- `Two` 的 `NI Λ₁`; `Hs`, `Hl`, `Irr` 的 `NI h`, `NI (hl f)`: 闭项里的实例是 `NI-up (Λn n)`, `NI-up Λ` (编译过). 不满足的层: 含 `hΩ (inj₂ _) _` 的层 (`step SL` 的新种类, 坐标 `HB SL`), 例如 `hΩ (inj₂ tt) (λ c → hz)`; `TΛ` 族的层都不含.
- 关系里 "右边多出一段" 的四个构造子都有实际用到的实例 (`Hs.hx`, `Hl.stR`, `HsS.c1`).

## 第一个障碍 (下一步的)

**有回灌的折叠.** 关系 `Mo` 没有新种类闭包结点 (`nc (inj₂ _)`) 的构造子, `Run-R` 的旧种类闭包结点只在第 0 层目标有损时成立 (`RKa-R` 要 `s ≡ inj₂ tt`). 有回灌时 (新种类的 `κc₁` 读 `rd₁`, 旧种类的 `κcA` 读 `sum`), 两边输出只相关不相等, 回灌出的两个世界不同, 要异质世界的关系 ([ValTK](ValTK.lagda.md) 的第一个障碍, `HtCrossV` 的第一个障碍同形). 本路没有对它写尝试, 没有报错原文, 没有否定定理: **未走通, 也未尝试**. 判断: `Mo` 加一条 "两个世界带 $W\le W'$ 证据, 右边的世界更大" 的变体, 只要折叠对世界单调, 也许能覆盖 `κc₁` (回灌的读数右边更大 ⇒ 世界右边更大); 这正是 `GoodUp` 卡住的 "跨世界的值单调", 本路不在同一处硬攻.

**跨折叠的闭项** (`TΛ` 对 `TK`, `TN`, `TS`): 种类结构不同 (`SL` 对 `KΛc`, `U`), 数据类型不同, 而且后三者有回灌. 要先有不同种类结构之间的折叠模拟; 没有做.

## 界与读法 (全部是判断)

| 对象 | 界 (判断, 粗) | 依据, 测到哪里 |
|---|---|---|
| `TΛ` | 读 $\psi_0(\Omega_2)$ 量级 (乘以小因子), 低于 $\psi_0(\Omega_3)$ | `GL` 的一切旧种类有损 (`fb-lossy`), 基世界里一切种类的顶是底 (`top-base`); 折叠里没有新种类结点 (层满足 `NI`), 世界不变 (判断, 没有写成对折叠全程的不变式), 所以层的 $\Omega$-结点只在底坐标上取分支. 在底坐标上 $t_n$ ($n\ge1$) 的影子是 $1$, 层 $1\boxplus\mathrm{up}\,\Lambda$ 的影子是 $(1,2,2,\ldots)$ 的 ℕ-极限 |
| `TΛ₂` | 读 $\psi_0(\Omega_\omega)$ 量级 | 同上的影子: $\Lambda_2=\mathrm{fix}(\Lambda+1)$, $\mathrm{it}_m$ 的影子约 $2+m$ |
| `TΛn n` ($n\ge1$) | 读 $\psi_0(\Omega_{\omega\cdot n})$ 量级 | 同上: $\Lambda_{n+1}=\mathrm{fix}(\Lambda_n+1)$ 的影子多一个 $\omega$ |
| $T(0)$ = `col collL hz tt` (`base≤` 的公共下界) | 读 $\psi_0(\Omega_1)$ 量级 | 层 $1\boxplus0=1$, 按此前各路 "层 $x$ 的坍缩读 $\psi_0(\Omega_x)$" 的读法; 没有对参照树的定理 |
| 与 `TK`, `TN` | 不比较 | `ValTK` 的读法 (三者在 $\psi_0(\Omega_2)$ 与 $\psi_0(\Omega_\Omega)$ 之间) 与上面不矛盾; 没有定理 |

这些读法说明 `TΛ` 族**远低于** $\psi_0(\Lambda)$ (与 `FabLFReGen` 的判断一致), 原因是 C6 (回灌有损); 本路的定理只说顺序, 不说大小 (手册 §3.3: 本路的严格是 "比前一项多一个后继" 这一档, 不是对参照树的界). 上面的影子论证若写成定理, 要一条 "基世界里的折叠只看底坐标" 的不变式与反方向的关系 (左边更大), 本路没有做.

## 翻译账

本路不读记号.

| 新增 | 来源 | 读自记号 / 树逼出 / 脚手架 |
|---|---|---|
| `Mo` 的同形部分 (`m1`, `m⨾`, `ml`, `mi`, `mw`) | `TpPortSim.SimD` (已有) | 树逼出 (搬运) |
| `mc` | `GenFoldRun.RKc` 的旧种类两行 (有损 / 保留) | 树逼出 |
| `mz`, `mr`, `me`, `ml0` | 状态 `⊕` 把输出接在右边, `Stp` 是 $\omega$ 份, `Rpt` 的第 0 项就是原状态 | 树逼出 |
| `NI` | 关系没有新种类回灌的构造子; `up` 的像只含旧种类 | 树逼出 (划出定理的适用范围) |
| `lossy` | `RKa` 的有损一行 | 树逼出 (适用范围) |
| `Kn1` (严格用的常数动作) | 同一实例里 "左边更小" 的动作 | 验收工具 (第 4 层), 不进成品 |

归类 (判断): **提供信息**. 没有新构造子或节点字段, 不改树、折叠、合法性, 没有 `Lab`, 没有记号, 没有序数值验收. 这一站新用到的字段: `GenFoldRun` 的 `⊕⟨_⟩`, `Stp`, `Rpt` 第 0 项, `RKc`/`RKa`/`RKk` 的旧种类行, `rkT` 只在没有结点证据时上升. 信息是: (1) 对没有回灌的一般折叠, "跨实例" 与 "状态单调" 是同一条关系的保持, 含旧种类 $\Omega$-极限也成立, 判断: `TpMono` 的第一个障碍 (`ChangeHs` 在 $h\ge1$) 的根子是回灌 (与前缀行走), 不是 $\Omega$-极限本身 (那里是另一份折叠 `HtTowerFFold`, 本路没有在它上面证); (2) `TΛ` 族的值严格单调, 但读法 (判断) 显示 C6 使它们停在低处. 第 4 层没有逼出改前 3 层.

## 审计 (2026-11-05)

- **从头编译.** 删本路自己的 `.agdai` (逐个写精确路径: `probes/_build/2.8.0.2/agda/OCF/Align/ValNewRel.agdai`, `ValNewRun`, `ValNewTw`, `ValNewStr`, `ValNewOm`, `ValNew`), 依赖用共享接口, 从仓库根: `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/ValNew.lagda.md +RTS -M6G -RTS`, 退出码见汇报 (末次复核 0). 单个模块各 4 到 6 秒, 峰值常驻约 1.0G 到 1.4G.
- **禁用构造.** 六个文件的代码块里 `postulate`, 洞, `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY`, `trustMe`, `Funext`, `REWRITE`, `--with-K`, `--cubical` 都是 0; 选项都是 `--safe --without-K --lossy-unification`. 停机由结构检查给出 (`RelA`, `irr`, `sum-M`, `drp-M`, `Int-M`, `Run-R` 一族对关系的推导与 `AccY`; `stR`, `c0` 对 ℕ; `base≤` 对层).
- **导入闭包** (`importclosure.py OCF.Align.ValNew`, 不加 `--only`): 退出码 0, 闭包 100 个模块 (本地 87, 库 13), 禁用表命中 0. 闭包经 `FabLFReGen`, `GenFoldInst` 等带进的模块都是上游已有的.
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词): `ValNewStr:TΛn<` 399/0/0, `ValNewStr:TΛ<TΛ₂` 404/0/0, `ValNewStr:stage<` 374/0/0, `ValNewTw:TΛn≤` 386/0/0, `ValNewRun:cross` 230/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用 (`module R = …`, `module TW = R.Two …`), 导入闭包覆盖. 只保证不引用, 不说明定义没有受记号启发.
- **代码行** (agda 块里非空非注释) / 文件行: `ValNewRel` 159/223, `ValNewRun` 218/290, `ValNewTw` 165/266, `ValNewStr` 85/136, `ValNewOm` 127/194, 入口 7/约 110; 合计代码 761.
- **生成文件**: 无 (全部手写; `Run-R` 一族的证明按 `TpPortRun` 的形状手写改写, 没有用脚本, 没有建 `probes/Survey/scripts/valnew/`).

## 文件

| 文件 | 内容 |
|---|---|
| `ValNewRel` | `NI`; 关系 `Mo`; 第 0 层 `sum-M`; `Ωd-M`; `Int-M` |
| `ValNewRun` | 两个实例的一般折叠保持 `Mo` (`Run-R`), `cross` |
| `ValNewTw` | 后继一步, 极限一步, 合法性证明无关, `TΛ` 族的 $\le$ |
| `ValNewStr` | 严格: `hs-strict`, `hl-strict`, `TΛn<`, `TΛ<TΛ₂`, `stage<` |
| `ValNewOm` | $\Omega$-一步 (`Ω-strict`, `Ω-strict-bot`), 公共下界 `base≤` |
| `ValNew` | 入口 (本文件) |

## 接手清单

1. **回灌.** 把 `Mo` 推广到两个世界 $W\le W'$ (右边更大), 先只对新种类的 `κc₁` (读回 `rd₁` 右边更大 ⇒ 新界右边更大, 要 `rd₁` 对关系单调). 先把接口写成记录, 配对派否定一路, 对准 "第 $\ge1$ 层目标上的输出关系在升高的世界里保持" (`GoodUp` 的位置). 有了它, `ValTK` 的 `Dom lv₀ lvΛ` 与 `TK₀ ≤ TK` 可以重做.
2. **上界的不变式.** "`GL` 的坍缩里世界不变, 层的 $\Omega$-结点只在底坐标上取分支" 写成对折叠全程的不变式; 再写反方向的关系 (左边更大), 把 $T(\mathrm{hΩ}\,\kappa\,g)$ 夹在 $T(g\,\bot)$ 的常数倍之间. 这是 "界与读法" 一节的第一环.
3. **第一位置单调.** 三步 (`hs-strict`, `hl-strict`, `Ω-strict-bot`) 已有; 把它们按路径归纳合成 "$a\lhd b$ (路径上的 $\Omega$-段只走底坐标) ⇒ $T(a)<T(b)$", 即 `TpMonoIf` (b) 在基世界的版本. 一切世界的版本要 $T(g\,c)\le T(g\,c')$ 对 $c\lhd c'$, 而折叠只看底坐标 (判断), 所以那一版对 `GL` 的坍缩多半只能以 "两边相等" 的形式成立; 没有做.
4. **跨折叠.** `TΛ` 与 `TN`/`TK`/`TS` 要不同种类结构之间的折叠模拟; 先判断是否值得 (那三者的读法与 `TΛ` 不同档的证据只有判断).
