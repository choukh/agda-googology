# Third: LHRec 的第三种组织 (入口)

> 不含记号. 构造一路 Third (配对否定一路 NegThird), 2026-11-06. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不用函数外延, 不用 UIP. 闭项, 证书, FGH 无模块参数. 不改任何已有文件.
>
> **任务** (作者本轮选定, 原话 "攻: LHRec 的第三种组织"; 说明 "构造+否定: 共享低层世界, 底对 ℕ 递归, 第 n+1 个底的分量高度取第 n 个底的值 ..., 写折叠与 ψ₀Λ 候选闭项").
>
> **先说结论.** 写出了对 $n$ 一切底一份的折叠, 与闭项 `TΛ : Cd`, 证书 `LgB-TΛ` (标准 `LgB`), FGH `fghΛ`. 分量高度确实取上一个底的值, 对角在 $\sup_n$ 上. 但**不把它报为 ψ₀Λ 的候选**: 为了让折叠是全函数, 本路付了三处损失 (§2), 定理 `ThirdVal.rk-⊲` 说每一站固定世界里高度的第一位置序保序地映进可数树. 判断: 读法在 RecB 的 ψ₀(Ω_{Ω·ω}) 附近, 没有下界定理, 也没有分开两者的测试. **真正的 ψ₀Λ 候选: 未找到** (§3 卡点).
>
> | 文件 | 内容 |
> |---|---|
> | [ThirdIf](ThirdIf.lagda.md) | 接口 (定稿 21:21): 一层世界, `LayerMv`, 塔 `Tw`, 位置 `Pos` |
> | [ThirdTw](ThirdTw.lagda.md) | 分类, 嵌入, `along`, 底 `Sb n`, 地板 `fl n`, $\Lambda$ 层的地板 `flΛ` |
> | [ThirdFold](ThirdFold.lagda.md) | 同底折叠 `Φ`, 结点一份 `nodeG`, 折叠与自己的路径合一, 洗法 `San` 作参数 |
> | [ThirdSan](ThirdSan.lagda.md) | 洗法实例 `Er` |
> | [ThirdPS](ThirdPS.lagda.md) | 对任一世界序的路径结构, 塔上的 `PSL`, 上抬 `lift` |
> | [ThirdPath](ThirdPath.lagda.md) | `PH-node` (结点一份), `PH-Φ` (同底折叠保路径, 一切 `Q`) |
> | [ThirdLeg](ThirdLeg.lagda.md) | 合法化 `legS`, 世界 `W c₀`, 代表坐标 `pkS` |
> | [ThirdX](ThirdX.lagda.md) | 跨底折叠 `ΦX`, `PH-ΦX↓` (一切 `Q`) |
> | [ThirdTm](ThirdTm.lagda.md) | 世界塔, 下降 `desc`, 闭项 `TN`, `TΛ`, 证书, FGH |
> | [ThirdVal](ThirdVal.lagda.md) | `rk-⊲`, `er-drop`, `leg-const`, `slot-zero` |
> | [ThirdCmp](ThirdCmp.lagda.md) | 有限测试 (验收文件, 不在闭包里) |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.Third where

open import OCF.Lean.CRwBase using (LgB)
open import OCF.Lean.ThirdTm public using (TΛ; LgB-TΛ; fghΛ; module Cn)
open import OCF.Lean.ThirdTw public using (Sb; fl; SΛ; flΛ)
open import OCF.Lean.ThirdVal public using (module Rk; module Stage; er-drop; leg-const; slot-zero)

cert : LgB TΛ
cert = LgB-TΛ
```

## §1 新的做法: 结点一份, 折叠与路径合一

RecB 的同底与跨底两个折叠各写一遍结点, 路径定理也各写一遍. 这里 `nodeG` 是结点的唯一定义 (留 / 同层 / 在上), `PH-node` 是它的唯一路径定理, 同底 `Φ` 与跨底 `ΦX` 都只给决定和递归. 塔的自己的路径 `Gd` 由折叠同时返回 (`GT t = Σ (HB (T t)) (Gd t)`): "同层" 与 "在上" 的链把上一步输出喂回坐标, 坐标要带路径, 所以路径定理不能写在折叠之后. 这一步是树侧的 (判断): 证据与值一起算.

指标种类对一切底一条规则: 当作第 $0$ 层的新种类与 $t$ 比较 (RecB 的 "$n\ge1$ 一律留" 消失了), 因为第 $n+1$ 个底的指标种类的坐标就是第 $n$ 个底的值.

## §2 三处损失 (定理与判断)

| 损失 | 为什么要付 | 定理 |
|---|---|---|
| **留下的新种类的坐标被洗** (`Er`): 穿过高度 $\Omega$-分量的结点换成 $0$ | 输出分支要在任意坐标有定义, 坐标里的种类可能没有 `Pos`; `NegThirdIf.pos-dec→LPO`, `no-wash` 排除判定 `Pos` 与保根种类的洗法 | `er-drop` |
| **合法化有损** (`legS`): 只有指标种类累加, 其余种类常值分支 | 累加到一切种类要对 `Tw` 的坐标递归, 未写 (不是否定) | `leg-const` |
| **世界固定**: 每一站 $w$ 不动, 只有指标分量的界是真的; 坐标的 $\Omega$-结点不留, 在代表坐标取分支 | `NegThirdPre.upd→WLPO` (条件: 函数外延) 排除按分量写回; 留下内层结点撞 `keep-req`, `no-lower-rule` | `slot-zero`, `rk-⊲` |

**`rk-⊲` 的读法 (判断).** 定理: 固定世界里 $a\lhd m$, $m$ 合法, 则 `rk a` $\lhd$ `rk m` (可数树). 这说明一站的塔里能比较的高度, 序型由一棵可数树控制. 原设计的力量来自低层世界随 $\Omega$-结点移动 (LHRec 实例 `J₁` 的 Kripke 式 $u'$), 那里同一个高度结点的不同坐标会在不同世界里被看到; 本路放弃了它. 所以我判断: 第 $n$ 个底的有效层号不超过上一个的有效层号加可数, `TΛ` 读法在 ψ₀(Ω_{Ω·ω}) 附近. 这是判断, 没有上界定理 (`rk-⊲` 只管序, 不管值), 也没有下界定理.

## §3 卡点: 真 ψ₀Λ 候选还差什么 (判断, 依据编译的否定)

留下的结点的分支对**任意**坐标要有定义, 而坐标 $e$ 穿过高度的 $\Omega$-分量时, 要比较的是 $e$ 与世界的界. 三条路都有编译的或判断的障碍:

1. **洗坐标.** 保根种类的洗法推出 LPO (`NegThirdIf.no-wash`); 判定 `Pos` 推出 LPO (`pos-dec→LPO`). 换分量要坐标反变的回缩, 判断: 没有.
2. **坐标带证据** (种类带世界戳, 坐标 $=$ (值, 世界 $V\ge$ 戳, 路径), 留下时换戳, 反变方向一致). 能绕开 1 与 `keep-req`, 但回灌要把折叠输出读成**合法**的高度, 而合法性 `LgB` 的单调要分支不读证据, 输出的分支读世界 (判断, 未编译).
3. **世界随结点移动.** 按分量写回推出 WLPO (条件: 函数外延); 整体抬升未否定, 也没有写.

编译错误原文: 无 (本路闭项一次编译通过, 卡点不是类型错误, 而是读法).

## §4 翻译账

- **新结点, 新字段.** 无新结点. 底的形状 (指标分量 + 第 $c$ 个分量) 来自 `LFReTy`, **记号引导, 如实**. 层号 $x_{n+1}$ 的读法受记号启发.
- **由树逼出.** (1) 折叠与路径合一: 由链的坐标要带路径. (2) 指标分量的旧种类不留: 由 `NegThirdPre.keep-req`, `no-lower-rule`. (3) 洗法换根种类: 由 `no-wash`. (4) 世界不写回: 由 `upd→WLPO` (条件).
- **累加, 如实.** 同 CRw, RecB: 后继 `mulG`, ℕ-极限 `ΣG`, 链 `chainG`, 对角 `yΛ` 都是部分和; 塔在 $\Omega$-高度的地板 `topT` 不累加 (不进闭项路径的 `tp`, `tp` 走 `bot`).
- **摆脱侧.** `nodeG`/`PH-node` 让结点规则对同底跨底一份; 指标种类的规则对一切底一份. `rk-⊲` 是树侧的否定工具: 不看记号就能说 "这一站的高度序是可数的".
- **攀爬侧.** 读法没有确认提升 (判断).

## §5 行数 (定义级切片)

脚本 `Survey/scripts/third/locslice_third.py` (口径同 `recb/locslice_recb.py`; 参数化模块手工列根, 不跟随 CRw 根上的 `open`). 2026-11-06 跑出 (主闭项 `TΛ`):

| 层 | Third (`TΛ`) | 对照 |
|---|---|---|
| 1 定义 | 248 | RecB 245 |
| 2 + 折叠, 实例, 闭项, FGH | 1047 | RecB 810 |
| 3 + 证书 | **1049** | RecB **817** (ψ₀(Ω_{Ω·ω}), 判断), FabLFReGen 1513 |

层 2 已含形状证书的 50 行 (`ThirdFold` 的模块根把 `Sh` 一组带进来, 同 RecB 的记账), 层 3 总数不受影响. 第 3 层逐模块: `CRwBase` 149, `ThirdFold` 147, `ThirdPath` 129, `ThirdLeg` 111, `ThirdX` 111, `ThirdTm` 96, `ThirdPS` 89, `ThirdSan` 78, `LHRecLeg` 60, `ThirdTw` 60, `ThirdIf` 11, `CRw` 8. 新写 832 行, 沿用 217 行. 闭包里 `Third*`, `CRw*`, `LHRec*` 之外的仓库模块: 0. 记号模块: 0. **1049 与 817 同读法 (判断), 所以本路没有比 RecB 便宜, 也没有确认的提升;** 跨读法的行数不作结论.

**逐件** (块本身的行数, 不含依赖):

| 件 | 行 |
|---|---|
| 接口用到的 `Tw`, `Pos` | 11 |
| 底与地板 | 29 |
| 嵌入 (`emb`, `along` 及位置) | 30 |
| 路径结构 (`ThirdPS`) | 85 |
| 同底折叠与决定 | 105 |
| 形状证书 | 50 |
| 洗法实例 | 76 |
| 下层路径 (`PH-node`, `PH-Φ`, 搬运) | 116 |
| 合法化 | 48 |
| 世界与代表坐标 | 57 |
| 跨底折叠与 `PH-ΦX↓` | 85 |
| 地板路径, 世界塔, 下降 | 61 |
| 闭项, FGH, 证书 | 24 |

路径与世界塔专用的块 (路径结构, 下层路径, 地板路径与世界塔) 约 262 行 (判断归类), RecB 是 322 行; 结点一份让 `PH-node` 取代了 RecB 的两份搬运. 接口的 `LayerMv` 没有实例化: 本路的回灌写在 `ThirdX` 里 (`sh₀`, `Adm₀`), 世界固定, 不需要低层世界的移动.

## §6 接手清单

1. 让世界随高度的 $\Omega$-结点移动而不写回分量: 全局抬升, 或把 $w$ 从 `Wd` 换成只含指标分量的世界.
2. `legS` 对一切种类累加: 对 `Tw` 的坐标递归, 用 `LHRecLeg.θK` 的办法.
3. `TΛ` 的值: 上界与下界都没有; 分开 `TN (1) 1` 与 `TN (1) 2` 的测试没有.
4. `flΛ` 没有用到闭项里 (闭项走 $\sup_n$ 下降); `Lg` 没有证.

## §7 结论 (按档)

- **[定理]** 接口 `ThirdIf`; 对一切 `U, w, Sn`: `Φ`, `Sh-Φ`; 对一切 `Q`: `PH-Φ`, `PH-ΦX↓`; 实例 `Er`; 闭项 `TΛ`, 证书 `LgB-TΛ`, `fghΛ`; `rk-⊲` (每一站), `er-drop`, `leg-const`, `slot-zero`.
- **[有限测试]** `ThirdCmp`.
- **[判断]** 读法在 ψ₀(Ω_{Ω·ω}) 附近; 坐标带证据断在合法性; §3 的穷尽.
- **[未找到]** 读 ψ₀Λ 的候选闭项. 这不是否定.
