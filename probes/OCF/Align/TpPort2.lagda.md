# `T⁺` 的 Ω-极限一步: 把单种类主线的 Ωᴴ 做法搬到两种种类 (入口)

> 不含记号. 作者选定原话: "值的一侧 + 第 4 层 B1 都派"; 本路是值的一侧, 单路. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`, 不改树、折叠、合法性, 不改已有文件.
>
> **判决: PARTIAL (编译过的定理).**
>
> 1. **`s-hΩ` 在最小坐标的分支不含 Ω-极限时成立 (定理, 两种种类都有).** `TpPort2Om.sΩ`: 对一切种类 $\kappa$ 与一切合法 $\mathrm{h\Omega}\,\kappa\,g$, `Free (g bot)` ⇒ $T^+(g(\mathrm{bot}))<T^+(\mathrm{h\Omega}\,\kappa\,g)$; 写成接口 `TpMonoIf.Steps.s-hΩ` 的形状是 `s-hΩF`. 前提只要最小坐标上的一个分支不含 Ω-极限 (不要求一切分支). 特例无前提: **`T0<Ω₂`** $T^+(0)<$ `T-Ω₂`, `T0<Ω₂²` $T^+(0)<$ `T-Ω₂²`, `T0<Z` ($Z=\mathrm{h\Omega}\,\kappa_A\,(\lambda\_.0)$).
> 2. **方法 (照 `MonoPort8`, `MonoPort9One`).** 回灌第 0 格在一个具体世界 $U$ 里展开 (新种类 $U=(1,\mathrm{rd}(0,z_1Y))$, 旧种类 $U=(V_0,0)$), 第一个节点在最小坐标上; 节点用单世界观测 (`TpPortNode.ΩdObs`, `nodeSelf`); 节点 (世界 $U$, 实例 $1\boxplus h$) 与较小一边 $T^+(g\,\mathrm{bot})$ (世界 $(1,0)$, 实例 $1\boxplus g\,\mathrm{bot}$) 之间只差世界与实例, 用不含回灌的两世界互模拟 (`TpPort2Sim`, `MonoPort8Sim` §1–§7 的脚本克隆; `TpPort2Cross.changeW`). 新种类多出的一件是读回: 第 0 格的路径定义地是 `hlim 0 hself`, 第 1 段的路径定义地是 `hLim (C.suc C.self) (hsuc hself)`, 节点就在 `hLim` 段 (旧种类的闭包 `KG`) **之前**, 所以不必展开 `KG`, `Walk₁` 只走后继一句. 这一点是检查器的计算 (`node≤cell` 通过), 回答了 `TpPort` 第一个障碍第 3 条留下的判断.
> 3. **接口律 (b) 严格版扩到最外是 Ω-极限的右边 (定理).** `TpPort2Tab.fst<⁺`: `FreeTop b` ⇒ ($a\sqsubset b$ ⇒ $T^+(a)<T^+(b)$), `FreeTop` 在后继与 ℕ-极限上同 `TpPortStep.fst<F`, 在 Ω-极限上是 "最小坐标的分支不含 Ω-极限". 非严格版 `fstLim` 只在最小世界里的路径不是 `hself` 时给出.
> 4. **去了条件的已有值结论**: `TpMonoTab.Tab.cells≤ 1` (`cells≤₁`, 另有严格版 `cells<₁₂`); `NegTpMonoWorld.no-valmono⁺` (前提 `Steps T⁺` 去掉: `no-valmonoT⁺`, $T^+$ 对通常的值序不单调). `TpMonoTab` 的 20 条里, 带 $n$ 的五族在个别 $n$ 上去了条件 (`TpPort` 六处, 本组 `cells≤ 1` 一处), 其余各条与各族的其余 $n$, 以及 `LvRdVal.val-mono`/`val-strict`, `LvTopVal.val-cum`/`val-cum<`/`val-lim`, `LvKtVal.val-cum`/`val-cum<`/`val-lim` 仍是条件定理; 本组的边界写成编译过的 `¬FT-*`, `¬Up-Λω1` (只说本组的 `FreeTop` 不覆盖).
>
> **对纲领与目标.** 纲领 1: 比较都是 `A` (布劳威尔树) 里的 `≤`, 输入是合法高度. 纲领 2: 无公理, 停机由检查器的结构检查给出 (生成的 `Run-E` 一族与折叠同一度量). 纲领 3: 互模拟两边世界各自独立但不比较世界, 单世界关系只读一个世界的目标, 没有全局比较; 律只对一切世界的字面第一位置陈述, 最小世界里过 Ω-分支只能走最小坐标 (界的证据把坐标定住). 纲领 4: 导入闭包与切片干净 (审计). 目标 "让树自足": 本路把已有的树侧证明搬到两种种类, 没有读记号, 没有新的树侧判据; 值定理是值的定理 (`TLRuleSpec._≤_`), **不是对参照树的序数值验收**.

## 文件

| 文件 | 来源 | 内容 |
|---|---|---|
| [TpPort2Sim](TpPort2Sim.lagda.md) | 生成, `MonoPort8Sim` §1–§7 | 两边世界独立的互模拟 `SimE`/`Re`, `sumE`, `ΩdE`, `IntE`, `Two` 与七条折叠引理 (`Run-E` …) |
| [TpPort2Cross](TpPort2Cross.lagda.md) | 手写 | `Cross`, **`changeW`**, `TΛ-at`; 否定 `no-κAE`, `no-κHE` |
| [TpPort2One](TpPort2One.lagda.md) | 手写 | `HasPfx`, `pfxRun`; 一个世界 `One`: `Pfx`, `gZ₀`; 一个节点 **`Node.low`** |
| [TpPort2Om](TpPort2Om.lagda.md) | 手写 | `drp≤`; `OmH` (新种类), `OmA` (旧种类) 的第 0 格第一个节点; **`sΩ`**, `s-hΩF`, `T0<Ω₂`, `T0<Ω₂²` |
| [TpPort2Tab](TpPort2Tab.lagda.md) | 手写 | **`fst<⁺`**, `fstLim`; `cells≤₁`, `cells<₁₂`, **`no-valmonoT⁺`**; 边界 `¬FT-*`, `¬F-ΛF`, `¬Up-Λω1` |

生成脚本: `probes/Survey/scripts/tpport2/mk_tpport2.py` (调用 `probes/Survey/scripts/tpport/tpgen.py` 的公共变换, 不改它); 从仓库根运行 `python3 probes/Survey/scripts/tpport2/mk_tpport2.py .` 逐字节重新生成 `TpPort2Sim`.

## 定理表 (无条件)

| 名字 | 文件 | 陈述 (读法) | 档 |
|---|---|---|---|
| `Run-E` 一族七条, `IntE`, `sumE`, `ΩdE` | TpPort2Sim | 两个实例、两个外层世界、一切目标对 (世界、位置、合法各自任意), 共有目标层不含 Ω-极限: 相关的输入折叠出相关的输出; 第 0 层相关的树和相等 | 定理 (生成) |
| **`changeW`** | TpPort2Cross | `Free Λ` ⇒ $T_\Lambda$ 与 $\Omega_\Lambda$ 在任意实例 $\Lambda'$、任意合法世界 $W\ge(0,0)$、任意位置上的折叠的和互相 $\le$ | 定理 |
| `no-κAE`, `no-κHE` | TpPort2Cross | 两种种类的 Ω-极限层的 $\Omega_L$ 与自己不在两世界互模拟里 (一切 $g$, 两个世界) | 否定, 定理 (只否定本关系覆盖 Ω-极限层) |
| `pfxRun` | TpPort2One | 左脊前缀的折叠的和不高于整体 | 定理 |
| `gZ₀`, `pZ₀` | TpPort2One | 字面的起始段 $Z_0=\mathrm{cv}\,X_1\,(Y_0\oplus\mathrm{Stp}\,Y_0)$ 自洽, 是自己的前缀 | 定理 |
| `TH≡`, `TA≡` | TpPort2Om | $T^+(\mathrm{h\Omega}\,\kappa\,g)=\lim(\mathrm{pt}\,b\,D)$, $D_n$ 是回灌第 $n$ 格 | 定理 (`refl`) |
| **`T0<Ω₂`**, `T0<Ω₂²`, `T0<Ω₂′` | TpPort2Om, TpPort2Tab | $T^+(0)<$ `T-Ω₂`; $T^+(0)<$ `T-Ω₂²` | 定理, 无前提 |
| `T0<Z` | TpPort2Tab | $T^+(0)<T^+(\mathrm{h\Omega}\,\kappa_A\,(\lambda\_.0))$ | 定理, 无前提 |
| **`cells≤₁`**, `cells<₁₂` | TpPort2Tab | $T^+(\mathrm{cells}\,1)\le$ (严格 $<$) $T^+(\mathrm{cells}\,2)$ | 定理, 无前提 |
| **`no-valmonoT⁺`** | TpPort2Tab | $\neg$ `ValMono T⁺ Lg-T⁺ _≤ᴴ_`: $T^+$ 对输入的通常值序不单调 | 否定, 定理, 无前提 (只否定对 `_≤ᴴ_` 的按值单调) |
| `ft-cells2`, `ns1` | TpPort2Tab | `FreeTop (cells 2)`; 最小世界里 `cells-st 1` 不是 `hself` | 定理 (计算) |
| `¬FT-Ω₂+1`, `¬FT-mul2`, `¬FT-fb₂1`, `¬FT-cells3`, `¬FT-Tᵀ+1`, `¬F-Hn0`, `¬F-ΛF`, `¬Up-Λω1` | TpPort2Tab | 这些输入不满足 `FreeTop` / `Free` | 定理 (只说本组不覆盖它们) |

## 定理表 (条件) 与前提实例

| 名字 | 前提 (Agda 类型) | 实例 / 不满足的例子 |
|---|---|---|
| `Node.low` | `R7.Good Y`, `Pfx Y`, `one ≤ β`, `Free (g′ c)` | `OmH`/`OmA` 的第一个节点 (`gN`, `pfx⊕ … pZ₀`, `sum≥ one …`, `free-top`) |
| **`sΩ`**, **`s-hΩF`** | `Free (g (bot S₁ κ))` | `Ω₂ᴴ` ($g=\mathrm{up}$, $g\,0=0$), `Ω₂²`, $Z$, `cells 2` (`ft-cells2`), 一切分支都是可数高度的 Ω-极限; 不满足: `mul 2` (`¬FT-mul2`, 分支 `mul 1` 含 Ω-极限), `Λs₂ 1` (`¬FT-fb₂1`) |
| `OmH.Fz.grow`, `OmA.Fz.grow` | `Free (g hz)` / `Free (g azero)` | 同上 |
| **`fst<⁺`** | `FreeTop b` | `TpPortStep.fst<F` 的一切实例 (`Free b` 的后继与 ℕ-极限), `Ω₂ᴴ`, `cells 2`; 不满足: 见 `¬FT-*` |
| `fstLim` | `FreeTop b`, `NotSelf p` | `cells≤₁` |

`TpMonoTab.Tab` 的 20 条, 状态 (前提 `Laws⁺`, 去条件的是对个别 $n$):

| 已去条件 | 来源 | 仍是条件 (第一个缺的步骤) |
|---|---|---|
| `mul<ω 0`, `fb₂<ω 0`, `cells<Tᵀ 0`, `cells<Tᵀ 1`, `cells≤ 0`, `x<Tᵁ 0` | `TpPortTab` | `Ω₂<Ω₂+1`, `Tᵀ<Tᵀ+1`: `s-hs` 在含 Ω-极限的 $h$ (`¬FT-Ω₂+1`, `¬FT-Tᵀ+1`) |
| **`cells≤ 1`** | 本组 `cells≤₁` | `Ω₂<Ω₂·2`: `SimInv` 与 `s-hΩ` 在分支含 Ω-极限 (`¬FT-mul2`) |
| | | `mul<ω n` ($n\ge1$), `Ω₂·2<Ω₂ω`, `cum<∞`, `lv<∞`, `Ω₂<∞`, `fb₂<ω n` ($n\ge1$), `cells<Tᵀ n` ($n\ge2$), `x<Tᵁ n` ($n\ge1$): `s-hl` 在含 Ω-极限的项 (`TpPortTab.¬F-*`) |
| | | `fb₂< n`: `s-hΩ` 在分支含 Ω-极限 (`¬FT-fb₂1`) |
| | | `cells≤ n` ($n\ge2$): `¬FT-cells3` |
| | | `lv≤cum`: (c) 左加平移; `Tᵁω≤`, `Tᵁ≤ω`, `t≤Ω₂`, `Ω₂≤t`, `Tᴰ₊≤`, `≤Tᴰ₊`: (a) 互模拟不变, 输入含 Ω-极限 |

`LvRdVal.val-mono`, `val-strict`: 右边 `Λω1 = ΛF ⊞ Hω1` 最外是 ℕ-极限, `LimF` 要第 0 项不含 Ω-极限, 而 `ΛF` 的第 0 项 `Hn 0` 含 (`¬Up-Λω1`). `LvTopVal`, `LvKtVal` 的 `val-cum`, `val-cum<`, `val-lim`: 对任一 `FoldAt` 陈述, 接口不给 `Hs 0` 不含 Ω-极限的证据; 要的同样是 `s-hl` 在含 Ω-极限的项 (判断; 截断的平凡实例 `foldTriv` 下 `Hs s = hz`, 那里前提可由 `TpPortStep.LimF` 给, 但那是值无意义的实例, 本组没有写).

## 第一个障碍

**Ω-极限层上的观测与换实例.** 剩下的条件定理要的一步都是下面三种之一, 共同点是**被折叠的层本身含 Ω-极限**:

1. `s-hΩ` 在分支含 Ω-极限 (`mul 2`, `Λs₂ 1`): 第一个节点的层 $1\boxplus g(\mathrm{bot})$ 含 Ω-极限. `changeW` 要 `Free` (两世界互模拟装不下 $\Omega_L$: `no-κAE`, `no-κHE`, 编译过); `Node.low` 的 `ΩdObs` 要 `Fin k` (单世界关系 `TpPortRel.Rel` 在 Ω-极限层上是 $\top$, 不传信息).
2. `s-hs`, `s-hl` 在含 Ω-极限的输入 (`Ω₂ᴴ`, `idx Ω₃`, `mul 1`, `cum 0`, `ΛF ⊞ …`): `TpMonoHs.ChangeHs` / `TpMonoHl.MonoHl` 要把实例 $L$ 与 $L+1$ (或 $1\boxplus f(n)$ 与 $1\boxplus\mathrm{hl}\,f$) 里**同一个** $\Omega_L$ 的折叠相比, $L$ 含 Ω-极限; 折叠里的 `RunM`/`RunK` 回灌出的格世界 ($\mathrm{rd}(\beta, z_1Y)$, $\mathrm{sum}(w, z\,Y)$) 由状态决定.
3. (a) `SimInv`, `LgIrr` 在含 Ω-极限的输入: 同 2, 两边实例同形但合法性证明不同 (`NegTpMonoSim.l₁≢l₂`).

判断 (没有编译过的否定, 写 "未走通"): 2 里的跨实例一步不是两世界互模拟能补的. 在 `changeW` 的设定里, 两边都从空状态起, $z_1Y$ 字面相同, 但格世界的高度分量从**各自世界的界**读回 ($\mathrm{rd}(0,\cdot)$ 对 $\mathrm{rd}(v_1,\cdot)$), `Walk₁` 走的坐标序列不同 (大世界一边先走 $0\to v_1$ 那一段). 所以 Ω-极限层上要的不是互模拟, 而是 "大世界一边的格以小世界一边的格为前缀" 一类的关系, 要对 `Walk₁`、`Cut₁`、`KG.Walk`、`κc₁` 的字面逐句写. 这与 `MonoPort9` §3 记下的单种类下一站 (`MonoPort7Lim.Suc.growS` 要 `Free Λ`) 同形. 没有报错原文: 本组没有对这些输入写出失败的尝试; 边界是编译过的 `¬FT-*`, `no-κAE`, `no-κHE`.

**更便宜的下一步 (判断, 未做).** 旧种类的 Ω-极限 (例如 `NegTpMonoWorld.Ωᴬ`) 的第 0 格整格都在同一个世界 $(V_0,0)$ 里走 (`KG.Walk`, 同单种类), 把 `MonoPort9One` §4 的路径归纳 (`WG`, `WRG`, `WL`) 搬到 `KG.Walk` 上, 就得到 "第 0 格走过的一切坐标 $c$: $T^+(g\,c)<T^+(\mathrm{h\Omega}\,\kappa_A\,g)$"; 新种类的第 0 格在 `hLim` 段里进旧种类的闭包, 闭包的格换世界 ($(V_\kappa, v_1)$), 要 `MonoPort8` §3 的 `GoodUp` 或 `MonoPort9Walk` 的 "在 $V_\omega$ 里重做". 这两步都不碰接口: 接口 (b) 只用最小坐标.

## 翻译账

本路不读记号. 新定义:

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `TpPort2Sim` (生成) | `MonoPort8Sim` §1–§7 的树侧证明, 只换世界与高度的类型、`Two` 的 `o₁`/`o₂`、`Int` 的 `NZ₁` 参数 | 树逼出 (已有, 搬运) |
| `changeW` 的两种种类写法 | `HtTowerFClosed.At.ΔΩ` 的字面 (起点世界 $(0,0)$, 第 1 层第一位置 `o`) | 树逼出 |
| `Node` 的界证据 `e` 作参数, 位置限于 `sL e hself` | 折叠在节点处用 `accK r`, 只有这一形状定义地化成 `accL k` (`ΩdObs` 要的); 两种种类的回灌第一个节点的界在 `κA` 是 `C.self`, 在 `κH` 是 `hself` | 树逼出 (第一次写成任意 $r$ 时编译不过, 报 `accL k != accK r`) |
| `OmH` 的显式项 (`qN = (C.self , hlim 1 (hLim (C.suc C.self) (hsuc hself)))`, `wN`, `YN`, `rgt`, `nth`) | `κc₁`, `κΔ₁`, `Walk₁` 的 `hl` 与 `hΩ` 两句, `rd-fst` 在 $z_1Y$ 上的计算; `rgt`/`nth` 只用来写出被比较的那一段 | 脚手架 (工程, 定义性化简的需要) |
| `OmA` 的显式项 (`qN = (C.lim 0 (C.suc C.self) , hself)`) | `KG.KR.κc`, `KG.Walk` 的字面 (同 `MonoPort8Om`) | 脚手架 (同上) |
| `FreeTop` | `SucF`, `LimF`, `sΩ` 三者的前提的并; 最小世界里过 Ω-分支只能走最小坐标 (`Bd` 在 $(0,0)$ 上的字面) | 树逼出 |
| `NotSelf`, `toP` | `hself` 一支要 Ω-极限输入上的 `LgIrr`, 本组没有 | 树逼出 |

归类: **提供信息** (判断). 没有新构造子或节点字段, 不改树、折叠、合法性, 没有 `Lab`, 没有记号, 没有序数值验收. 这一站新用到的字段: `nμ` 的回灌第 0 格 (`κc₁ … 0` 的 `rd`, `rd-fst`, `Sv₁`, `co₁`), `Walk₁` 的 `hl` 与 `hΩ` 两句 (只走到 `KG` 之前), 旧种类 `nκ` 的 `KG.KR.κc 0` 与 `KG.Walk`, `top⁺` 的 `⊞` 在 Ω-分支上逐点. 否定 (`no-κAE`, `no-κHE`, `¬FT-*`) 划出本组关系与 `FreeTop` 不能有的形状; `no-valmonoT⁺` 是关于 `T⁺` 本身的否定.

## 审计 (2026-11-05)

- **从头编译**: 删本组 6 个模块的 `.agdai` (逐个写精确模块名), 依赖用共享接口, `agda --library-file=<scratch>/libraries -i src -i probes --html --html-highlight=all --html-dir=<scratch>/tpport2/html probes/OCF/Align/TpPort2.lagda.md +RTS -M6G -RTS`, 退出码 0, 约 11 秒, 峰值常驻约 1.4G.
- **禁用构造**: 6 个文件的代码块里 `postulate`, 洞, `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY`, `trustMe`, `Funext`, K, `REWRITE` 都是 0; 选项都是 `--safe --without-K --lossy-unification`.
- **导入闭包** (`importclosure.py`, 不加 `--only`): 入口 87 个模块 (本地 75, 库 12), `TpPort2Sim` 24, `TpPort2Cross` 25, `TpPort2One` 37, `TpPort2Om` 52, `TpPort2Tab` 86; 禁用表命中都是 0. `TpPort2Tab` 的闭包大, 是因为它导入 `TpMonoTab` 用到的闭项 (`HtTowerNFb`, `FamFoldOne`, `UipFbClosed`, `FamFoldAll`, `LvRdFold`) 与 `NegTpMonoWorld`, 都过了禁用表.
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词): `sΩ` 614/0/0, `s-hΩF` 615/0/0, `T0<Ω₂` 637/0/0, `T0<Ω₂²` 637/0/0, `changeW` 254/0/0, `no-κHE` 83/0/0, `fst<⁺` 766/0/0, `cells≤₁` 870/0/0, `cells<₁₂` 868/0/0, `no-valmonoT⁺` 630/0/0, `¬Up-Λω1` 312/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用 (`open One …`, `module KG = P.KG …`), 导入闭包覆盖. 只保证不引用, 不说明定义没有受记号启发.
- **生成文件**: 脚本重跑, `TpPort2Sim` 的 md5 与仓库里的逐字节相同.
- **代码行** (agda 块里非空非注释) / 文件行: 生成 `Sim` 245/304; 手写 `Cross` 41/72, `One` 115/182, `Om` 156/263, `Tab` 93/171, 入口 7/约 110; 手写合计 412. 脚本 `mk_tpport2.py` 87 行.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpPort2 where

import OCF.Align.TpPort2Sim
import OCF.Align.TpPort2Cross
import OCF.Align.TpPort2One
import OCF.Align.TpPort2Om
import OCF.Align.TpPort2Tab
```
