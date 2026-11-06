# `T⁺` 的单调, 用 `MonoPort` 的手法搬到两种种类 (入口)

> 不含记号. 作者选定原话: "A2: 把 MonoPort 手法搬到两种种类". 单路. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`, 不改树、折叠、合法性, 不改已有文件.
>
> **判决: PARTIAL (编译过的定理).**
>
> 1. **不含 Ω-极限的输入上, `TpMonoIf` 的三个归结前提都证出来了 (定理).** `SucF.change : ChangeHs h`, `SucF.mono : MonoStepHs h` (`Free h`); `LimF.M.mono : MonoHl f lf n` (只要 $f(0),\dots,f(n)$ 不含 Ω-极限, `Upto f n`). 经 `TpMonoHs.hs-reduce`, `TpMonoHl.hl-reduce`: **`SucF.grow`** $T^+(h)<T^+(h+1)$, **`LimF.grow`** $T^+(f\,n)<T^+(\mathrm{hl}\,f)$.
> 2. **接口的律 (b) 在右边不含 Ω-极限时成立 (定理)**: `fstF`, `fst<F` (一切世界的 (严格) 字面第一位置 ⇒ $\le$ / $<$), 合法性证明无关 `irrF`. 这是 `Laws⁺` 在 Ω-自由部分上的 (b) 与 `LgIrr`; (a) 互模拟不变、(c) 左加平移、以及含 Ω-极限的输入都没有证.
> 3. **第一批无条件的闭项值定理** (`TpPortTab`): 一切可数高度沿 $\ll$ 严格增长 (`grow≪`; 特例 $n$, $\omega$, $\omega+1$, $\omega\cdot2$); `TpMonoTab` 的条件定理在前几项上去掉条件的六条: `mul<ω₀` ($T^+(0)<$ `T-Ω₂ω`), `fb₂<ω₀` (`T-fb₂ 0 <` `T-fb₂ω`), `cells<Tᵀ₀`, `cells<Tᵀ₁` ($T^+(\mathrm{cells}\,0), T^+(\mathrm{cells}\,1)<$ `Tᵀ`), `cells≤₀`, `x<Tᵁ₀` ($T^+(x_0)<$ `Tᵁ`). 其余的较小一边含 Ω-极限 (`¬F-Ω₂`, `¬F-mul1`, `¬F-H0`, `¬F-cum0`, `¬F-Λs₂1`, `¬F-cell₂`, `¬F-x1`, 编译过), 本组不覆盖, 仍是条件定理; `Tlv n`, `T∞` 都在其中 (`cum 0 = H 0` 含 Ω-极限).
> 4. **方法**: 单种类主线的 `HtCrossVSim`/`HtCrossVRun` (不含回灌的互模拟, 换实例) 与 `MonoPort3Gen`, `MonoPort5Rel` (`RelM`), `MonoPort5Chn`, `MonoPort6Zero`, `MonoPort7Rel`/`Int`/`Lay`/`Snd`/`Node` (单世界关系, `ΩdObs`, `HAKb`, `nodeSelf`) 用脚本克隆到两种种类的折叠 `HtTowerFFold` 上 (12 个生成文件, 证明逐句不变), 手写的只有三个归结 (`TpPortStep`), 闭项 (`TpPortTab`), 边界 (`TpPortNeg`). 克隆一次编译通过: 两种种类的折叠在不含 `nκ`, `nμ` 的树上与单种类的折叠字面同形 (判断, 证据是克隆编译通过).
>
> **对纲领与目标.** 纲领 1: 比较都是 `A` (布劳威尔树) 里的 `≤`, 输入是合法高度. 纲领 2: 无公理, 停机由检查器的结构检查给出. 纲领 3: 关系只在两边共有的目标上比 (`Two` 的 `fr`), 单世界关系只读一个世界的目标, 没有全局比较; 律只对字面第一位置陈述. 纲领 4: 导入闭包与切片干净 (审计). 目标 "让树自足": 本路是把已有的树侧证明搬到两种种类, 没有读记号, 也没有新的树侧判据; 值定理是值的定理 (`TLRuleSpec._≤_`), 不是对参照树的序数值验收.

## 文件

| 文件 | 来源 | 内容 |
|---|---|---|
| [TpPortSim](TpPortSim.lagda.md) | 生成, `HtCrossVSim` | `Free`, 互模拟 `Rl`, `sum-R`, `Ωd-R`, `Int-R` |
| [TpPortRun](TpPortRun.lagda.md) | 生成, `HtCrossVRun` | `Two`: 两个实例里折叠的七条引理 |
| [TpPortDef](TpPortDef.lagda.md) | 生成, `StrRelDef` §1 | 第 0 层结构关系 `_⊑₀_`, `val₀` |
| [TpPortGen](TpPortGen.lagda.md) | 生成, `MonoPort3Gen` | 与关系无关的和结构核 `Core` |
| [TpPortRelM](TpPortRelM.lagda.md) | 生成, `MonoPort5Rel` 的 `RelM` | 一般层的结构关系 |
| [TpPortChn](TpPortChn.lagda.md) | 生成, `MonoPort5Chn` | 第 ≥1 层的上升链 |
| [TpPortZero](TpPortZero.lagda.md) | 生成, `MonoPort6Zero` | 第 0 层的核与链 |
| [TpPortRel](TpPortRel.lagda.md) | 生成, `MonoPort7Rel` | `Rel`/`LowT`/`CtxP`, 输出律, `≼`, `HAK` |
| [TpPortInt](TpPortInt.lagda.md) | 生成, `MonoPort7Int` | `Int` 单调 (`IntMK`, `IntMS`) |
| [TpPortLay](TpPortLay.lagda.md) | 生成, `MonoPort7Lay` | 层 $L$ 的核实例 |
| [TpPortSnd](TpPortSnd.lagda.md) | 生成, `MonoPort7Snd` | 节点一步, `sndS`/`sndArg` |
| [TpPortNode](TpPortNode.lagda.md) | 生成, `MonoPort7Node` | `HAKb`, `RKb`, `nodeSelf`, **`ΩdObs`** |
| [TpPortStep](TpPortStep.lagda.md) | 手写 | `change′`, `irrF`, `SucF`, `LimF`, `fstF`, `fst<F` |
| [TpPortTab](TpPortTab.lagda.md) | 手写 | 可数高度, 去条件的六条闭项定理, `¬F-*` |
| [TpPortNeg](TpPortNeg.lagda.md) | 手写 | `no-κA`, `no-κH`, `id≤T`, `no-all` |

生成脚本: `probes/Survey/scripts/tpport/mk_tpport.py` 与 `tpgen.py`; 从仓库根运行 `python3 probes/Survey/scripts/tpport/mk_tpport.py .` 逐字节重新生成 12 个生成文件 (md5 核对过).

## 定理表 (无条件)

| 名字 | 文件 | 陈述 (读法) | 档 |
|---|---|---|---|
| `ΩdObs` | TpPortNode | 层 $k$ 不含 Ω-极限, 一切实例: $\Omega_k$ 在两个世界里的两次折叠的观测相关 (前提是动作与状态的性质, 用时都填上) | 定理 (生成) |
| `change′` | TpPortStep | `Free Λ` ⇒ $T_\Lambda$ 与它在任意大实例 $\Lambda'$, 任意位置 $e$ 上的折叠互相 $\le$ | 定理 |
| `irrF` | TpPortStep | `Free a` ⇒ `T⁺ a la ≤ T⁺ a la′` | 定理 |
| **`SucF.change`**, **`SucF.mono`** | TpPortStep | `Free h` ⇒ `Hs.ChangeHs h lh`, `Hs.MonoStepHs h lh` | 定理 |
| **`SucF.grow`** | TpPortStep | `Free h` ⇒ `asuc (T⁺ h lh) ≤ T⁺ (hs h) lh` | 定理 |
| **`LimF.M.mono`** | TpPortStep | `Upto f n` ⇒ `Hl.N.MonoHl f lf n` | 定理 |
| **`LimF.grow`** | TpPortStep | `Upto f n` ⇒ `asuc (T⁺ (f n) (proj₂ lf n)) ≤ T⁺ (hl f) lf` | 定理 |
| **`fstF`, `fst<F`** | TpPortStep | `Free b`, `a ⊑ b` (`a ⊏ b`) ⇒ `T⁺ a la ≤ T⁺ b lb` (严格) | 定理 |
| **`grow≪`** | TpPortTab | $a\ll b$ 在 `A` 里 ⇒ $T^+(a)<T^+(b)$ (可数高度) | 定理, 无前提 |
| `growN`, `growω`, `growω1`, `growω2` | TpPortTab | $T^+(n)<T^+(n+1)$; $T^+(n)<T^+(\omega)$; $T^+(\omega)<T^+(\omega+1)$; $T^+(\omega+n)<T^+(\omega\cdot2)$ | 定理, 无前提 |
| **`mul<ω₀`** | TpPortTab | `asuc (T⁺ (mul 0) (Lg-mul 0)) ≤ T-Ω₂ω` | 定理, 无前提 |
| **`fb₂<ω₀`** | TpPortTab | `asuc (T-fb₂ 0) ≤ T-fb₂ω` | 定理, 无前提 |
| **`cells<Tᵀ₀`** | TpPortTab | `asuc (T⁺ (cells 0) (proj₂ (Lg-idx Ω₃) 0)) ≤ Tᵀ` | 定理, 无前提 |
| **`cells<Tᵀ₁`**, **`cells≤₀`**, **`x<Tᵁ₀`** | TpPortTab | $T^+(\mathrm{cells}\,1)<$ `Tᵀ`; $T^+(\mathrm{cells}\,0)\le T^+(\mathrm{cells}\,1)$; `asuc (T⁺ (C₁.x 0) (C₁.lx 0)) ≤ Tᵁ` | 定理, 无前提 |
| `¬F-Ω₂`, `¬F-mul1`, `¬F-H0`, `¬F-cum0`, `¬F-Λs₂1`, `¬F-cell₂`, `¬F-x1` | TpPortTab | 这些输入含 Ω-极限 (不是 `Free`) | 定理 (只说本组不覆盖它们) |
| `no-κA`, `no-κH` | TpPortNeg | 两种种类的 Ω-极限层: $\Omega_L$ 与自己不在 `Rl` 里 | 否定, 定理 (只否定本组的互模拟覆盖 Ω-极限层) |
| `id≤T`, `no-all` | TpPortNeg | 可数 $a\le T^+(a)$; 任何合法 $\Lambda$: $\neg\,\forall a.\ T^+(a)<T^+(\Lambda)$ | 定理; 否定 (只否定 "一切 $a$, 无界") |

## 定理表 (条件) 与前提实例

| 名字 | 前提 | 实例 |
|---|---|---|
| `SucF.*` | `Free h` | `hz`, 一切 `N n`, `embᵀ a` (`free-emb`), `ω`, `ωp n`; 不满足: `Ω₂ᴴ` (`¬F-Ω₂`) |
| `LimF.*` | `Upto f n` (前 $n+1$ 项 `Free`) | `mul`, `Λs₂`, `cells`, `C₁.x` 在 $n=0$ (`up0`), `cells` 在 $n=1$ (`up1`); `N`, `ωp`, `embᵀ ∘ f` 在一切 $n$ (`upto-all`); 不满足: `mul` 在 $n\ge1$ (`¬F-mul1`), `Λs₂` 在 $n\ge1$ (`¬F-Λs₂1`), `cells` 在 $n\ge2$ (`¬F-cell₂`), `C₁.x` 在 $n\ge1$ (`¬F-x1`), `cum` 在一切 $n$ (`¬F-cum0`) |
| `fstF`, `fst<F` | `Free b` | 同 `SucF` |
| `TpMonoTab.Tab` 的 20 条 | `Laws⁺` | 没有对 `T⁺` 的实例 (同 `TpMono`); 本组只在 Ω-自由部分给出 (b). 其中 `mul<ω 0`, `fb₂<ω 0`, `cells<Tᵀ 0`, `cells<Tᵀ 1`, `cells≤ 0`, `x<Tᵁ 0` 由 `TpPortTab` 去了条件; 这五族的别的 $n$ 与另外 15 条仍是条件定理 |

## 第一个障碍

**含 Ω-极限的输入.** `TpMonoTab` 剩下的条件定理, 较小一边都含 Ω-极限 (`¬F-*`). 三处卡住, 都与单种类主线 `MonoPort8`/`9` 的第一个障碍同形:

1. **跨实例 (`ChangeHs`, `change′`)**: 本组的互模拟没有 `nκ`, `nμ` 的构造子, 装不下 Ω-极限层的 $\Omega_L$ (`no-κA`, `no-κH`, 编译过). 含 Ω-极限的层上, 两个实例回灌出的世界 (`κc` 的 `sum`, `κc₁` 的 `rd`) 只互模拟不相等, 要异质世界的关系 (`HtCrossV` 的第一个障碍; 判断).
2. **实例之内 (`MonoStepHs`, `MonoHl`)**: 单世界关系 `Rel` 在 Ω-极限层上是 $\top$ (`TpPortRel` 的定义, 同 `MonoPort7Rel`), `ΩdObs` 要 `Fin k`. 层 $k$ 含 Ω-极限时, 节点上升的链读状态在层 $k$ 上的读数, 读数含 `nκ`/`nμ` 的回灌输出 (判断; 单种类的对应是 `MonoPort9` §3 的 "下一站").
3. **`s-hΩ` 没有写.** 单种类的对应是 `MonoPort8Om` (回灌第 0 格的具体展开 + `changeW`) 与 `MonoPort9` (`growC`, 在 $V_\omega$ 里重做全部格). 两种种类多一件: 新种类 (`κH`) 的回灌第 0 格的世界是 $(1, \mathrm{rd}(\ldots, z_1\,Y))$, 沿 `H₀` 的路径走 (`Walk₁`), 路上的 `hLim` 段是旧种类的闭包 (`KG`). 对 `Ω₂ᴴ = hΩ κH up`, 第 0 格是否走过坐标 $0$ (从而给出 $T^+(0)<$ `T-Ω₂`) 取决于读回的 $v_1$ 的形状, 没有算 (判断). 没有否定定理, 写 "未走通".

没有报错原文: 本组没有对这些输入写出失败的尝试; 边界是编译过的 `¬F-*`, `no-κA`, `no-κH`.

## 翻译账

本路不读记号. 新定义:

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 12 个生成文件 | 单种类主线的树侧证明, 只换世界与高度的类型、模块参数、`Int` 的一个参数、`nμ` 的空子句 | 树逼出 (已有, 搬运) |
| `Int` 的 `zy₁`/`zz₁`, 节点的 `zL₁` | 两种种类的 `Int` 多一个 `NZ₁` 搬运参数 (`HtTowerFTree.Int` 的字面) | 树逼出 |
| `oΛ` 模块参数 | 两种种类的折叠要 "第 1 层是第一位置" (`HtTowerFFold` 的参数) | 树逼出 |
| `Upto f n` | 第 $n$ 段的比较只读前 $n$ 个节点的状态 (`Rp n`, `Rpt` 的字面) | 树逼出 |
| `free⊞`, `free-top` | `top⁺ h = 1 ⊞ h` 的字面 | 树逼出 |
| `embᵀ`, `≪→⊏` | `A` 的构造子换成高度的构造子 | 树逼出 |
| `TΛ-in`, `change′`, `Cross` | `HtCrossVInst` 的照搬 | 树逼出 (已有形状) |

归类: 提供信息 (判断). 没有新构造子或节点字段, 不改树、折叠、合法性, 没有 `Lab`, 没有记号, 没有序数值验收. 这一站新用到的字段: 两种种类的 `Int` 的 `NZ₁` 参数, `Run` 在不含 `nκ`/`nμ` 的树上的子句 (与单种类字面同形), `top⁺` 的 `⊞`. 否定 (`no-κA`, `no-κH`, `no-all`) 划出本组关系与陈述不能有的形状.

## 审计 (2026-11-05)

- **从头编译**: 删本组 16 个模块的 `.agdai` (逐个写精确模块名), 依赖用共享接口, `agda --library-file=<scratch>/libraries -i src -i probes --html … probes/OCF/Align/TpPort.lagda.md +RTS -M6G -RTS`, 退出码 0, 约 24 秒, 峰值常驻约 1.2G.
- **禁用构造**: 16 个文件的代码块里 `postulate`, 洞, `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY`, `trustMe`, `Funext`, K, `REWRITE` 都是 0; 选项都是 `--safe --without-K --lossy-unification`.
- **导入闭包** (`importclosure.py`, 不加 `--only`): 入口 76 个模块 (本地 65), `TpPortStep` 48 (本地 38), `TpPortTab` 74, `TpPortNeg` 75; 禁用表命中 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词): `fst<F` 626/0/0, `fstF` 624/0/0, `change′` 258/0/0, `grow≪` 636/0/0, `cells<Tᵀ₀` 689/0/0, `cells<Tᵀ₁` 689/0/0, `cells≤₀` 725/0/0, `x<Tᵁ₀` 645/0/0, `fb₂<ω₀` 626/0/0, `mul<ω₀` 608/0/0, `growω` 633/0/0, `growN` 631/0/0, `no-all` 639/0/0, `no-κH` 83/0/0, `ΩdObs` 434/0/0, `sndS` 400/0/0; `TpPortStep:grow` (取到 `SucF`/`LimF` 中的第一个) 616/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用 (`module TW = Two …`, `open RelP …`), 导入闭包覆盖. 只保证不引用, 不说明定义没有受记号启发.
- **生成文件**: 脚本重跑, 12 个文件 md5 与仓库里的逐字节相同.
- **代码行** (agda 块里非空非注释) / 文件行: 生成 `Sim` 115/151, `Run` 160/201, `Def` 71/90, `Gen` 321/385, `RelM` 61/80, `Chn` 58/74, `Zero` 107/132, `Rel` 237/310, `Int` 240/293, `Lay` 87/112, `Snd` 174/206, `Node` 182/225 (合计 1813); 手写 `Step` 179/282, `Tab` 120/198, `Neg` 31/54, 入口 17/约 120; 手写合计 347. 脚本 `mk_tpport.py` + `tpgen.py`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpPort where

import OCF.Align.TpPortSim
import OCF.Align.TpPortRun
import OCF.Align.TpPortDef
import OCF.Align.TpPortGen
import OCF.Align.TpPortRelM
import OCF.Align.TpPortChn
import OCF.Align.TpPortZero
import OCF.Align.TpPortRel
import OCF.Align.TpPortInt
import OCF.Align.TpPortLay
import OCF.Align.TpPortSnd
import OCF.Align.TpPortNode
import OCF.Align.TpPortStep
import OCF.Align.TpPortTab
import OCF.Align.TpPortNeg
```
