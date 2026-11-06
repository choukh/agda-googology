# `T⁺` 对输入单调 (入口): 构造一路

> 不含记号. 作者选定原话: "A2: T⁺ 对输入单调". 本篇是构造一路; 否定一路前缀 `NegTpMono`, 共用接口 [TpMonoIf](TpMonoIf.lagda.md) (接口定稿 2026-11-05 12:11; 变更: 12:23 增 §5, 只增). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不改树、折叠、合法性, 不改已有文件.
>
> **判决: PARTIAL.**
>
> 1. **`T⁺` 满足接口的律: 未证 (未走通, 没有否定定理).** (a) 互模拟不变、(b) 一切世界的字面第一位置单调对一般输入都没有证出来. 第一个障碍见下文.
> 2. **(b) 恰好等价于四条一步律 (定理).** `TpMonoStep`: `Steps F` (合法性无关; 后继; ℕ-极限第 $n$ 项; $\Omega$-极限最小坐标, 后三条严格) ⇔ `FstMono F` 与 `FstMono< F`, 对任意 `F`.
> 3. **后继一步与 ℕ-极限一步归结到一次折叠 (定理 + 条件定理, 对一切合法输入, 含两种种类的 $\Omega$-极限).** `TpMonoHs`: `T⁺ (hs h)` 严格高于 "实例 $1\boxplus(h+1)$ 里, 链第 0 项中再折叠一次 $\Omega_{1\boxplus h}$" 的和 (`hs-strict`, 无前提); 于是 `s-hs` 在 $h$ 处 ⇐ `ChangeHs h` (跨实例, 同一世界) ∧ `MonoStepHs h` (实例之内). `TpMonoHl`: 同样, `s-hl` 在 $(f,n)$ 处 ⇐ `MonoHl f lf n` (一条).
> 4. **第一站 (定理, 无前提).** `TpMonoOne.T⁺0<T⁺1 : asuc (T⁺ hz tt) ≤ T⁺ (hs hz) tt`, 由 `ChangeHs 0` 与 `MonoStepHs 0` 的证明 (`change0`, `mono0`) 经 `hs-reduce` 得到. 这也是第 3 条前提的实例.
> 5. **闭项之间的值定理表 (条件定理, 前提 `Laws⁺`)**: `TpMonoTab.Tab`, 20 条, 见下表. 律的形状可满足 (`TpMonoToy.toy`, 结构秩; 否定一路独立给出另一个模型 `rk-laws`). 请求的跨族比较 (`Tᴰ₊` 对 `Tᵁ`, `Tᵀ` 对 `Tᵁ`, `Tlv n` 对 `Tlv (n+1)`, `T∞` 对 `Tdg₂`/`T-fb₂ω`) **不在律的定义域里**: 输入之间没有字面第一位置、互模拟或左加平移的证据; 否定一路的 `blind₂` 说单靠律推不出这一类 (主审转告, 我未复核).
>
> **对纲领与目标.** 纲领 1: 一切比较都是 `A` (布劳威尔树) 里的 `≤`; 输入是合法的高度. 纲领 2: 无公理, 停机由检查器保证. 纲领 3: 律只对一切世界的字面第一位置、互模拟、左加平移陈述 (接口文件头); 只在一个世界里的版本被否定一路编译否定 (`no-fst<W⁺`, `no-fstW⁺`, 主审转告), 本接口的陈述不在其中. 纲领 4: 导入闭包与切片干净 (审计). 目标 "让树自足": 一步律 ⇔ (b) 是对路径构造子的一步定理; `Run-R`/`Chn-R` 是对折叠字面的一条关系引理, 没有读记号; 但覆盖到第 0 层的树为止. 值定理是值的定理, 不是对参照树的序数值验收.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpMono where

import OCF.Align.TpMonoIf
import OCF.Align.TpMonoStep
import OCF.Align.TpMonoToy
import OCF.Align.TpMonoHs
import OCF.Align.TpMonoHl
import OCF.Align.TpMonoOne
import OCF.Align.TpMonoTab
```

## 接口内容与变更

[TpMonoIf](TpMonoIf.lagda.md), 只有类型. `Fn = (h : Ht) → LgB h → A`; 关系 `_⊑_` (一切世界的第一位置), `_⊲⁺[_]_`, `_⊏_` (严格: 先下降一步); 律 `LgIrr`, `SimInv` (a), `FstMono`, `FstMono<` (b), `ShiftMono` (c), 记录 `Laws`, `Steps`; `Laws⁺ = Laws T⁺`, `Steps⁺ = Steps T⁺`. 律的定义域写在文件头: 每对输入带互模拟证据、一切世界的路径, 或左加平移的字面构造. 变更: 12:23 增 §5 (转出 `ChangeHs`, `MonoStepHs`, `MonoHl` 三个类型, 供否定一路对准), 只增.

**(a) 怎样处理不同的合法性证明.** `SimInv F = ∀ a la b lb → a ≈ b → F a la ≤ F b lb`: 两边的合法性证明 `la`, `lb` 各自任意. 所以 `LgIrr` 是 (a) 在 `≈-refl` 处的特例 (`T⁺` 读合法性证明: `rkT` 里的 `cmpB … lΛ`, 两个证明给出的位置可以不同). (b) 的 `fst` 在 `hself` 处也推出 `LgIrr`. 本路对 `T⁺` 的 `LgIrr` 只在 `LgB` 定义地是 $\top$ 的输入上平凡成立 (如有限高度), 一般没有证.

## 定理表

| 名字 | 文件 | 陈述 | 档 |
|---|---|---|---|
| `steps→fst`, `steps→fst<` | TpMonoStep | `Steps F → FstMono F`, `Steps F → FstMono< F` | 定理 |
| `fst→steps`, `laws` | TpMonoStep | 反方向; 合成 `Laws` | 定理 |
| `rk`, `toySteps`, **`toy`** | TpMonoToy | 结构秩 `F₀` 满足 `Steps`, `Laws` | 定理 (律的形状可满足) |
| `Hs.hs-unfold`, **`Hs.hs-strict`** | TpMonoHs | 一切 $h$: `sum b₀ X ≤ T⁺ (hs h) lh`, `asuc (sum b₀ X) ≤ T⁺ (hs h) lh` | 定理 |
| **`Hs.hs-reduce`** | TpMonoHs | `ChangeHs → MonoStepHs → asuc (T⁺ h lh) ≤ T⁺ (hs h) lh` | 条件定理 |
| `Hl.T⁺≡`, `Hl.N.hl-unfold`, **`Hl.N.hl-strict`** | TpMonoHl | 一切 $\mathrm{hl}\,f$, $n$: `T⁺ (hl f)` 不低于/严格高于 `sum β X` | 定理 |
| **`Hl.N.hl-reduce`** | TpMonoHl | `MonoHl → asuc (T⁺ (f n) _) ≤ T⁺ (hl f) lf` | 条件定理 |
| `_⊑_`, `sum⊑` | TpMonoOne | 第 0 层的树上的关系 (同形 + 右边多接一段); 相关 ⇒ 和 $\le$ | 定义, 定理 |
| **`Two.Run-R`, `Two.Rpt-R`, `Two.Chn-R`** | TpMonoOne | 任意两个实例, 第 0 层的树: 相关的树、状态与动作 ⇒ 第 0 层目标上相关的输出; 链的各项与状态相关 | 定理 |
| **`mono0`**, **`change0`** | TpMonoOne | `Hs.MonoStepHs hz tt`, `Hs.ChangeHs hz tt` | 定理 |
| **`T⁺0<T⁺1`** | TpMonoOne | `asuc (T⁺ hz tt) ≤ T⁺ (hs hz) tt` | **定理, 无前提** |
| `Tlv0≡`, `idx-hs` | TpMonoTab | `Tlv 0 ≡ T-Ω₂`, `idx (hs Ω₃) ≡ hs (idx Ω₃)` | 定理 (`refl`) |
| `hs→⁺`, `⊞-hs⁺`, `⊞-hl⁺`, `⊞-hΩ⁺`, `hz⊞≈`, `≈-sym`, `DgM` | TpMonoTab | 关系小件 | 定理 |
| `Ω₂⊏+1`, `mul1≈`, `mul1⊏2`, `mul⊏ω`, `cum⊏∞`, `cum⊑`, `fb₂⊏`, `fb₂⊏ω`, `cells⊏`, `idx⊏+1`, `x⊏` | TpMonoTab | 闭项输入之间的字面证据 | 定理 |
| `Tab.*` (20 条, 下表) | TpMonoTab | 闭项之间的值 | 条件定理 (`Laws⁺`) |

## 闭项值定理表

条件全是 `Lw : Laws⁺` (表中 "律" 一栏写用到的律). 陈述在 `TpMonoTab.Tab` 里逐字写, 下面是读法.

| 比较 | 名字 | 输入之间的证据 | 律 | 状态 |
|---|---|---|---|---|
| `T-Ω₂ < T-Ω₂+1` | `Ω₂<Ω₂+1` | `psuc hself` | (b) | 条件定理 |
| `T-Ω₂ < T-Ω₂·2` | `Ω₂<Ω₂·2` | $\Omega_2\approx0\boxplus\Omega_2$ (`mul1≈`), `mul 1 ⊏ mul 2` | (a), (b) | 条件定理 |
| `T⁺ (mul n) < T-Ω₂ω`; `T-Ω₂·2 < T-Ω₂ω` | `mul<ω`, `Ω₂·2<Ω₂ω` | `plim n hself` | (b) | 条件定理 |
| `Tlv 0 = T-Ω₂` | `Tlv0≡` | 定义相等 | 无 | **定理** |
| `Tlv n ≤ T⁺ (cum n)` | `lv≤cum` | `cum (n+1) = cum n ⊞ H (n+1)` | (c) | 条件定理 |
| `T⁺ (cum k) < T∞`; **`Tlv n < T∞`**; `T-Ω₂ < T∞` | `cum<∞`, `lv<∞`, `Ω₂<∞` | `plim k hself` | (b), (c) | 条件定理 |
| `T-fb₂ n < T-fb₂ (n+1)`, `T-fb₂ n < T-fb₂ω` | `fb₂<`, `fb₂<ω` | `fb₂-fst`, `plim n hself` | (b) | 条件定理 |
| `T⁺ (cells n) < Tᵀ`, `T⁺ (cells n) ≤ T⁺ (cells (n+1))` | `cells<Tᵀ`, `cells≤` | `plim n hself`, `cells-st` | (b) | 条件定理 |
| `Tᵀ < Tᵀ+1` | `Tᵀ<Tᵀ+1` | `idx (hs Ω₃) ≡ hs (idx Ω₃)` | (b) | 条件定理 |
| `T⁺ (x n) < Tᵁ` | `x<Tᵁ` | `plim n hself` | (b) | 条件定理 |
| `Tᵁ` 在外层 $(0,\omega)$ 上同值 | `Tᵁω≤`, `Tᵁ≤ω` | `inω≈` | (a) | 条件定理 |
| `Tᴰ₊` 每项 $=$ `T-Ω₂`; `Tᴰ₊` $=$ `Dg (λ _ → T-Ω₂)` | `t≤Ω₂`, `Ω₂≤t`, `Tᴰ₊≤`, `≤Tᴰ₊` | `pr₀-top`, `in-suc` | (a) | 条件定理 |
| `Tᴰ₊ ≤ Tᵁ`? | — | 没有: `Ω₂ᴴ` 与槽 `x n` 之间无字面证据 | — | 不在定义域 |
| `Tᵀ ≈ Tᵁ`? | — | 没有: 格 `cells` 是读回的累加, `x` 是槽; `H 1 ≡ idx (Ωtop S₁)` 不是定义相等 (实验, `refl` 被拒) | — | 不在定义域 |
| `Tlv n < Tlv (n+1)`? | — | 没有: `H n`, `H (n+1)` 是不同级的下降, 无字面证据 | — | 不在定义域 |
| `T∞` 对 `Tdg₂`, `T-fb₂ω` | — | 没有: `Λ∞` 与 `Λω₂` 无字面证据; `Tdg₂` 对 `T-fb₂ω` 要连续性或加法闭包, 不是单调律 | — | 不在定义域 |
| `T⁺ 0 < T⁺ 1` | `T⁺0<T⁺1` | `psuc hself` | 无 (直接证) | **定理** |

"不在定义域" 的几条: 律是对字面证据陈述的, 这几对输入是不同折叠或不同读回的产物, 之间没有接口里的三种证据. 要比较它们, 要的是输入高度之间的值比较 (判断: 那是 "按值单调" 一类, 先对照手册 §3.1 与否定一路的 `no-valmono⁺` 再决定), 或者证明两个读回之间的字面关系 (例如槽与格的互模拟, 要 (a) 的加强: 第 2 层目标的输出读回后互模拟). 都没有做.

## 前提实例

- `Laws⁺` (表的前提): **没有对 `T⁺` 的实例.** 律的形状可满足: `TpMonoToy.toy` (结构秩 `F₀`); 否定一路的 `rk-laws` 是另一个 (主审转告). 这只说明条件定理不是因律自相矛盾而空真, 不说明 `T⁺` 满足它们.
- `Hs.hs-reduce` 的 `ChangeHs h`, `MonoStepHs h`: $h=0$ 处有实例 `change0`, `mono0` (定理). 一般 $h$ 没有. 单种类主线的对应物在不含 $\Omega$-极限的输入上是编译过的定理 (`HtCrossVInst.X≈`, `MonoPort7Lim.Suc.monoS`; 判断: 照搬到两种种类的折叠上对不含 $\Omega$-极限的 $h$ 可满足).
- `Hl.N.hl-reduce` 的 `MonoHl`: 没有实例 (单种类主线的对应物 `MonoL` 在 `Free (hl f)` 上是 `MonoPort7Lim.Lim.monoL`).

## 第一个障碍

**`ChangeHs h` 在 $h\ge1$ (以及一切含 $\Omega$-极限的 $h$) 上.** 两个实例里同一次折叠, 输出在 ℕ-分支的 $\lambda$ 之下是两个实例各自的项, 只能逐点相关, 不定义相等. [实验, 有限测试] $h=0$ 时 `Hs.X hz tt ≡ Hs.X′ hz tt` 用 `refl` 被拒 (`UnequalTerms: hs hz != hz of type HB S₁`), 所以连最小的一站也要一个关系 (本路的 `_⊑_`). 本路的关系只覆盖第 0 层的树; $h\ge1$ 时链的项是第 $\ge1$ 层的树, 含节点, 输出要在第 $\ge1$ 层的目标上比, 节点在高目标上 "保留" 时比较两个实例的 `cmpB` 结果 (位置不同, 由 `lΛ` 搬出). 这是 `HtCrossVRun` (单种类, `Free`) 那一族关系在两种种类上的对应, 加上 `nκ`, `nμ`, `Walk₁`, `RunM` 的子句. 含 $\Omega$-极限时更进一步: 回灌把第 0 层的输出读成世界 (`κc` 的 `sum`, `κc₁` 的 `rd`), 两个实例回灌出的世界只互模拟不相等, 关系要异质 (`HtCrossV` 的第一个障碍; 边界 `HtCrossVNeg.no-val-world`, `no-κ`, `MonoPort8Sim.no-κE` 都是单种类的编译否定, 只杀那几种关系的形状). 没有否定定理, 写 "未走通".

**`MonoStepHs h`, `MonoHl`**: 实例之内的 $\le$ 语义. $h=0$ 时第 0 层的 `_⊑_` 够 (`mono0`); 一般要 `MonoPort6`/`7` 的 `Rel`/`ΩdObs` 在两种种类上的对应, 含 $\Omega$-极限的层要跨世界的 $\le$ 关系 (`MonoPort9` §3 的 `GoodUp`, 未证).

**`s-hΩ`**: 没有写展开. 单种类的对应 `MonoPort8Om` (旧种类, 分支不含 $\Omega$-极限) 的形状: 回灌第 0 格的第一个节点 + 换世界换实例 (`changeW`, 要 `Free`). 两种种类多一个新种类闭包 (`RunM` 回灌, `κc₁`/`rd`/`Walk₁`).

报错原文 (实验): `error: [UnequalTerms] hs hz != hz of type HB OCF.Align.HtTowerFTree.S₁ when checking that the expression refl has type Hs.X hz tt ≡ Hs.X′ hz tt`.

## 翻译账

本路不读记号. 新定义:

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 律的定义域: 一切世界的第一位置 | 壁垒影子 (`no-all` 一类); 一切世界里过 $\Omega$-分支只能走 `bot` | 树逼出 (否定逼出) |
| `Steps` 与 `steps→fst` | 路径的三个构造子; 最小世界里的界 | 树逼出 (结构参数的一步定理) |
| (c) `ShiftMono` | `FamFoldAll.cum` 的累加 `⊞` | 树侧的加法; 为接上 `Tlv n` 与 `T∞` 而加 (判断: 不来自记号, 但是为一组闭项而加的律) |
| `hs-unfold`/`hs-strict`/`hl-*` | `HtCrossInst.Hs`/`Hl` 的照搬, 折叠的字面 (`Run`, `RunNi`, `RKi`, `Chn`) | 树逼出 |
| `_⊑_` 的 `r+` (右边多接一段) | 大状态的读数以小状态的读数为前缀 (`⊕` 的字面) | 树逼出 |
| `Two.Run-R`/`Chn-R` 对两个实例 | 折叠在第 0 层的树上只经 `Run` 五句与动作 | 树逼出 |
| `TpMonoToy.rk` | 律的可满足性 | 验收工具, 不进成品 |

归类: 提供信息 (判断). 没有新构造子或节点字段, 不改树、折叠、合法性, 没有 `Lab`, 没有记号, 没有序数值验收. 这一站新用到的字段: 路径的构造子与最小世界的界 (`TpMonoStep`); `Ωd (hs b)` 与 `Ωd (hl f)` 的节点在第 0 层目标上上升, 链从状态读数起步 (`TpMonoHs`, `TpMonoHl`); `⊕` 把输出接在状态读数的右边 (`r+`). 否定的划界在否定一路.

## 审计

2026-11-05:

- **从头编译**: 删本路八个模块的 `.agdai` (逐个写精确模块名), 依赖用共享接口, 入口 `agda --library-file=<scratch>/libraries -i src -i probes --html … probes/OCF/Align/TpMono.lagda.md +RTS -M6G -RTS`, 退出码 0, 8.1 秒, 峰值常驻约 0.79G.
- **禁用构造**: 八个文件的代码块里 `postulate`, 洞, `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY`, `trustMe`, `Funext`, K 都是 0; 选项都是 `--safe --without-K --lossy-unification`. 终止由结构检查给出 (`fst₀` 对路径, `Run-R`/`Rpt-R` 对 `_⊑_` 的推导, `Chn-R` 对 ℕ).
- **导入闭包** (`importclosure.py`, 不加 `--only`): 八个模块逐个跑, 退出码 0, 禁用表命中 0; 入口闭包 68 个模块 (本地 57), `TpMonoOne` 24 (本地 14).
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词): `TpMonoOne:T⁺0<T⁺1` 274/0/0, `change0` 237/0/0, `mono0` 242/0/0, `TpMonoHs:hs-strict` 222/0/0, `TpMonoHl:hl-strict` 235/0/0, `TpMonoStep:steps→fst<` 76/0/0, `TpMonoToy:toy` 95/0/0, `TpMonoTab:lv<∞` 373/0/0, `≤Tᴰ₊` 378/0/0, `Tlv0≡` 352/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用 (`module I12 = Two …`, `module H0 = Hs …`), 导入闭包覆盖. 只保证不引用, 不说明定义没有受记号启发.
- **生成文件**: 无 (全部手写, 没有建 `probes/Survey/scripts/tpmono/`).
- **代码行** (agda 块里非空非注释) / 文件行: `TpMonoIf` 56/126, `TpMonoStep` 43/80, `TpMonoToy` 36/53, `TpMonoHs` 46/96, `TpMonoHl` 68/114, `TpMonoOne` 159/256, `TpMonoTab` 124/211, 入口 9/约 115; 合计代码 541.
