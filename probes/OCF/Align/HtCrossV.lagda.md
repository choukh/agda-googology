# 跨高度比较闭项: 换实例, 不用外延性

> 主线 (高度树 `HtFeed`) 第一个障碍第 1 条的复做, 对应 `RouteReview2` 的 P3. 入口. **判决: PARTIAL.** 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, **不用函数外延性** (主线四个文件的源码与导入闭包里都没有它, 见审计). 定义不读记号, 没有验收文件.
>
> - **不含 $\Omega$-极限的高度上, 换实例做到了, 在值上, 不用外延性.** 小的那个实例的最高层 $\Lambda$ 不含 `hΩ` (`Free`, 一切可数高度 `emb a` 都是, `free-emb`), 大的那个实例 $\Lambda'$ 任意: `TΛ Λ l` 与 `TΛ-in Λ′ l′ Λ e` 在值上相等 (`change′`, 互相 `≤`), 与合法性证明无关 (`lg-irr′`). 跨高度的归结 `hs-reduce<′` (前提只有 `MonoStep`), `hl-reduce<′` (前提只有 `MonoL`, 只要第 $n$ 段 `Free`) 成立; $\Lambda=0$ 时无条件: `hz<1′ : asuc (TΛ 0) ≤ TΛ 1` (原来是外延性的条件定理, 现在是定理).
> - **含 $\Omega$-极限的高度没有做到.** 旧的条件定理在这部分没有新版本 (表中标 "无"). 编译过的边界: 原路线那一步 (`eq0`) **恰好等价于**第 0 层 ℕ-序列的外延性 (`eq0↔ext`); P3 提的 "第 0 层只要值相等" 与现有的结构关系接不上 (`no-val-world`); 无回灌的关系装不下 $\Omega$-极限的输入 (`no-κ`); `EndLowAccept.ToLimit` 要的那一段不在范围内 (`fb1-not-free`). 一般情形的第一个障碍是**异质世界**: 两个实例回灌出的世界只是互模拟, 不相等, 关系要对两个不同的世界与两个不同的高度说话 (判断, 见 "第一个障碍"). 未走通, 没有否定定理.

## 设计

| 件 | 定义 | 文件 |
|---|---|---|
| 不含 $\Omega$-极限 | `Free : H → Set`, `free⊲` (第一位置继承), `free-emb` | [HtCrossVSim](HtCrossVSim.lagda.md), [HtCrossVInst](HtCrossVInst.lagda.md) §6 |
| 关系 | `SimD`/`RelA`/`Rl`: 与 `HtCrossSim` 相同, **没有 `sκ`**; `irr`, `conv`, `Ωd-R` (要 `Free`), `Int-R` (无 `nκ` 子句) | HtCrossVSim |
| 第 0 层到值 | `sum-R`, `pt-R`, `sym0`, `sum-R′`: 相关的第 0 层树, 和在值上相等 | HtCrossVSim |
| 状态 | `StR`: **只有差**, 没有第 0 层的相等 `zR` | [HtCrossVRun](HtCrossVRun.lagda.md) |
| 共有目标不含 $\Omega$-极限 | `Two` 的参数 `fr`, 用时取任一边的 `Free` | HtCrossVRun |
| 折叠 | `Run-R`, `Rpt-R`, `RunNi-R`, `Ai-R`, `Chn-R`, `RKi-R`, `BNi-R`: 与 `HtCrossRun` 同名七条逐字相同 (`Run-R` 少 `sκ` 一条); 回灌的十条不要 | HtCrossVRun |
| 换实例 | `inst0′`, `Rl→≈`, `change′`, `lg-irr′`, `hs-in′`, `hl-in′`, `hΩ-in′`, `Ω-in′` | HtCrossVInst |
| 归结 | `X≈`, `hs-reduce′`, `hs-reduce<′`, `hl-reduce′`, `hl-reduce<′`, `hz≤1′`, `hz<1′`; 无条件的展开与严格照抄 | HtCrossVInst |
| 边界 | `eq0↔ext`, `no-val-world`, `no-κ` | [HtCrossVNeg](HtCrossVNeg.lagda.md) |
| 对照 | `MonoStep≡`, `MonoL≡`, `TΛ-in≡`, `X≡`, `X′≡` (都是 `refl`); `fb1-not-free`, `fb0≤ω` | [HtCrossVBridge](HtCrossVBridge.lagda.md) |

**为什么去掉 `nκ` 就不要外延性.** 旧证明里外延性只在 `eq0` 用, `eq0` 只在 `zR` (状态第 0 层部分的相等) 用, `zR` 只在回灌 (`κc` 的世界 $v=\mathrm{sum}\,W\,(z\,Y)$) 读. 回灌只由 `nκ` 触发, `nκ` 只来自 `Ωd (hΩ g)` (`Int` 只把 `nκ` 搬成 `nκ`). 小实例的最高层不含 `hΩ` 时, 一切共有目标 $t$ 也不含 (`free⊲`), `Step` 写进去的 $\Omega_t$ 没有 `nκ`, 输入也没有, 于是相关的树里从不出现 `nκ`, `z` 只被写, 从不被读, `StR` 可以不比它. 第 0 层的输出只相关不相等, 但闭项是它们的和, 相关的和值相等 (`sum-R`), 这就够了.

**为什么大实例可以任意.** 关系只在两边共有的目标上比 (`DfR`), 共有目标是小实例最高层的第一位置. 大实例在别的目标 (含 $\Omega$-极限的) 上写什么, 关系不看, 也没有流回共有目标: 节点的层是输入里的层, 都在小实例之下.

**与壁垒.** 与 `HtCross` 相同: 两个实例的输入是同一层的树, 目标在两边都是最高层的第一位置, 世界是同一个字面的世界. 没有全局比较.

## 定理表

"旧" 列是 `HtCross` 里以外延性为前提的结果, "新" 列是本族不用外延性的版本.

| 旧 (条件: 外延性) | 新 | 文件 | 新的陈述 | 档 |
|---|---|---|---|---|
| `Run-R` 与同伴 | `Run-R` 与六个同伴 | HtCrossVRun | 无 `nκ` 的关系下, 两个实例的折叠在共有目标上相关; 共有目标 `Free` | 定理 |
| `inst0` | **`inst0′`** | HtCrossVInst | 第 0 层输出相关 (`Rl hz`), 不是相等 | 定理 |
| `change` | **`change′`** | HtCrossVInst | `Free Λ` ⇒ `TΛ Λ l ≈ TΛ-in Λ′ l′ Λ e` (值, 两个方向), $\Lambda'$ 任意 | 定理 |
| `lg-irr` | **`lg-irr′`**, `lg-irr-emb` | HtCrossVInst | `Free Λ` ⇒ `TΛ Λ l ≈ TΛ Λ l′`; 一切可数高度 | 定理 |
| `hs-in`, `hl-in`, `hΩ-in` | `hs-in′`, `hl-in′`, `hΩ-in′`, `Ω-in′` | HtCrossVInst | 同上的特例; `hΩ-in′` 只要分支 `g c` 是 `Free` | 定理 |
| `X≡` | `X≈` | HtCrossVInst | `Free Λ` ⇒ `sum b₀ X ≈ sum b₀ X′` | 定理 |
| `hs-reduce`, `hs-reduce<` | **`hs-reduce′`, `hs-reduce<′`**, `hs-reduce<-emb` | HtCrossVInst | `Free Λ`, `MonoStep` ⇒ `asuc (TΛ Λ) ≤ TΛ (hs Λ)` | 条件定理 (`MonoStep`, 未证) |
| `hl-reduce`, `hl-reduce<` | **`hl-reduce′`, `hl-reduce<′`** | HtCrossVInst | `Free (f n)`, `MonoL n` ⇒ `asuc (TΛ (f n)) ≤ TΛ (hl f)` | 条件定理 (`MonoL`, 未证) |
| `hz≤1`, `hz<1` | **`hz≤1′`, `hz<1′`** | HtCrossVInst | `asuc (TΛ 0) ≤ TΛ 1` | **定理, 无前提** |
| 同上, 含 $\Omega$-极限的 $\Lambda$ | 无 | | | 未走通 |
| `path-rel` (`hΩ g` 上) | 无 | | 输入含 `nκ` | 未走通 |
| `EndLowAccept.ToLimit` | 无 (`fb1-not-free`) | HtCrossVBridge | `Λs 1` 是 $\Omega$-极限 | 否定 (只否定本族覆盖它), 定理 |
| | `MonoStep≡`, `MonoL≡`, `TΛ-in≡`, `X≡`, `X′≡` | HtCrossVBridge | 新旧前提与闭项逐字相同 | 定理 (`refl`) |
| | **`eq0↔ext`** | HtCrossVNeg | `(Rl hz x y → x ≡ y)` ⟺ 第 0 层 ℕ-序列的外延性 | 定理 |
| | **`no-val-world`** | HtCrossVNeg | 值相等的两个第 0 层状态回灌出值相等的世界, 切出的上下文不相关 | 否定, 定理 |
| | `no-κ` | HtCrossVNeg | `¬ Rl (hΩ g) (Ωd (hΩ g)) (Ωd (hΩ g))` | 否定, 定理 |

`hs-unfold`, `hl-unfold`, `hs-strict`, `hl-strict`, `mono-hz` 本来就无前提, 照抄进 HtCrossVInst (免得导入旧文件), 不另列.

**读法 (判断).** `Free` 的高度是可数的 (由 `hz`, `hs`, `hl` 生成), 闭项读 $\psi_0(\Omega_x)$, $x<\Omega$. 第一个不在内的高度是 `Ωᴴ` ($\psi_0(\Omega_\Omega)$); 它在世界 1 里的两个分支在内 (`Ω-in′`).

## 第一个障碍

**回灌的世界是类型的下标, 两个实例算出的世界只是互模拟.** (判断, 有编译过的旁证.)

1. **相等要外延性.** 两个实例的第 0 层输出含 $\mathbb N$-分支 (`rise` 给 `nl`), 分支是两个实例各自的 λ, 只能逐点相关. `eq0↔ext`: "相关 ⇒ 相等" 恰是 ℕ-序列的外延性, 不能另证.
2. **不相等就是两个世界.** `κc` 把 $v_i=\mathrm{sum}\,W\,(z\,Y_i)$ 作新世界, 下游的 `St v`, `D ly v`, `Tg v t m` 都以它为下标. $v_1\ne v_2$ (字面) 时, 两次折叠在不同的世界里继续, 此后的世界都字面地含 $v_1$ 或 $v_2$, 没有共有的目标. `DfR` 只在共有目标上比, 就成了空话.
3. **值相等不够** (`no-val-world`): 关系要沿世界的结构走 (`Walk`, `Cut` 对路径递归), 值相等的世界形状可以不同, 切出的上下文不相关. 要的是**互模拟** (同形, 极限处逐点), 不是 `≈`.
4. **于是关系要异质.** 对 $W_1\approx W_2$ (互模拟) 的两个世界, 路径 $W_i\lhd W_i'$ 相关, `Lg` 证明相关, `cmpF` 对相关输入判定相同. 回灌走过 $[W_0, v)$ 的坐标 $c$, 在 $v_1$, $v_2$ 的非共有部分里, 坐标 $c_1\approx c_2$ 不相等, `Ωd (hΩ g)` 的分支给出层 $g\,c_1$, $g\,c_2$ 的节点: **高度也要异质**, 而且要 $g$ 把互模拟的坐标送到互模拟的高度. 对任意的 $g : A\to H$ 这不可证 (它本身是一种外延性, 判断); 对具体的高度 (如 `emb`, 由结构递归定义) 可以逐个证. 所以一般情形的最弱前提应是对 $\Lambda$ 的一条性质 "`hΩ g` 保互模拟", 而不是全局的外延性 (判断, 未编译).
5. **判定一致还要一条引理**: 异质时 `rkT-rel` 的 "一边保留一边上升" 要推出 "高度互模拟于自己的严格第一位置", 再由良基否定 (判断, 未编译).

照此写, 要把 `HtCrossRun` 的十七条 (含回灌的十条) 连同 `Int-R`, `IW-R`, `Cut-R` 改成对两个世界、两个高度的版本 (判断: 行数至少是现在的两倍). 没有写. **没有否定定理**, 只写 "未走通".

**P3 的工程判断要更正.** `RouteReview2` P3 说 "`StR` 第 0 层改为 `≈ᵛ`/`≤` 双向而不是 `≡` (入口已判断可行)". 按上面 2–3, 只改 `StR` 一处不行: 世界是类型下标 (`κc`), 值相等的世界给不出相关的上下文 (`no-val-world`). 可行的是本族的做法 (第 0 层只在最后取值, 中途不读) 加上它的范围限制 (`Free`).

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 关系去掉 `sκ` | 回灌的世界是第 0 层输出的和, 是类型下标; 相等要外延性 (`eq0↔ext`) | **树逼的** |
| `StR` 去掉 `zR` | `z` 只在回灌里被读 | 树逼的 (`κc`) |
| `Free`, `fr` | `Step` 在每个共有目标写 $\Omega_t$, 只有 `Free` 的 $t$ 不含 `nκ` (`no-κ`) | 树逼的 |
| 结论在值上 (`≈`) | 规则 (不用外延性) 加 `eq0↔ext`; 闭项是和, 相关的和值相等 (`sum-R`) | 树逼的 |
| 其余 (`Run-R` 七条, `Int-R`, 展开, 严格) | 逐字照抄 `HtCross` | 无新增 |

**按 `AGENTS.md` 归类: 提供信息.** 没有新构造子, 没有新节点字段, 没有改折叠, 没有 `Lab`, 没有记号. 一步定理: `Run-R` 对一切 $(\Lambda_1,l_1,\Lambda_2,l_2)$ 与一切层 (共有目标 `Free`); `change′` 对一切 `Free` 的 $\Lambda$ 与一切 $\Lambda'$. 否定定理划出不能有的: 不用外延性的第 0 层相等 (`eq0↔ext`), 值相等的世界上的结构关系 (`no-val-world`), 无回灌关系里的 $\Omega$-极限 (`no-κ`). 这一站**没有新用到树的任何字段**: 它是把旧证明里外延性的唯一用处定位到 `κc`, 再划出不经过 `κc` 的部分. 没有序数值验收 (没有参照树).

## 账

文件级 (agda 代码块里非空非注释的行):

| 文件 | 行 | 内容 |
|---|---|---|
| `HtCrossVSim` | 113 | `Free`, 无 `nκ` 的关系, 第 0 层到值, 小件, `Int-R` |
| `HtCrossVRun` | 159 | 判定一致 (照抄), 两个实例的折叠 (七条) |
| `HtCrossVInst` | 161 | 换实例 (值), 归结, 照抄的展开与严格, 可数高度 |
| `HtCrossVNeg` | 62 | `eq0↔ext`, `no-val-world`, `no-κ` |
| `HtCrossVBridge` | 28 | 对照 (导入旧文件) |
| 入口 | 6 | |
| 合计 | 529 | |

脚手架分账 (判断): `sum-R` 一族 (约 20 行) 是 "结论只到值" 所需; 其余与 `HtCross` 逐字相同或是它的子集, 没有一行按站写. 与 `HtCross` 比, 少了回灌的十条 (约 120 行) 与 `IW-R`, `Cut-R`.

## 审计

- **导入闭包** (`importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRuleSpec --only OCF.Align.TLRuleSum --only OCF.Align.SumOne --only OCF.Align.HtGen --only OCF.Align.HtFeed --only OCF.Align.SumVar --only OCF.Align.CvFold --only OCF.Align.CvHigh --only OCF.Align.CvLayer --only OCF.Align.HtCross --only OCF.Align.HtCrossV`): 入口 (25 个模块, 本地 15), `HtCrossVSim` (本地 7), `HtCrossVRun` (11), `HtCrossVInst` (13), `HtCrossVNeg` (8) 都是退出码 0, 禁用表 0, `--only` 之外 0. 入口的闭包里**没有** `HtCrossSim`, `HtCrossRun`, `HtCrossInst`, `HtCrossNeg`, 闭包里的本地源文件都不含外延性这个词 (按词扫过). 对照文件 `HtCrossVBridge` 导入 `HtOutFeed`, 在上面的 `--only` 下退出码 1 (`HtOutRead` 在表外, 预期如此); 加 `--only OCF.Align.HtOut` 后退出码 0, 禁用表 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `HtCrossVRun:Run-R` 146/0/0, `HtCrossVInst:change′` 177/0/0, `lg-irr′` 178/0/0, `hs-reduce<′` 196/0/0, `hl-reduce<′` 215/0/0, `hz<1′` 199/0/0, `Ω-in′` 186/0/0, `HtCrossVNeg:eq0↔ext` 37/0/0, `no-val-world` 44/0/0, `no-κ` 29/0/0, `HtCrossVBridge:MonoStep≡` 124/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明没受记号启发.
- **禁用构造**: 六个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 不用 `--cubical`; 都带 `--safe --without-K --lossy-unification`. 六个文件里没有外延性的名字 (按词扫过, 0 处).
- **从头编译** (`--ignore-interfaces`): 入口退出码 0 (30 秒, 峰值 1.2G); `HtCrossVBridge` 退出码 0.

## 时间线

写定义前读过: `HtCross`, `HtCrossSim`, `HtCrossRun`, `HtCrossInst` (全文), `HtFeedTree`, `HtFeedFold`, `HtFeedClosed`, `HtFeedGrow` 前半, `CumReadCF` 前半, `TLRuleSpec` 的序, `EndLowAccept` §4, `HtOutFeed` 的 `Λs`, `RouteReview2` P1–P8. 没有打开 `EBO`, `Correspond`, `Label`, 也没有读任何基本列规则.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtCrossV where

open import OCF.Align.HtCrossVSim using (Free; free⊲; SimD; RelA; Rl; irr; sum-R; sum-R′; Ωd-R; Int-R) public
open import OCF.Align.HtCrossVRun using (module Val; module Two) public
open import OCF.Align.HtCrossVInst using (_≈_; module Cross; Rl→≈; TΛ-in; change′; lg-irr′; hs-in′; hl-in′; hΩ-in′; module Hs; module Hl; module HsS; module HlS; mono-hz; hz≤1′; hz<1′; free-emb; lg-irr-emb; Ω-in′; hs-reduce<-emb) public
open import OCF.Align.HtCrossVNeg using (SeqExt₀; Eq0; eq0→ext; ext→eq0; eq0↔ext; no-val-world; v≈; no-κ) public
```
