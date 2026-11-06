# 只对可入层号给分量的并: 构造一路 (入口)

> 不含记号. 作者选定原话: "ColimW: 只对可入层号给分量". 接口 [ColimAIf](ColimAIf.lagda.md) ("接口定稿 2026-11-05 11:12", 变更记录: 无), 与否定一路 `NegColimA*` 共用. 配合 [ColimW](ColimW.lagda.md) 的第一个障碍, [ColimWNeg](ColimWNeg.lagda.md) 判决里的 "不否定: 世界只对可入层号给分量", [Survey/StallDiagnosis.md](../../Survey/StallDiagnosis.md) §2.2 (W⁺), §2.4. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延; UIP 只在 `ColimARaise` §3 作前提 (条件).
>
> **判决: 部分成立.** 前两步是定理 (对一切 `S`, 一切合法外层世界与外层界), 第三步在最小实例上是定理; 没有折叠, 没有闭项, 没有值的结论.
>
> 1. **`LevC′ X w` 是种类结构** (定理, [ColimAKS](ColimAKS.lagda.md)). 世界 `GWA X w = A × Π_y (AdmL X w y → HB (LevA w y))` 只对可入层号给分量, 分量以证据为参数. 由它算不出原来的 `Wd (Lev x)` (Ω-结点要对一切坐标给分量, 有界与否不可判定; 接口文件头), 所以种类族换成 `LevA w`: **Ω-并只取有界坐标**, 种类带坐标的界的证据. `restrA` 沿种类里的证据把路径接下去, `LevC′` 是拉回, `cmpK`, `botBd` 原样拉回.
> 2. **认同: 每个种类读自己的 (层号, 证据) 处的分量** (`globA`, `refl`). **拷贝的认同要跨证据相干**: 相干世界里同一层号两个证据下的界互推 (`crossA`, `crossPrA`, 定理, 不用外延); 不相干时有合法世界使 `κ₂`, `κ₂′` 读到不同的界 (`noCrossA`, 定理). 所以认同需要相干, 这一条写进了接口 `CrossA` 的前提.
> 3. **`copy→⊥` 在 `LevC′ x₀ wω` 里不成立的前提是逐分量合法 `LocalLg`** (定理, [ColimACopy](ColimACopy.lagda.md)), 与 `ColimWCopy` 相同. 拷贝 (同一层号的两个种类) 不在 `CopyShape` 的范围里, 由第 2 条处理.
> 4. **可入层号上的更新, 包括无限层号** (定理, [ColimARaise](ColimARaise.lagda.md)). `raiseA′`: 对一切 `S`, 一切合法 $w$, $X$, 满足接口 `RaiseA′` 七条律; 判定用 `bdec`; **增量是可入层号上的族** (LocUip 的族增量写法), 判为相等时取族在 $(y, p)$ 处的值, 不沿相等证明搬运, 所以 `atA` 不要对角引理, `cohA` (保相干) 不要 UIP. 对 `ColimWNeg` 的外层世界族一致地构造出来 (`raiseA′-wα : ∀ α → RaiseA′ x₀ (wα α)`). **单个增量**的版本要沿判定给的相等证明搬运: 在 UIP 之下有 (`uip→raiseA1`, 条件定理); 不加 UIP 没有证, 也没有否定. 这正是 `AdmWCoh` 的墙的同一位置, 族增量绕开了它, 单个增量没有.
> 5. **一步回灌与 ω 条** (定理, 最小实例 $X = x_0$, 外层世界 `wω`). 在有限层号 `finH 1` 与第一个无限层号 `up ω₀` (`ColimW` 的第一个障碍) 上各接一次族 `topF` (每个后继层号放它之上的第一个 Ω): 合法, 变大, 相干; `κ₂` 与 `κω` 处含新种类节点的格有界 (`cell₂`, `root₂`, `cellω`, `rootω`), 拷贝 `κ₂′`, `κω′` 处同一个格有界 (`cell₂′`, `cellω′`; 由 `atA` 对一切证据直接得到). 在 `up ω₀` 上接 $n$ 份得 $W_n$, 接它们的 ℕ-极限得 $W_\omega$: 都合法相干, $W_n\le W_{n+1}$, $W_n\le W_\omega$, 第 $n$ 格与极限格各在自己的世界里有界 (`Wn≤`, `Wn≤ω`, `celln`, `cellωω`, `cellωω′`).
>
> **`raiseA-sep` 为什么在这里不适用.** 它读 `proj₂ (Fα α) (up ω₀)`: 世界在**裸**层号 `up ω₀` 处的值. `GWA` 在那里的分量要证据 `AdmL x₀ (wα α) (up ω₀)`, 而证据只在 $\alpha$ 某处为真时有 (`ColimWNeg.adm₁` 要 $k$ 与 `α k ≡ true`); 有了证据, "是不是 $y_0$" 由 `decA` (即 `bdec`) 直接判定. 编译的事实是 `raiseA′-wα` (前提族是定理). 判断 (元层): 对本接口若有 `FE₀ → (∀ α → RaiseA′ x₀ (wα α)) → WLPO`, 与 `raiseA′-wα` 合起来得 `FE₀ → WLPO`, 在有外延而 WLPO 不成立的实现性模型里不成立; 所以那样的论证对本接口不存在.
>
> **是否回到 `AdmWCoh` 的跨证据相干/UIP 墙.** 分两处回答. (i) **认同**: 回到了 "要跨证据相干" (`noCrossA`, 定理), 但相干由更新保持, 不要 UIP (族增量, `cohA`). (ii) **更新**: 单个增量回到 UIP 墙 (`uip→raiseA1` 只是条件定理; 墙的确切内容同 `LocUipNegLoop`), 族增量绕开 (`raiseA′`). 所以这一路把墙推到了 "回灌产出的增量是不是对层号一致的族" 上 (`LocUipNegSec` 的同一陈述: 读回值是某个族在 $y_0$ 处的值).
>
> **第一个障碍 (判断, 没有定理).** 两处, 都没有试.
>
> 1. **回灌产出族增量.** 折叠在节点处读回的是一个高度 (单个增量). 要用 `raiseA′`, 读回必须写成对一切可入层号一致的函数, 在 $y_0$ 处取值; 写不成就落回单个增量, 即 UIP 墙. 本篇的 `topF` 是一致的族, 但不是读回.
> 2. **外层世界变大.** `LevA w` 的种类带外层世界 $w$ 下的证据. 外层世界 $w \le w'$ 时高度沿 `Bd↑` 搬到 `LevA w'` 没有问题; 但世界 `GWA X w` 要扩成 `GWA X w'`, 新世界在 $w'$ 下可入的每个 $(y, p')$ 处都要一个分量, 而 "$p'$ 是不是某个 $w$ 下的证据搬上来的" 要判定. 判断: 在公共界 $w'$ 之下用 `cmpB`/`cmpF` 大概可判定 (同 `bdec` 的道理), 但证据是数据, 扩张后的相干要重新证.
>
> **对纲领与目标.** 不触壁垒: 没有序, 没有全局三歧; 一切判定在同一合法界 $X$ 之下、同一合法外层世界 $w$ 里 (`bdec`), 一切比较在同一种类的同一个界之下. 律的定义域按 AGENTS: 更新律里每一对层号都带 $X$ 之下的证据; 认同律每条只含一个种类; 拷贝律带相干前提. 这一路对 `ColimW` 的第一个障碍 (无限层号上的更新) 给出构造, 代价是 (a) 种类带外层证据, (b) 拷贝要相干, (c) 增量要是族.
>
> **交付拆成两条.** (a) 合法的构造: `LevC′` (一切 $X, w$), `raiseA′` (一切合法 $X, w$, 一切层号), `W₁`, `Wω₁`, $W_n$, $W_\omega$ (合法, 相干, 变大; `κ₂`, `κω` 及其拷贝处含新节点的格有界). 没有闭项, 没有折叠. (b) 关于值的定理: **没有** (这一路不涉及序数值; 世界不是闭项).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ColimA where

open import OCF.Align.ColimAIf public
open import OCF.Align.ColimAKS public
open import OCF.Align.ColimACopy public
open import OCF.Align.ColimARaise public
```

## 接口内容

| 名字 | 内容 |
|---|---|
| `LevA w` | Ω-并只取外层世界 $w$ 下有界坐标的种类结构族 (底 `S₀`, `step`, `sup ℕ` 原样) |
| `GWA X w` | 只对可入层号给分量的世界, 分量以证据为参数 |
| `Adm.dnS`, `dnL`, `dnΩ`, `restrA` | 路径下行; `LevA w x` 的世界沿路径由 `GWA` 算出 |
| `Adm.LgGA`, `_≤GA_`, `CohA` | 合法, 世界序, 跨证据相干 |
| `Adm.KC`, `EC`, `LgWC`, `BdC`, `PrC`, `CmpKC`, `BotBdC` | `LevC′ X w` 的各部分 (沿 `restrA X hself`) |
| `Adm.LvA`, `LEA`, `lvlA`, `cEA`, `BdLA`, `PrLA`, `GlobA`, `GlobPrA` | 带证据的层号映射与认同律 (每条一个种类) |
| `Adm.CrossA`, `CrossPrA` | 拷贝: 同一层号两个证据, 前提相干 |
| `Adm.IncA`, `CohI`, `RaiseA′` | 族增量, 族相干, 更新 (七条律) |
| `Adm.RaiseA1` | 单个增量的更新 (对照) |
| `e₂`, `e₃`, `eω`, `eω′`, `eA`, `L₀`, `κ₂`, `κ₂′`, `κω`, `κω′`, `κA`, `pω` | 最小实例 |

接口自定稿后未改 (变更记录为空).

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `LevC′`, `cmpKC′`, `botBdC′` | ColimAKS | 拉回是 `KS`; 接口 `CmpKC`, `BotBdC` 的实例; 一切 `S`, $X$, $w$ | 定义/定理 |
| `globA`, `globPrA` | ColimAKS | 种类的界/第一位置 = 它的 (层号, 证据) 处的 | 定理 (`refl`) |
| `lgGA→`, `≤GA→`, `≤GA-rf`, `W₀`, `lgW₀`, `cohW₀` | ColimAKS | 整体合法/世界序推出每一级; 最小世界合法相干 | 定理 |
| `⊲-map`, `restr-move`, `crossA`, `crossPrA` | ColimAKS | 相干世界里拷贝的界/第一位置互推 | 定理 |
| `copyω`, `copyω←`, `copy₂` | ColimAKS | 实例: `κω`↔`κω′`, `κ₂`→`κ₂′` (相干世界) | 定理 |
| `noCrossA`, `¬cohWbad` | ColimAKS | 不相干的合法世界里 `κ₂`, `κ₂′` 的界不互推; 那个世界不相干 | 定理 (否定, 只说不加相干时认同不成立) |
| `no-retractA` | ColimAKS | `no-retract` 对 `LevC′` | 定理 |
| `shapeA′`, `¬localA′`, `illegal-W₂A`, `legal-sameA` | ColimACopy | 形状成立, `LocalLg` 不成立; 前提可满足 | 定理 (否定只说这一个形状) |
| `decA` | ColimARaise | 同一合法界下两个可入层号的相等可判定 | 定理 |
| `raiseA′` | ColimARaise | 一切 `S`, 合法 $X$, $w$: `RaiseA′` 七条律 | 定理 |
| `raiseA′-wα` | ColimARaise | `∀ α → RaiseA′ x₀ (wα α)` | 定理 |
| `uip→raiseA1` | ColimARaise | `UIPS → RaiseA1` | 条件定理 (UIP) |
| `topA`, `Lg-topA`, `topF`, `cohTop` | ColimARaise | 一致的族增量 (每个后继层号之上的第一个 Ω) | 定理 |
| `W₁`, `lgW₁`, `grow₁`, `cohW₁`, `cell₂`, `cell₂′`, `root₂` | ColimARaise | 层号 `finH 1` 一步回灌 | 定理 |
| `Wω₁`, `lgWω₁`, `growω₁`, `cohWω₁`, `cellω`, `cellω′`, `rootω`, `offω` | ColimARaise | 第一个无限层号 `up ω₀` 一步回灌; 别的层号不动 | 定理 |
| `sA`, `sω`, `Wn`, `Wωω`, `lgWn`, `lgWωω`, `cohWn`, `cohWωω`, `Wn≤`, `Wn≤ω`, `celln`, `cellωω`, `cellωω′` | ColimARaise | `up ω₀` 上的 ω 条 | 定理 |
| "`raiseA-sep` 那样的论证对本接口不存在" | — | 元层, 见判决 | 判断 |
| "单个增量不加 UIP 写不出" | — | 未证, 未否定 | 判断 |
| 第一个障碍两条 | — | 见判决 | 判断 |

## 前提实例

- `raiseA′` 的前提 `LgW S w`, `LgB X`: 最小实例 `Lg-wω`, `Lg-Ωtop S₀`; 族 `Lg-wα α` (一切 α).
- `crossA` 的前提 `CohA W`: `cohW₀`, `cohW₁`, `cohWω₁`, `cohWn n`, `cohWωω`.
- `noCrossA`: 世界 `Wbad` 合法 (`lgWbad`), 前提的一半 `bad₂` 成立.
- `legalA` 的前提 `∀ p → LgB (δ y₀ p)`: `Lg-topA`, `Lg-sA`, `Lg-sω`; `cohA` 的前提 `CohI`: `cohTop`, `refl`.
- `uip→raiseA1` 的前提 `UIPS`: `S = S₀` 时即 `AdmWCoh.UIPᴴ`, 由 `AdmWUip.fe→uip` (条件: Funext) 给出; 一般 `S` 没有给实例 (判断: 有 K 的模型里成立).
- `¬localA′`: 形状 `shapeA′` 是闭项; 共用世界合法的实例 `legal-sameA`.

## 翻译账

本路不读记号. 新定义:

| 定义 | 来源 | 归类 |
|---|---|---|
| `GWA X w` (只对可入层号给分量) | 作者原话; 诊断 §2.2 W⁺; 由 `ColimWNeg.raiseA-sep` (裸层号上的世界分出 $y_0$) 逼出 | 树侧 |
| `LevA w` (Ω-并只取有界坐标) | 由 "`restr` 要对一切坐标给分量, 有界不可判定" 逼出 (接口文件头, 判断; 另一出路 `SupB` 有 `AdmWCoh.¬cmpK`) | 树侧 (壁垒规则 "比较要字面公共上界" 用在种类族上) |
| `restrA` 沿路径, `lvlA` 带证据 | `ColimWIf.restr`, `lvl` 加证据 | 脚手架 (序数值不需要) |
| `CohA` | `noCrossA` 逼出 (定理) | 树侧 (世界的相干) |
| `IncA`, `CohI`, 族增量的 `incA` | `LocUipIf.Inc` 的可入版; 由单个增量的 UIP 墙 (`AdmWCoh`, `LocUipNegLoop`) 逼出 | 脚手架 (类型论的要求) |
| `topA` | 实例用的一致族 ("之上的第一个 Ω", `Ωtop`) | 测试数据 |
| `RaiseA′` 的形状 ("在一个层号上接长, 别处不动") | 沿用 `ColimWIf.RaiseG`, 根子在 `HtTowerFFold.RunM` (诊断 §4 (i) 的翻译痕迹); 本路没有去掉它, 只把律的定义域改成可入 | 沿用的翻译痕迹 |

没有新构造子; 没有读自记号基本列规则的字段; 没有闭包定理, 没有验收, 没有标签. 这一步: **摆脱侧** (去掉 "世界是裸层号上的函数" 这一条), 不加深翻译; 提供信息: `noCrossA` 划出 "以证据为参数的世界没有相干就认同不了", `uip→raiseA1` 与 `raiseA′` 的对照划出 "墙在单个增量, 不在可入更新".

## 审计

- 编译: 从仓库根 `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/ColimA.lagda.md +RTS -M6G -RTS`, 退出码 0 (五个文件; 接口单独编译退出码 0).
- 导入闭包 (`importclosure.py OCF.Align.ColimA`, 另跑 `--only OCF.Align. --only OCF.BTBO`): 29 个模块 (本地 19: `AdmWNegCopy`, `ColimA*` 五个, `ColimWCopy`, `ColimWIf`, `ColimWKS`, `ColimWNeg`, `ColimWRaise`, `CumReadCF`, `HtFeedTree`, `HtTowerCont`, `HtTowerNeg`, `HtTowerTy`, `HtTowerU`, `StallDxBdec`, `OCF.BTBO`), 禁用表 0, 退出码 0. 接口 `ColimAIf` 的闭包 17 个模块 (本地 7), 禁用表 0.
- 定义级切片 (`depslice.py`, 同一个 `--html` 目录): `ColimAKS:LevC′` 71/0/0, `ColimAKS:globA` 77/0/0, `ColimAKS:crossA` 78/0/0, `ColimAKS:noCrossA` 96/0/0, `ColimACopy:¬localA′` 113/0/0, `ColimARaise:raiseA′` 122/0/0, `ColimARaise:raiseA′-wα` 133/0/0, `ColimARaise:uip→raiseA1` 132/0/0, `ColimARaise:cellω` 140/0/0, `ColimARaise:cellωω` 141/0/0, `ColimARaise:Wn≤ω` 141/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58.
- 禁用构造: 无 postulate, 无洞, 无 TERMINATING/NON_TERMINATING/NO_POSITIVITY, 无 trustMe, 不开 K, 无 Funext; UIP (`UIPS`) 只作 `uip→raiseA1` 的前提.
- 文件行数 (总行 / 非空代码行): `ColimAIf` 249/145, `ColimAKS` 193/116, `ColimACopy` 57/37, `ColimARaise` 331/203, 入口 `ColimA` 约 104/6.
