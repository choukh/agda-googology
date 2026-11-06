# 第十七轮的否定一路: 入口

> **判决: 否定成立 (`RkSoundT` 与不带时间条件的 `RkSound`; `Laterᵈ` ⇒ `DomL` 一律; 动作限制的一条封闭律); `NKp` 未找到否定.** 对着接口 [StrRel17If](StrRel17If.lagda.md) 写 (定稿 2026-11-05 12:12, §1–§4; 12:43 的变更记录是文字补注, 不改定义, 本文写完后对着补注后的版本重编, 退出码 0). 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 不改任何已有文件, 不改接口与 `StrRel17` 前缀的文件. 实例都在 $\Lambda_2=2$ 上 (没有 $\Omega$-极限), 时间关系的封闭性对一切 $\Lambda$.
>
> **对纲领与目标意味着什么 (判断).** 全部是第 4 层 (关系与语义) 的结论, 不碰树、折叠、合法性. B1 ("带时间关系的语义") 想用 "再折叠时的状态支配产生时的状态" 救 `rk⁺` (链极限 ≤ 节点). 编译的结论是: **状态上的时间条件不够.** `rk⁺` 一对输出的左边 (上升的链极限) 在产生时就运行完, 右边 (保留的节点) 的分支要到换世界之后才运行, 而 `cv` 把第 $0$ 层累计清零. 只要产生时的动作读累计, 两边就在值上分开, 哪怕再折叠的状态就是产生时的状态本身 (`¬RkSoundT`). 不带时间条件时, 连不读状态的常数动作也分得开 (`¬RkSound`). 这一缺陷与 `NegSR16` 的 `¬semNK` 同源 (都是 "差保留, 累计被 `cv` 清零"), 这次落在 `rk⁺` 上. 没有推出 LPO/WLPO 或判定.

## 1 定理表

| 名字 | 文件 | 陈述 | 档 |
|---|---|---|---|
| **`¬RkSoundT`** | [NegSR17RkT](NegSR17RkT.lagda.md) | `¬ RkSoundT hz (hs hz)` ($\Lambda_2$) | **否定 (定理, 值)** |
| `preP`, `jYP`, `laterP`, `domP`, `relRef`, `lowOL` | NegSR17RkT | 前提全部成立; 再折叠状态 = 产生时状态 (`Later`, `DomL` 都成立); 左边 $\ge z_P+1$ | 定理 (前提可满足) |
| `_≈_`, `sum≈`, `Cong.run≈`, `refR≈`, `orEq` | NegSR17RkT | 无节点树的逐点结构相等; `Run` 对它的同余; 右边的再折叠与再折叠状态的累计无关; 保留输出不依赖产生时的累计 (`refl`) | 定理 (工具) |
| **`¬RkSound`**, **`¬sem∀`**, `¬semLR`, **`¬semᴺLR`** | [NegSR17Rk](NegSR17Rk.lagda.md) | `¬ StrRel16If.RkSound hz (hs hz)`; "`RelX⁺ hz (hs hz)` ⇒ `SemX²⁺`" 不成立; `SemXᴺ` (动作 `ActNZ`) 也不成立 | **否定 (定理, 值)** |
| `relLR`, `pre`, `jYN`, `RK.le`/`ge`/`riseLe`/`riseGe`, `lowL`, `upR`, `gap`, `¬valRef` | NegSR17Rk | 前提与值的计算 | 定理 |
| `¬domEx`, `domOK`, **`valOK`** | NegSR17Rk | 上一行的反例违反 `DomL`; 换成满足 `DomL` 的再折叠状态, 同一对的值是对的 | 定理 |
| `later⊕`, `laterᵈ⊕`, `laterᵈcv₀`, `laterᵈcv`, `laterᵈKb` | [NegSR17Time](NegSR17Time.lagda.md) | `Later` 对 `⊕` 封闭; `Laterᵈ` 对 `⊕`, `cv` (沿路径复合), `Kb` 的状态形状封闭 (一切 $\Lambda$) | 定理 (正面) |
| `inv0`, **`¬domCv`** | NegSR17Time | 产生时累计非 `n0` ⇒ 任何 `cv q Y′` 都不满足 `DomL` (一切 $\Lambda$) | 定理 |
| **`¬domFromLaterᵈ`** | NegSR17Time | "`J²⁺ Y₀ Y′` 且 `Laterᵈ q Y′ Y₂` ⇒ `DomL Y₀ Y₂`" 不成立 (闭项状态 $Y_1$ 换到世界 $1$) | **否定 (定理)** |
| `actNZ-Act`, `lead-run`, `actNZ-Ai`, `zPos` | [NegSR17Act](NegSR17Act.lagda.md) | `Act` 满足 `ActNZ`; `Lead1` 分支的 `Ai` 继承 `ActNZ`; `NKp` 的条件下 `nκ` 运行时累计字面非零 | 定理 (正面) |
| `hawL`, `keptL`, `brZero`, **`¬actNZ-kept`**, **`¬keptNZ`** | NegSR17Act | `HAWᴺ` 的产生时动作 (`AL`, `C1`) 下, 保留输出的节点的分支为 `n0`, 它的分支动作在一切再折叠动作下违反 `ActNZ`; 封闭律 `KeptNZ` 不成立 | **否定 (定理)** |

## 2 每条律为什么是构造一路需要的

- **`RkSoundT`** (接口 §3): B1 的核心; `rk⁺` 是 `RelX⁺` 里唯一能推出 "链极限 ≤ 节点" 的规则 (`StrRel17Obs.invNi`), 构造一路的 "`RelX⁺` ⇒ 语义" 要它. `StrRel17Time.valT` 是它在动作 `Act`、一个再折叠目标对上的正面实例.
- **`RkSound`** (`StrRel16If` §6): `StrRel16Sem.Zero⁺.semX0⁺` 与 `StrRel16Node.ZRk` 的条件. 它不成立说明时间条件确实需要; 反例违反 `DomL` (`¬domEx`), 换成满足 `DomL` 的状态值就对了 (`valOK`).
- **`Laterᵈ` ⇒ `DomL`**: 接口 §1–§2 说 "由字面的时间关系推出 `DomL`". `rk⁺` 的输出在目标的世界里被再折叠, 中间经过 `cv` (`BNi`, `Kp`, `Kb`, `κc` 都先 `cv`), 折叠的字面给出的是 `Laterᵈ` (`laterᵈcv`, `laterᵈKb`), 构造一路要从它得到 `DomL`.
- **`KeptNZ`**: `NKp` 只在 `SemXᴺ` (动作 `HAWᴺ`) 下成立; 节点的语义沿链以分支动作 `Ai` 运行, 保留的输出是新节点, 日后再折叠时链的动作是它的 `Ai`; 要在那里用 `NKp`, 这些 `Ai` 要满足 `ActNZ`.

## 3 前提实例

全部是编译过的定理, 没有空真的否定: `preP`/`pre` (`RkPre` 的六项), `TX` 对 `(cp00 , u∞ s∞)`, 种类 `refl`; 再折叠一侧 `cp00`, `hawC1⁺`/`hawC1ᴺ`, `n0⁺`, `jYP`/`jYN`, 目标对 `(cp00 , s∞)`; `DomL` 由 `jYP` 给出 (`domP`), `Later YP YP` 是 `laterP`. `¬domFromLaterᵈ`: `hY₁⁺`, `laterᵈcv₀`. `¬keptNZ`: `hawL`, `actNZ-Act`.

## 4 只否定什么, 不否定什么

- **否定**: (a) `RkSoundT hz (hs hz)` 的字面陈述 (产生时动作取遍旧 `HAW²`, 再折叠动作取遍 `HAW²⁺`); 反例的产生时动作 `Az` 读第 $0$ 层累计. (b) `StrRel16If.RkSound hz (hs hz)`, 以及 "`RelX⁺` ⇒ `SemX²⁺`" 与 "`RelX⁺` ⇒ `SemXᴺ`" 在层对 $(0,1)$ 上; 反例的产生时动作是常数 `C1`. (c) "`J²⁺` 加 `Laterᵈ` ⇒ `DomL`". (d) `ActNZ` 经保留输出传到分支动作的封闭律.
- **不否定**: 把产生时动作限制为不读累计的一类 (例如只用 `Act`) 之后的 `RkSoundT` (`StrRel17Time.valT` 是那一类在一个目标对上的正面结果; 判断: 有 $\Omega$-极限时, 分支含 `nκ` 的节点的 `Ai` 读累计, 这一限制不是折叠自动满足的, 未编译); 右边保留的再折叠目标对上的问题 (`StrRel17Obs`, 结论关系的形状, 与本文无关); 只比差分量的时间条件 (`DomL` 去掉累计) 下的 `rk⁺` 可靠性 (未比较值); `NKp`, `NKpV` (见下).
- **`NKp` (修补后的 "ni 对 nκ"): 未找到否定.** 它的前提 `SemXᴺ (ni r u) (v′ self)` 是一对节点的语义, 而节点的语义在左升右留的目标对上要 `RelX⁺` 关联 (`nl …`, `ni …`), 那只有 `rk⁺` (`StrRel17Obs.invNi`); 现有文件里没有任何节点对的无条件语义, 所以本文给不出满足全部前提的实例, 也就写不出值的反例. 判断 (未编译): (i) 节点的坐标层之下没有 $\Omega$-极限时, 节点的输出不读累计, 而 `NKp` 的条件使 `nκ` 的第 $0$ 格至少走一步并在那里运行 `v′ self` (`zPos`), `NegSR16` 的机制被挡住; (ii) 坐标层之下有 $\Omega$-极限时, 左边的节点在累计未清零的状态上运行, 右边的 `v′ self` 在 `cv` 之后运行, 机制与 `¬RkSoundT` 同源, 可能有值的反例, 但要先有节点语义的实例.
- 没有推出 LPO/WLPO 或判定; 否定都是 "这条律在可满足的前提下是假的" 一类.

## 5 修补的方向 (判断, 未试)

`¬RkSoundT` 与 `NegSR16.¬semNK` 的共同点: 差分量 `d` 经 `cv` 保留, 累计 `z` 被清零, 而某一边 (链, 或 `nκ` 的格) 在清零之前读了累计. 可能的出路: (a) 语义里把动作限制为不读累计 (`d`-only), 并检查折叠里的 `Ai` 是否满足 (有 $\Omega$-极限时要看 `nκ` 的回灌); (b) 让保留输出的分支在产生时就带上累计 (改折叠, 第 4 层不能做, 要交作者); (c) 时间条件里加 "右边保留的分支运行时的状态" 与 "左边产生时的状态" 的关系 (不是再折叠的状态). 交构造一路定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSR17 where

open import OCF.Align.NegSR17Rk public using (¬RkSound; ¬sem∀; ¬semLR; ¬semᴺLR; ¬domEx; domOK; valOK; relLR)
open import OCF.Align.NegSR17RkT public using (¬RkSoundT; preP; jYP; laterP; domP; relRef; refR≈; orEq)
open import OCF.Align.NegSR17Time public using (module Clo; ⊲-assoc; DomFromLaterᵈ; ¬domFromLaterᵈ)
open import OCF.Align.NegSR17Act public using (actNZ-Act; lead-run; actNZ-Ai; zPos; hawL; ¬actNZ-kept; KeptNZ; ¬keptNZ)
```

## 6 审计

- **冷编译** (2026-11-05): 删掉本组 `.agdai` (逐个写模块名: `NegSR17Act`, `NegSR17Rk`, `NegSR17RkT`, `NegSR17Time`, `NegSR17`; 未动 `StrRel17*`), 从入口重编: 退出码 0, 约 6 秒, 峰值常驻约 1.1 GB (`-M8G`). 代码块里 `postulate`, 洞, `TERMINATING`, `NON_TERMINATING`, `NO_POSITIVITY`, `trustMe`, `Funext` 都是 0, 不开 K.
- **导入闭包** (`importclosure.py`, `--only` 同 `StrRel14Neg`/`StrRel16` 的前缀表加 `OCF.Align.NegSR17`): 入口闭包 82 个模块 (本地 72, 库 10), 禁用表 0, `--only` 之外 0.
- **定义级切片** (`depslice.py`): `¬RkSoundT` 270 块, `¬RkSound` 255, `¬sem∀` 255, `¬semᴺLR` 250, `valOK` 227, `¬domFromLaterᵈ` 198, `¬keptNZ` 199, `zPos` 186; 记号模块 0, 记号词 0. 正对照 `Om1HnAccept:label-term₀` 1188 块, 记号模块 92, 记号词 58. 切片看不见模块应用, 块数偏少; 记号无关由导入闭包保证.

## 7 账

| 文件 | 行 (代码, 去空行与注释) | 内容 |
|---|---|---|
| `NegSR17Rk` | 174 | 常数动作下的值不变 (`RK`), `¬RkSound`, `¬sem∀`, `¬semᴺLR`, `¬domEx`, `valOK` |
| `NegSR17RkT` | 237 | `≈`, `Cong.run≈`, `lift`, `liftMono`, 三层实例, `¬RkSoundT` |
| `NegSR17Time` | 58 | `Later`/`Laterᵈ` 的封闭性, `¬domCv`, `¬domFromLaterᵈ` |
| `NegSR17Act` | 74 | `actNZ-Act`, `actNZ-Ai`, `zPos`, `¬actNZ-kept`, `¬keptNZ` |
| 入口 | 6 | |
| 合计 | 549 | 全部手写; scratch 里的草稿 (`D1`–`D3`) 按段落搬入, 没有生成脚本入库 |

## 8 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `¬RkSoundT` 的机制 | `RKi` 的 rise 句在产生时运行链, keep 句的分支经 `BNi` 在 `cv p Y` 之后运行; `cv` 的字面清零累计 | 树逼的 (否定) |
| `¬RkSound` 的机制 | 链从产生时的读数起, 再折叠时从再折叠的读数起 (`Chn` 的字面) | 树逼的 (否定) |
| `≈`, `Cong.run≈` | `Run` 对 `⨾`, `nl`, `nw` 的字面, `Rpt` 的状态与上下文 | 树逼的 (工具) |
| `laterᵈcv`, `¬domFromLaterᵈ` | `cv` 的字面 (`tg↑`, 累计置 `n0`); `⊲-tr` 的结合律 | 树逼的 |
| `¬keptNZ` | `ActNZ` 只看第 $0$ 层目标; `RKi` keep 句的分支是产生时动作在保留目标上的输出 | 树逼的 (否定) |

**归类: 提供信息.** 没有新构造子或节点字段, 没有改树、折叠、合法性, 没有 `Lab`, 没有记号. 否定划出: 以状态为对象的时间条件不能保证 `rk⁺` 的可靠性 (保留的分支在 `cv` 之后运行); 不带时间条件更不行; `Laterᵈ` 推不出带累计的 `DomL`; 只看第 $0$ 层的动作限制不经保留输出传下去.
