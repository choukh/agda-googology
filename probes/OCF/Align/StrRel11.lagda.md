# 结构关系, 第十一轮: 对层递归的关系族直接写在主线上: 入口

> **判决: PARTIAL.** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 没有改任何已有文件, 没有改树与折叠.
>
> 1. **(否定, 定理) `SumOneFold` 上带对齐的目标对经不起 `cv`** (`StrRel11CvNeg.¬cv-al`). 交接单第 1 项要 "`R∀` 只在带 `Al` 的目标对上取读数关系" (由 `StrRel10Kp.¬nw-tgt` 逼出). 在 `SumOneFold` 上, 对任意满足 "0 在下" 与最弱值可靠性的读数关系族, 这样的 `R∀` 经 `cv` 保不住 (前提可满足: $W\le W'$, `cv` 路径逐步对齐, 领先量, `Lg` 等式). 原因是 `SumOneFold` 的目标 `(t ⊲ W) ⊎ (W ⊲ t)` 在 `cv` 时要经 `cmpF` 重新分类. 与 `¬nw-tgt` 合起来: 在 `SumOneFold` 上, 读数关系对一切目标对取不行, 只对对齐的目标对取也不行. **所以第 1, 2 项不在 `SumOneFold` 上做, 直接做在主线 `HtFeedFold` 上** (第 4 项与之合并).
> 2. **(定理) 主线上的对齐路径对与目标对** (`StrRel11Tg`). `APair` = `snd-nwA` 的四个前提 (对齐, 底端领先量, 两条 `Lg` 等式), 对 `self` 与复合封闭 (`ap-self`, `ap-tr`). 推论对任意读数关系族: `cvR` (主线的 `cv` 只接长目标路径, 对齐的 `R∀` 经它保持), `advR` (`⊕`), `kpR`/`kp-nw` (`Kp` 的状态 `cv wu Y` 与上下文 `nw wu w` 要的正是目标对的对齐, 即 `¬nw-tgt` 说缺的那件), `stack` (交接单第 3 项在主线上的形式: `Kb` 叠起来的路径 `⊲-tr wu p` 的对齐 = 目标对与分支对的复合).
> 3. **(定理) 两世界上节点读数的种类一致** (`StrRel11Rk.rk-agree`): 同一坐标层, 同一目标层, 两个世界上 `rkT` 同为 `rise` 或同为 `keep`. 只用 "第一位置的严格部分不成环" (`irr`), 不比较值.
> 4. **(定义 + 定理) 对层递归的关系族与语义** (`StrRel11Le`, 交接单第 1 项). `Rel L` 对一切层 (含 `hl`, `hΩ`) 定义, 坐标关系由更低层的 `Rel` 经左边节点的位置给出 (`Below`/`RelS`/`RelAt`, 对层结构递减; 节点规则的前提是 "坐标相关 ⇒ 分支相关", 若坐标关系是同一个归纳族, 它出现在箭头左边, 不严格正 (判断), 所以对层递归). 规则: `n0`, `n1`, `⨾`, `nl`, `pr`, 对齐的 `nw` (`nwAᴸ`), 节点 (`niᴸ`, 两边 `StH` 可不同, 坐标层相同, 只取对齐的分支对), `nκ` (`κᴸ`, 只取对齐的分支对). 语义 `SemL L`: 两世界, 对齐的运行路径对, 动作对前提 `HA L` (**上下文按 `Rel L` 相关 ⇒ 输出相关**), 状态与输出在一切对齐的目标对上按 `Rel` 相关. **与层无关的六条规则对一切层成立** (`sem-n0`, `sem-n1`, `sem-⨾`, `sem-nl`, `sem-nw`, `sem-pr`, 一个证明对一切层, 无前提).
> 5. **(否定, 定理) `Ωᴴ` 处同层节点规则收不下 $\Omega_\Omega$ 的自比** (`StrRel11Om.¬rel-Ω`): `Rel Ωᴴ (Ωd Ωᴴ {0}) (Ωd Ωᴴ {1})` 是空的, 因为对齐的分支世界对 $(1,2)$ 上两个节点的坐标层是 `emb 1` 与 `emb 2`. 只否定这一族规则.
> 6. **(暂停) 节点与 `nκ` 两条规则的可靠性, `Ωᴴ` 处的 `MonoStep`.** 没有做. 第一个障碍与剩下的清单见 §3.

## 0 模块

| 文件 | 内容 | 档 |
|---|---|---|
| [StrRel11CvNeg](StrRel11CvNeg.lagda.md) | `TA`, `R∀ₐ`, `CvStable`, `Bot`, `Snd`, `no-pair`, **`¬cv-al`** | 定理 (否定) |
| [StrRel11Tg](StrRel11Tg.lagda.md) | `APair`, `ap-self`, `ap-tr`, `TA`, `R∀`, `OA`, `cvR`, `advR`, `kpR`, `kp-nw`, `stack` | 定理 |
| [StrRel11Rk](StrRel11Rk.lagda.md) | `_⊑∞_`, `_⊏_`, `irr`, `mix`, `RkRel`, **`rk-agree`** | 定理 |
| [StrRel11Le](StrRel11Le.lagda.md) | `LeF`, `Rel`/`Below`/`RelS`/`RelAt`, `HA`, `SemL`, `sem-n0`, `sem-n1`, `sem-⨾`, `sem-nl`, `sem-nw`, `sem-pr` | 定义, 定理 |
| [StrRel11Om](StrRel11Om.lagda.md) | `ap12`, **`¬rel-Ω`** | 定理 (否定) |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel11 where

open import OCF.Align.StrRel11CvNeg public using (¬cv-al)
import OCF.Align.StrRel11Tg
import OCF.Align.StrRel11Rk
import OCF.Align.StrRel11Le
open import OCF.Align.StrRel11Om public using (¬rel-Ω)
```

## 1 交接单逐项

| 项 | 状态 |
|---|---|
| 1. `Le_t` 带层下标, `SemL_t` 对层递归, 动作前提读上下文, `R∀` 只取带对齐的目标对 | 定义做在主线上 (`StrRel11Le`, `StrRel11Tg`); 在 `SumOneFold` 上这个 `R∀` 形状被 `¬cv-al` 否定. 关系对层递归 (不是 "一个带层下标的归纳族": 那样节点规则的前提里同一族出现在箭头左边, 不严格正 (判断, 没有编译那个失败的版本); `StrRel10` 入口说 "严格正", 照本轮的读法不成立). 上下文关系用 `Rel L` 本身 (不是 `SemL`): 上下文是语法对象, 动作读它当坐标. 可靠性: 六条与层无关的规则已证; `niᴸ`, `κᴸ` 未证 |
| 2. `snd0`, `coh₀/coh₁`, `GoD` 推广到 "第 $k$ 层坐标 + 第 $t$ 层树" | `snd0` 的角色由 `SemL` 对一切层统一承担 (第 0 层不另写). `coh` (左边自洽) 只给传递规则用; 本族暂不带传递规则, 所以不需要. `GoD` (走法比较) 是 `κᴸ` 可靠性的核心, 未移植 |
| 3. `Kb` 的 `⊲-tr wu p` 归到 `snd-nwA` | 主线形式: `StrRel11Tg.stack` (目标对 ∘ 分支对), 加上 `sem-nw` 就是 `snd-nwA` 的主线版. 定理 |
| 4. 移植到 `HtFeedFold` | 与第 1 项合并 (理由: 第 1 条判决). `Kp` 在目标 `Tg W t m` 下的形状: 状态 `cv (wm T) Y`, 上下文 `nw (wm T) w`, 都由目标对的对齐收下 (`kpR`, `kp-nw`) |
| 5. `HtCrossInst.MonoStep` 在 `Ωᴴ` | 暂停. 第一个障碍是跨坐标层的节点比较 (`¬rel-Ω`, §3); 另外 `hs-reduce<′` 要 `Free`, 在 `Ωᴴ` 不成立, 本轮未处理 |

## 2 规则的形状从哪里来

| 规则或定义 | 逼出它的地方 |
|---|---|
| `APair` (对齐 + 底端领先量 + `Lg` 等式) | `StrRel9Nw.snd-nwA` 的四个前提; 主线上每个 `cv` 与 `nw` 都是 "一条路径加一个旧对象" |
| `R∀` 只取对齐的目标对 | `StrRel10Kp.¬nw-tgt` (对一切目标对不行); 主线 `cv` 的字面 (`tg↑`) 让它保持 |
| `niᴸ`, `κᴸ` 只取对齐的分支对 | `BNi` 的 `cv p`, `Kb` 的 `cv p`: `cvR` 要对齐; 不对齐时 `StrRel8Neg.¬nwˡ` |
| `niᴸ` 两边 `StH` 可不同 | 两个世界上 `rkT`/`Kup` 算出的证明项不同 (`rk-agree` 只保证种类) |
| 坐标关系沿左边位置递归 | 两边位置不同 (世界不同), 坐标先 `outS` 取出; 同 `MonoPort6Rel.CtxP` |
| `HA` 的上下文关系 | `Ai` 把收到的上下文当坐标交给分支 (`StrRel9` §3) |

## 3 第一个障碍与剩下的清单

**第一个障碍 (`Ωᴴ` 的 `MonoStep`), 定理加判断.** `¬rel-Ω` (定理): 在本族里两棵 `Ωd Ωᴴ` 不相关. 判断: 左边在世界 0 起步, 右边在世界 1 起步, 走法的对齐必然把左边的分支世界 $c$ 配给右边的 $c'>c$, 两个节点的坐标层不同 (`emb c` 与 `emb c'`). 所以需要一条跨坐标层的节点规则, 它的可靠性在 `hz` 目标上是 "坐标层 $k$ 的链 $\le$ 坐标层 $k'$ 的链", 在夹在中间的目标层上一边是链一边是节点. 这就是实例之内对一切可数高度 $k\le k'$ 的单调, 含极限高度 (`MonoL` 那一类, `MonoPort6` 未做). 所以 `Ωᴴ` 处的 `MonoStep` 不是 "两世界语义移植" 之后的一步, 它以一切可数高度上的实例内单调为前提.

**剩下的清单 (按依赖顺序).**

1. `niᴸ` 的可靠性 (同层). 需要: (a) `rk-agree` (已有); (b) `RelS`/`Below` 与 `Rel k` 的互换 (沿位置, 每步定义性; `outS ∘ inS` 要 `out-inS` 一类等式, 主线 `HtFeedTree` 里尚无, 要补); (c) `HA` 对 `Ig↾` 的搬运 (`ap-tr`); (d) **`Int` 的两世界单调**: `Rel k z z′ ⇒ Rel L (Int … z …) (Int … z′ …)` (`Int` 含 `ni` 句与 `nκ`/`IW` 走法, 两世界版的 `MonoPort6Int.IntMS`); (e) 字典序归纳 (良基证明 `AccY L` 只作终止度量, 语义对一切 `ac` 全称), 同 `MonoPort6Snd.sndS`. 链 (`rise`) 的起点读数在 `tg self hk lW` 上, 这一对目标是对齐的 (`ap-self`). 估计 (判断) 400 到 700 行, 其中 (d) 占一半.
2. `κᴸ` 的可靠性. 第 0 层目标: 格 (`κc`/`κΔ`) 的世界由 `sum-fst` 生成, 要 `genᴾ` 与 `GoD` 的主线版 (格路径的对齐, `adv-sum` 逐格给底端领先量); 别的目标: `Kp`/`Kb` 在目标世界上走, `kpR`, `stack` 已给出状态与路径的对齐, 走法比较仍要 `GoD` 的主线版. 估计 500 到 900 行 (多为照抄 `StrRel4Gen`, `StrRel4Pr`, `StrRel9Walk`, 换成 `HtFeedFold` 的 `Walk`).
3. 跨坐标层的节点规则 (上面的第一个障碍) 与它的可靠性; 然后 `Ωᴴ` 处的 `MonoStep`. 另需处理 `hs-reduce<′` 的 `Free` 前提 (换实例在 `Ωᴴ` 不成立; 或直接在实例 `hs Ωᴴ` 里证增长, 未试).

## 4 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `¬cv-al` 的反例 | `SumOneFold.cv` 的 `cmpF` 分类 | **树逼的** (否定) |
| `APair`, `ap-tr` | `snd-nwA` 的前提; 主线 `cv`, `nw` 的字面 | **树逼的** |
| `R∀`, `OA` 只取对齐的目标对 | `¬nw-tgt`; 主线 `Tg W t m` 的字面 | **树逼的** |
| `irr`, `rk-agree` | `RunNi` 对 `rkT` 的分情形, 两世界 | **树逼的** |
| `Rel` 对层递归, `Below` 沿左边位置 | 节点分支的类型 `Vs L r`; 严格正性 | **树逼的** (类型的递归形状) |
| `niᴸ`, `κᴸ` 只取对齐分支对; `niᴸ` 两边 `StH` 不同 | `BNi`/`Kb` 的 `cv`; 两世界的证明项 | **树逼的** |
| `HA` 的上下文关系 | `Ai` 读上下文 | **树逼的** |
| `¬rel-Ω` | `Ωd (hΩ g)` 的字面 (分支 $c$ 上坐标层 `g c`) | **树逼的** (否定) |

**归类: 提供信息.** 没有新构造子或节点字段 (关系的构造子不是树的), 没有改树与折叠, 没有 `Lab`, 没有记号. 六条规则的语义对一切层一个证明, 不为某一站加前提. 这一站新用到的字段: 主线目标的世界路径 `wm` (`cvR`), 节点 `StH` 的位置 (`Below`, `irr`), `hΩ` 的分支函数 `g` 作坐标层 (`¬rel-Ω`). 两条否定划出不能有的形状: `SumOneFold` 上的对齐 `R∀`; 同层节点规则下的 $\Omega_\Omega$ 自比.

## 5 审计与账

- 编译: 删掉本轮六个 `.agdai` 后从入口从头编译, 退出码 0 (六个模块都重新检查). 约 4 秒, 峰值常驻约 0.7G (`-M6G`). 无禁用构造: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY`, `trustMe` 都是 0; `Funext` 只在入口的讲解文字里出现一次. 终止全由结构检查给出 (`Rel`/`Below`/`RelS`/`RelAt` 对层与位置, `irr` 对层, `NL.go` 对 $n$).
- 导入闭包 (`importclosure.py`, `--only` 为 `OCF.Free.Level`, `OCF.BTBO`, `OCF.Align.` 下的 `CumReadCF`, `TLRule`, `TLOpsW`, `SumOne`, `HtGen`, `HtFeed`, `HtCross`, `MonoPort`, `KVal`, `KNest`, `StrRel`, `BrwMid`, `LayerTr`, `NoCumLit`, `L1Val`, `DVal`, `GenAbs`): 入口闭包 66 个模块 (本地 56, 库 10), 禁用表命中 0, `--only` 之外 0, OK.
- `depslice.py`: `¬cv-al` 到达 148 块, `cvR` 54, `rk-agree` 50, `sem-nl` 134, `sem-⨾` 128, `¬rel-Ω` 43; 记号模块块数都是 0, 别处记号词 0. 正对照 `Om1HnAccept:label-term₀`: 1188, 92, 58. 切片看不见模块应用 (本轮四个模块带参数 `Λ lΛ`), 块数偏少; 记号无关由导入闭包保证.
- 代码行 (代码块内非空, 去注释行): 入口 7, `StrRel11CvNeg` 89, `StrRel11Tg` 61, `StrRel11Rk` 89, `StrRel11Le` 114, `StrRel11Om` 27; 合计 387. 没有逐字沿用旧文件的大段 (`StrRel11Le` 的 `sem-⨾`, `NL` 与 `StrRel9Snd.sndᴸ` 的 `⨾ᴸ`, `nlᴸ` 两句同形).
