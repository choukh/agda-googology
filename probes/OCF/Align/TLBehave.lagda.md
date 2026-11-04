# 树能否从对象在折叠下的行动判断 "这一层走到头"

> **判决: 部分做到. 分四句, 档次不同.**
>
> 1. **有一个判据, 不看记号, 在 `WorldTH` 这一族里有分辨力 (定理).** 世界内的一切对象 (高度 `ht _`, 世界合法) 都不 `Ad` (`no-ad`), `T₁` 的对象 `Ad` (`top-ad`). 每个高度行折叠一次被下一行吸收 (`abs-row`, `abs-val`), 顶折叠一次不被任何一行吸收 (`no-abs-top`).
> 2. **不是值的判据, 而且单调的值判据分不开 (定理).** `T₁` 严格低于一个不 `Ad` 的高度行 (`blind`). 下闭的值谓词对一切高度行成立, 就对一切树成立 (`cap-trivial`). 所以 `cofinal`, `no-stop` 不伤这个判据: 回灌过了值, 还是不 `Ad`, 还是被吸收. **非单调的值谓词没有否定.**
> 3. **循环的程度 (判断).** `Abs₁` 只提第一位置, 不循环, 但它依赖语言里有没有下一格. `Ad` 不提 `top`, 对类型里一切对象证明, 但它说的 "读到的高度跟着世界走" 就是绑定做的事. 所以它是 **绑定的语义刻画**, 不是从别处独立推出 "必须加绑定". 我认为这是比上一轮的 "高度有界" 进了一步的地方: 现在有一条连接值的定理 `read-above`, 和对全部对象的否定 `no-ad`. 没有做到的是下一句.
> 4. **还差的.** "不 `Ad` 就过不去" 没有定理: 回灌能过任何树的值. `Target` 仍未走通, 判据不需要它, 但 "绑定带来的值超过回灌能到的值" 这句话需要它. `Cl ⊤` 仍然没有实例, 也没有否定.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

## 时间线

1. 前两轮看过 `fs-1`, `fs-2`, `lt-b`. 这一轮写定义时没有打开 `*Accept`, `EBO`. 读了 `WorldTHW`, `WorldTHLe`, `WorldTHGrow`, `WorldTHInst`, `WorldTH`, `CumReadBase`, `CumReadCF`, `ValueJudgeBase`, `ValueJudgeLadder`, `LadderOrdNeg`, `Om1Hn*` 的陈述. `WorldTH` 正文写了读法; 任务书提示了 "左极限, 第一支, 共尾度".
2. 写 `TLBehaveDef`, `TLBehaveThm`, `TLBehaveNeg`, 编译.
3. 最后写 `TLBehaveAccept`.

## 判据

- **`Abs₁ p`.** `Ω̇ p one` 是某个 `Ω̇ p′ azero` 的第一位置. 第一位置 `⊴` 蕴含值的 $\sqsubseteq^0$ (`M₀.tp₀`), 反过来不蕴含.
- **`Cov h`.** 闭包节点的分支读到的高度盖住分支所在的世界: `v ⊲ hA (hOf (h q g))`.
- **`Ad y`.** 沿第一位置走到一个 `Cov` 的闭包节点.
- **这一层走到头**: 每一行 `Abs₁`, 没有对象 `Ad`. 高度行的语言满足它 (`abs-row`, `no-ad`). 加上顶之后两条都破: 顶不 `Abs₁`, 顶 `Ad`.

**试过的方向 (依据是定义).** 左极限: `ψ₀⁰` 的每一行, 值都是读到的项的极限 (`fsC`, `ol`, `oi`), 高度行和顶都连续, 单看值分不开. 不连续在读到的 **下标** 上, 这就是 `read-above` 与 `read-fixed-*` 的差别. 共尾度: `Ω·2` 与 `u` 的记号共尾度相同 (`cof-Ω·2`), 树里 `ht (asuc q)` 与顶都是 `oc`, 也分不开.

## 定理 (编译过, 无条件)

| 定理 | 陈述 | 文件 |
| --- | --- | --- |
| `abs-row`, `abs-val`, `abs-row-strict` | 高度行折叠一次增长, 又被下一行第 0 层吸收 (第一位置, $\sqsubseteq^0$) | [TLBehaveThm](TLBehaveThm.lagda.md) |
| `no-abs-top` | 对一切高度 $p$ (含 `tφ f`): `Ω̇ top one` 不是 `Ω̇ p azero` 的第一位置 | 同上 |
| `no-ad`, `fold-world`, `em-not-ad` | 高度 `ht _`, 世界合法的一切对象不 `Ad`; 折叠到世界内目标的输出不 `Ad`; 常数不 `Ad` | 同上 |
| `rows-not-ad` | 高度行在世界 `one` 上不 `Ad` | 同上 |
| `top-ad` | 顶的一切层 `Ad` | 同上 |
| `read-above` | `Cov` 的闭包节点, 对任何赋值 `val`: 第 $i$ 个输出严格低于第 $i$ 次读到的高度的秩 | 同上 |
| `read-fixed-s`, `read-fixed-l` | 高度行读到的高度不依赖世界 | 同上 |
| `dom-ht`, `row-above` | 下标的秩不超过行的值; 一切树低于某个高度行 | [TLBehaveNeg](TLBehaveNeg.lagda.md) |
| `cap-trivial`, `T₁-capped`, `floor-trivial`, `blind` | 单调的值谓词分不开, 见文件头 | 同上 |
| `cof-Ω·2`, `cof-u` | **只关于记号** | [TLBehaveAccept](TLBehaveAccept.lagda.md) |

**否定的范围.** `no-abs-top`, `no-ad`, `rows-not-ad`, `em-not-ad`, `fold-world` 是对 `WorldTH` 这个语言的陈述. `no-ad` 的前提 `Gw u` 可满足 (`g₀`, `gnext`). `cap-trivial`, `floor-trivial` 的前提 $P=\top$ 满足, 它们只否定对值单调的判据. 这些都不否定绑定路线, 也不否定别的数据树里有不靠绑定的 `Ad` 对象: `no-ad` 只说高度是 `ht _` 的对象.

**一个注意.** `no-abs-top` 依赖 `Hg` 里顶之上没有下一格. 给 `Hg` 加上顶的后继, `Abs₁ top` 就可能成立; 这是 `WorldTH` 的下一步 ($\psi_0(\Omega_{\Omega^2+\Omega})$), 判断要加, 没有做. 那时判据的第一半对新语言又成立, 第二半要看新语言有没有闭合自己行族的对象.

`Abs₁` 只测 `one` 这一层: `Ω̇ (ht q) b` 对 $b\ge2$ 不是第一位置, 这里的吸收不覆盖它们. 没有证 $\sqsubseteq^0$ 版本: 世界 `m` 由 `mx` 规范给出, $b$ 不一定在链上.

## `Target` 和 `Cl ⊤`

- **`Target`: 判据不需要它, 但它没有被取代.** 判据是结构的, 它说 `T₁` 的对象与世界内的对象行动不同. "绑定带来的值超过回灌能到的值" 是另一句话, 只有 `Target` (或同族版本 $R(\mathrm{lv}\,T_0)\preceq T_1$) 能说. **仍未走通.** 差的还是跨族和右加单调: $\psi_0(\Omega_u+x)\succeq\psi_0(x)$. 右加单调到闭包节点时要比较 $\mathrm{next}\,\eta\,y$ 与 $\mathrm{next}\,\eta'\,y'$, 两者字面不可比, 所以它需要 `Mono` 型的值单调 (判断).
- **`Cl ⊤`: 没有实例, 也没有否定.** 这一轮没有新进展. 仍然条件于 `Mono` (`mono→row`) 加 `val (next M)` 的算术.

## 判断

- 这些判据只在 `WorldTH` 证了. `CrossM` 一族 (`T⊤`, `F`, `N`) 没有定义 `Ad`; 那边的对应事实是 `no-cofinal`, `top-new`, `no-world`. 判断是同样成立: 世界里的位置与值无关, 所以读到的高度不跟世界走. 没有编译.
- `T₊` 的 `tH` 判断是 `Ad` 的: 第 `e` 支在世界 $M'$ 顶上. 没有编译.
- `read-above` 与 `no-ad` 合起来的直观: 世界内的对象读到的高度有固定的上界, 折叠产生的值很快盖过它; 顶读到的高度总在已经产生的值之上.

## 翻译账

这一轮没有新增数据树字段, 没有新 `Good` 规则.

| 东西 | 来源 |
| --- | --- |
| `⊴`, `T-strict`, `row-mono`, `next`, `oc` | 已有, `WorldTH` 账上 `Hg` 的 `ht`, `top` 照 $\Omega\cdot a$, $\Omega^2$ 写 |
| `Abs₁` | 树逼的: 第一位置已有; 选 `one` 这一层因为 `oc` 的第一支就是它 |
| `Cov`, `Ad`, `hOf`, `rk` | 我的定义; 想到它受绑定启发, 见判决第 3 句 |
| 语言选 `WorldTH` | 因为它的顶有证书, 高度与下标同类, 能在一族内比较 |

**不算树自足.** 判据能在对象上检验, 但 "要加一个对象使 `Ad` 成立" 这一步, 树只说得出 "现在没有", 说不出 "必须".

## 壁垒

没有新的下标类型. `Ad`, `Abs₁` 只是谓词, 不作判定. `dom-ht` 的 `≼` 是陈述用的序. `barrier` 的前提不被要求.

## 工程

`TLBehaveThm` 峰值约 10.7G, 用时约 40 秒; 哪一条定义吃内存没有查. `TLBehaveNeg` 约 4 秒.

## 审计

记号只在 [TLBehaveAccept](TLBehaveAccept.lagda.md), 入口不导入它.

- **导入闭包:** `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.LadderNF --only OCF.Align.LadderMono --only OCF.Align.LadderInf --only OCF.Align.LadderOrd --only OCF.Align.CrossM --only OCF.Align.CrossNext --only OCF.Align.CumRead --only OCF.Align.LevelFix --only OCF.Align.WorldTH --only OCF.Align.ValueJudgeBase --only OCF.Align.TLBehave OCF.Align.TLBehave`: 退出码 0, 禁用表 0, `--only` 之外 0, 19 个本地模块. 正对照 `OCF.Align.TLBehaveAccept`: 命中 `EBO`, 退出码 1.
- **定义级切片 `depslice.py` (块数, 记号块, 词命中):** `no-ad` 99, 0, 0; `top-ad` 43, 0, 0; `no-abs-top` 53, 0, 0; `abs-val` 294, 0, 0; `read-above` 80, 0, 0; `cap-trivial` 366, 0, 0; `blind` 379, 0, 0. 正对照 `TLBehaveAccept:cof-Ω·2`: 25, 17, 1. 切片看不见模块别名的实参, 以闭包为准.
- **禁用构造:** 全部 `TLBehave*` 没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, `--cubical`; 全部带 `--safe --without-K`.
- 闭包只保证不引用, 不说明没受记号启发: `Cov` 的想法受绑定和前两轮读过的记号启发.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLBehave where

open import OCF.Align.TLBehaveDef public using (Abs₁; Cov; Ad; hOf)
open import OCF.Align.TLBehaveThm using (abs-row; abs-val; abs-row-strict; no-abs-top; no-ad; fold-world; em-not-ad; rows-not-ad; top-ad; read-above; read-fixed-s; read-fixed-l)
open import OCF.Align.TLBehaveNeg using (dom-ht; row-above; cap-trivial; T₁-capped; floor-trivial; blind)
```
