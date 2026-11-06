# 结构的、对折叠输出封闭的值关系: 入口

> **判决: HOLDS (在 `MonoPort2` 的范围内) + PARTIAL (接 `CellStep`).** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, **不用 `Funext`**, 没有验收文件.
>
> 1. **先找反例, 没有找到.** 逐句检查 `HtFeedFold` 在这一范围 ($\Lambda=2$, 世界固定, 分支只在 `self`) 里会走到的子句: `Run` 的 `n0`, `n1`, `⨾`, `nl`, `nw`, `ni` (`RunNi` → `RKi`), `RKi` 的 `keep` (输出节点, 分支是 `BNi`) 与 `rise` (链 `Chn`), `Ai`, `BNi`, `Rpt`. **没有一句要左边极限截断**: 每一句都把结构相关的输入 (连同坐标、状态) 送到由同名结构构造子相关的输出. `nκ` 不在这一范围 (第 1 层的关系里没有它). 所以没有否定定理可写; 结论是下面的正定理.
> 2. **结构关系, 对折叠输出封闭 (HOLDS).** [StrRelDef](StrRelDef.lagda.md) 的两层关系: 第 0 层 $\sqsubseteq_0$ 的构造子恰是 `KNest2` §3 列的那一组 (`n0 ⊑ z`, `n1`, `⨾`, `nl` 逐项, `nw` 两边, 部分和 `pr`, 传递, 单位, 结合), **没有 `lim-leP`/`lim⊑`**; 第 1 层 $\sqsubseteq_1$ 是 `MonoPort2Rel` 的关系去掉 `lim⊑`, 节点分支按 $\sqsubseteq_0$ 对齐 (不按值). [StrRelZero](StrRelZero.lagda.md) **`snd₀`** 与 [StrRelSound](StrRelSound.lagda.md) **`snd₁`**: 关系推出两个目标上的输出**都**结构相关 (`out₀`, `out₁`). 第 0 层读数的单调是推论 (`StrRelDef.val₀`).
> 3. **`MonoStep 2` 的第二个证明, 全程结构 (HOLDS).** [StrRelChain](StrRelChain.lagda.md) **`mono₂ˢ`**, `chainLeˢ`, `grow₂₃ˢ`: 不经 `DValCanon.Gen`, 不用左边极限截断. **值只在最后读出一次** (起点的底 $1\le b_0$ 与链的极限), 起点状态的比较是字面的 (单位律加 `n0 ⊑ z`), 不要按值对齐.
> 4. **首对齐 (HOLDS, 组合部分).** [StrRelHead](StrRelHead.lagda.md) **`head`**: $x\sqsubseteq_0 x'$ ⇒ 左边每个被走到的位置有右边的位置, 前缀 $\sqsubseteq_0$, 剩余长度 $\le$; **`headAdm`**: 起点 $v\le v'$ 时, 两层 $c\le c'$ 且 $\mathrm{Adm}(c,c';v+x,v'+x')$, 正是 `KNest2Glue.CellStep` 每一格要的领先量 (`KNestAdm.Adm`). 构造的, 对推导归纳.
> 5. **只由值求首对齐推出 LPO (否定, 编译过).** [StrRelNeg](StrRelNeg.lagda.md) **`vhead→LPO`**: 把 `KNest2` §3 的判断 "值的比较喂不进首对齐" 变成定理 (只杀 "只看值" 的做法).
> 6. **`CellStep` 本身: 未走通 (PARTIAL).** 缺两件, 都不是否定: (i) 桥: `SumOneFold.Walk` 沿 `sum-fst v d` 的递归 (对序数路径) 与 `Sp d` 的位置一一对应; (ii) `KNest` 的语义 `OutLeᴬ` 只给值, 要改成给出结构关系的输出, 下一格的坐标才有 $d_n\sqsubseteq_0 d'_n$. 本组给的是 (ii) 在 `MonoPort2` 范围 (无 `nκ`) 里的形状, 与首对齐的组合核心. 见 §3.

## 1 定义

    data _⊑₀_ : D hz V → D hz V′ → Set     -- 两边世界可不同
      z0 : n0 ⊑₀ x          o1 : n1 ⊑₀ n1          sq : x ⊑₀ x′ → y ⊑₀ y′ → x⨾y ⊑₀ x′⨾y′
      lm : (∀ n → d n ⊑₀ d′ n) → nl d ⊑₀ nl d′       wl, wr : nw 两边透明
      pr : x ⊑₀ x′ → (∀ n → d n ⊑₀ d′ n) → ∀ k → x ⨾ preL d k ⊑₀ x′ ⨾ nl d′
      tr (中间项与左边同世界), u0l u0r u1l u1r, al al′ ar ar′

    data _⊑₁_ : D (hs hz) W → D (hs hz) W → Set
      MonoPort2Rel 的 ⊑ 去掉 lim⊑; ni⊑ 的三条前提都是 ∀ z z′ → z ⊑₀ z′ → …

    SRel Y Y′ = o₀(d Y) ⊑₀ o₀(d Y′) × d₁ Y ⊑₁ d₁ Y′        Good Y = d₁ Y ⊑₁ d₁ Y
    Obs Δ Δ′  = o₀ Δ ⊑₀ o₀ Δ′ × o₁ Δ ⊑₁ o₁ Δ′
    HA0 A A′  = ∀ w w′ → w ⊑₀ w′ → ∀ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (A … w Y) (A′ … w′ Y′)   -- 第 0 层动作, 坐标结构相关
    HA₁ A     = ∀ w w′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → Obs (A … w Y) (A … w′ Y′)                   -- 第 1 层动作, 坐标不被读

与 `MonoPort2` 的差别, 每一条的来由:

- **第 0 层坐标按结构关系带着** (`HA0` 的 $w\sqsubseteq_0 w'$, `Sem0` 对一切这样的坐标): `n1` 那一句把坐标交给动作 `Ai`, `Ai` 用它选节点的分支 ($u(z)$); 分支按 $\sqsubseteq_0$ 对齐, 坐标就必须按 $\sqsubseteq_0$ 相关. 这是 `ni⊑` 改成结构对齐逼出的.
- **两个读数都结构** (`Obs` 在 $T_0$ 上是 $\sqsubseteq_0$): 节点在 $T_0$ 上上升的链 (`Chn`) 的下一个链点是上一个链点的 $T_0$ 输出, 链点又作坐标喂进分支. 输出若只按值比, 下一步的坐标就只有值, 又回到 `Gen`. 所以 $T_0$ 的输出要结构相关, 这是链的字面逼出的.
- **没有 `lim⊑`**: 检查完每一句折叠, 输出的关系只由同名构造子组成 (`nlᴰ` ↦ `lm`/`nl⊑`, `⨾ᴰ` ↦ `sq`/`⨾⊑`, `RKi rise` ↦ `lm`, `RKi keep` ↦ `ni⊑`, 部分和 ↦ `pr`/`pre⊑`). `lim⊑` 在 `MonoPort2` 里只为 `Gen` (值 ⇒ 关系) 而存在.
- `tr` 的中间项与左边同世界: `trS` 要在中间项上跑同一个动作, 要一条进入路径; 第 0 层的世界不起作用, 这个限制没有用处上的代价.

## 2 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `refl₀`, `nwd`, `nwd′`, `preL₀`, **`val₀`** | StrRelDef | 第 0 层自比; `nw` 分配; 结构关系推出值单调 (一切底) | 定理 |
| `S⊕`, `G⊕`, `asS`, `S0ˡ`, `S0ʳ`, `rfΩ`, `PreOut.O≡₀` | StrRelDef | 状态更新在两层上都结构 | 定理 |
| `Steps.*`, `alS` … `ar′S`, `trS`, `preS` | StrRelZero | 第 0 层每个构造子一步 (两个动作不同) | 条件定理 (动作 `HA0`) |
| `rS` | StrRelZero | 一切第 0 层树对一个动作自比 (对树归纳) | 条件定理 (`I`) |
| **`snd₀`** | StrRelZero | $z\sqsubseteq_0 z'$ ⇒ 两个目标上的输出结构相关 | 条件定理 (`HA0`) |
| **`chainˢ`** | StrRelZero | 节点上升的链, 链点结构相关, 输出 $\mathrm{nl}$ 逐项 | 条件定理 (`HA0`) |
| `⨾S` … `preS`, `branch`, `niS` | StrRelSound | 第 1 层每个构造子一步 | 条件定理 (`HA₁`) |
| **`snd₁`**, `out₀`, `out₁` | StrRelSound | $x\sqsubseteq_1 x'$ ⇒ (a) $T_0$ 输出 $\sqsubseteq_0$, (b) $T_1$ 输出 $\sqsubseteq_1$ | 条件定理 (`HA₁`) |
| `HA-Stepˢ` | StrRelChain | `StepA` 满足 `HA₁` | 定理 |
| `chainˢ₁`, **`chainLeˢ`**, **`mono₂ˢ`**, **`grow₂₃ˢ`** | StrRelChain | `ChainLe (hs hz)`, `MonoStep 2`, $T_2+1\le T_3$ | **定理, 无前提, 无 `Funext`** |
| `sum⊞`, `pt⊞`, `lsplit`, `tl-cons`, `dec`, `toNl`, `pre≡`, `remTo` | StrRelHead | 位置的拆分, 极限的拆分 | 定理 |
| **`head`**, **`headAdm`** | StrRelHead | 结构关系 ⇒ 首对齐, 领先量 `Adm` | 定理 |
| **`vhead→LPO`** | StrRelNeg | 只由值求对应位置 ⇒ LPO | **否定, 定理** |
| `CellStep` | — | 见 §3 | 未走通 |

**有限测试.** 无.

## 3 `CellStep`: 接到哪里, 缺什么

`KNest2Glue.CellStep` 的格是 "沿 $a\lhd W$ 在世界 $W$ 里逐层走分支", 第 $n+1$ 格的路径字面是 `sum-fst v_n d_n`, $d_n$ 是上一格的第 0 层输出. 本组给出:

- **若** $d_n\sqsubseteq_0 d'_n$ 且 $v_n\le v'_n$, **则** 左格被走到的每一层 $c=v_n+\mathrm{pre}\,s$ 有右格的一层 $c'$, $c\le c'$, 且 $\mathrm{Adm}(c,c';v_n+d_n,v'_n+d'_n)$ (`headAdm`). 这是 `KNest2` §3 要的 "两格坐标由不含左边极限截断的结构关系相关 ⇒ 首对齐".
- **折叠的输出满足这个前提**: 在 `MonoPort2` 的范围里, 输出的第 0 层读数结构相关 (`out₀`), 起点也只要结构关系 (`StrRelChain.sLR`).

**第一个障碍 (判断, 依据写在每条里).**

1. **语义要换成结构的.** `KNest` 一族 (`KValSound.OutLe`, `KNestSound.OutLeᴬ`) 的结论是值的 $\le$. 第 $n+1$ 格要的 $d_n\sqsubseteq_0 d'_n$ 是第 $n$ 格的输出关系, 值的结论给不出来 (`vhead→LPO` 说明不能事后由值补). 所以要把 `OutLeᴬ` 改成像本组 `Obs` 那样在第 0 层读数上给出 $\sqsubseteq_0$, 再带上领先量. 本组在无 `nκ` 的范围里做了这件事的形状; `nκ` 的回灌 (`κc`, `κΔ`) 是 `drp` 加 `sum`, 都是结构操作 (判断: 不会逼出左边截断).
2. **桥.** `SumOneFold.Walk` 对序数路径 $a\lhd b$ 递归, 不对树 $d_n$ 递归; 要证 "沿 `sum-fst v d` 走 ≈ 按 $d$ 的位置 `Sp d` 逐个走", 其中复合路径来自 `⊲-tr`, 极限的尾巴来自 `tailP` 与 `WRp` (下标是 $m+n$, 与本组 `drop` 的形状差一个命题等式). 这是计算上的工作, 没有否定的迹象.
3. **两个折叠不是同一个.** `CellStep` 在 `SumOne` 折叠上, 本组在 `HtFeed` 折叠上. 第 0 层的树经 `MonoPortBridge.toS`/`ofS` 定义性地对应, `Sp`, `head` 的移植是机械的.

估计 (判断): 1 与 2 合起来 600 到 900 行, 与 `KNest` 的估计同量级; 但现在对齐方式是确定的 (首对齐, 由推导给出), 不再要在 "首对齐还是恒等对齐" 之间按值选 (`KNest2` 入口第 4 条的 "树世界可比" 前提可能可以去掉; 未验证).

**与 `MonoPort3Gen` 的关系 (判断).** 主审转告: `MonoPort3Gen` 把和结构的十四步写成对关系抽象的引理. 本组 `StrRelZero` §2 与 `StrRelSound` §2 是独立写的 (同 `MonoPort2` 的骨架), 没有接它; 本组的关系满足它的 `OutLaws` 的形状 (输出关系取两层的积, 第 0 层坐标关系取 $\sqsubseteq_0$, 不用 `LimLaw`), 接上后估计可省约 250 行. 未做.

## 4 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| $\sqsubseteq_0$ 的构造子 | `KNest2` §3 由首对齐列出的结构律; `DValCanon.Gen` 的结构律去掉 `lim-leP` | 树侧, 由否定判断逼出 (`KNest2` §3, 现在有 `vhead→LPO`) |
| `ni⊑` 按 $\sqsubseteq_0$ 对齐 | 坐标是上一段的输出 (链) 或输出节点的变量 (`BNi`) | **树逼的** (折叠的形状) |
| 坐标按 $\sqsubseteq_0$ 带着 | `n1` 把坐标交给 `Ai`, `Ai` 选分支 | **树逼的** |
| $T_0$ 读数结构 | 链点是上一个链点的 $T_0$ 输出 | **树逼的** (`Chn` 的字面) |
| 去掉 `lim⊑` | 每一句折叠输出只用同名构造子 | 树侧, 逐句检查 |
| `Sp`, `pre`, `rem`, `drop` | 一格的层就是树里 `n1` 的位置; 领先量是剩余长度 | 树侧, `KNestAdm.Adm` 的形状 |

**按 `AGENTS.md` 归类: 提供信息.** 没有新构造子或节点字段, 没有改树、折叠、`View`; 没有 `Lab`, 没有记号. 一步定理: `snd₀` 对一切动作对, `snd₁` 对一切动作, `head` 对一切推导; 这一站新用到的字段: `RKi` 的 `keep`/`rise` 两支、`Chn` 的链点 (第 0 层输出作坐标)、`BNi` 的坐标变量. 否定定理划出不能有的: "只由值对齐" (`vhead→LPO`). **脚手架** (判断): 自比的子推导与 `Good` 的跟踪仍在 (同 `MonoPort2`, "第 1 层不是一切树自比" 逼出); 第 0 层的自比由树归纳 (`rS`) 给出, 不进构造子. 去掉了 `MonoPort2Zero` §4 的 `Gen` 套用 (约 50 行) 与 `limS`/`lim-leP` (约 90 行), 加了坐标的结构比较 (约 30 行). 与 `MonoPort2` 的和结构部分重复, 见 §3 末.

没有序数值验收 (无参照树), `grow₂₃ˢ` 只说明不塌缩.

## 5 审计

- **编译**: 删掉本组自己的 `.agdai` 后从头编译入口, 退出码 0 (约 8 秒); 共享模块没有用 `--ignore-interfaces`.
- **禁用构造**: 七个文件无 `postulate`, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不用 `--cubical`, 不出现 `Funext`.
- **导入闭包** (`importclosure.py`, `--only` 同 [MonoPort](MonoPort.lagda.md) 加 `OCF.Align.StrRel`): 都是退出码 0, 禁用表 0, `--only` 之外 0.

| 模块 | 闭包 (本地) | 闭包里有 `DValCanon`/`MonoPortZero`/`MonoPort2Zero` |
|---|---|---|
| `StrRelDef` | 20 (10) | 无 |
| `StrRelZero` | 21 (11) | 无 |
| `StrRelSound` | 22 (12) | 无 |
| `StrRelHead` | 21 (11) | 无 |
| `StrRelNeg` | 22 (12) | 无 |
| `StrRelChain` | 44 (34) | 有 (经 `MonoPortStep` → `MonoPortOne`, 只为陈述 `MonoStep` 与 `step≡`) |
| 入口 | 57 (47) | 有 (同上, 另经 `KNestAdm`, 只为 `adm≡`) |

  所以 "关系与可靠性不经规范形 `Gen`" 对 `Def`, `Zero`, `Sound`, `Head`, `Neg` 是**编译器保证** (闭包里没有); `StrRelChain` 只在模块粒度上带进来, 定义级切片见下.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 别处记号词): `StrRelChain:mono₂ˢ` 250/0/0, `StrRelChain:grow₂₃ˢ` 331/0/0, `StrRelChain:chainLeˢ` 241/0/0, `StrRelSound:snd₁` 199/0/0, `StrRelZero:snd₀` 168/0/0, `StrRelHead:head` 57/0/0, `StrRelHead:headAdm` 65/0/0, `StrRelNeg:vhead→LPO` 82/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片是语法级的.

## 6 账

| 文件 | 代码行 | 内容 |
|---|---|---|
| `StrRelDef` | 175 | 实例 (重抄 40 行), 两层关系, `val₀`, 状态, `PreOut` |
| `StrRelZero` | 254 | 第 0 层每步, `snd₀`, `chainˢ` |
| `StrRelSound` | 231 | 第 1 层每步, `snd₁` |
| `StrRelChain` | 66 | `mono₂ˢ`, `grow₂₃ˢ` |
| `StrRelHead` | 190 | 位置, 拆分, `head`, `headAdm` |
| `StrRelNeg` | 131 | `vhead→LPO` |
| 入口 | 15 | |
| 合计 | 1062 | |

对照 `MonoPort2` (820 行, 同范围, 值的关系): 本组的 `Def`+`Zero`+`Sound`+`Chain` 是 726 行.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel where

import OCF.Align.StrRelDef
import OCF.Align.StrRelZero
import OCF.Align.StrRelSound
open import OCF.Align.StrRelChain using (HA-Stepˢ; chainLeˢ; mono₂ˢ; grow₂₃ˢ) public
open import OCF.Align.StrRelHead using (Sp; pre; rem; dec; head; headAdm) public
open import OCF.Align.StrRelNeg using (VHead; LPO; vhead→LPO) public
open import OCF.Align.CumReadCF using (A)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.KNestAdm as KA
import OCF.Align.StrRelHead as SH

-- 本组的 Adm 就是 KNestAdm 的 Adm
adm≡ : ∀ a b c d → SH.Adm a b c d ≡ KA.Adm a b c d
adm≡ a b c d = refl
```
