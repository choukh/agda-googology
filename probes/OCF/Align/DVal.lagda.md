# 差树上的值关系: 入口

> **判决: PARTIAL.** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> 1. **定义 (HOLDS).** 第 1 层差树上的关系 $\sqsubseteq^{\mathsf d}$ ([DValTree](DValTree.lagda.md)), 只看差树, 不提折叠, 不经 `toB`. 和的结构按值比 (同余, 单位, 结合, 极限是部分和的上界), `ni` **逐分支**比, 坐标按第 0 层的值对齐; 判据 (分支对坐标值单调, 被重排的一段自比) 作为构造子的前提. **不含 `nκ` 的规则.**
> 2. **折叠单调 (HOLDS, 不含 `nκ` 的那一段).** `DValSound.snd`: $x\sqsubseteq^{\mathsf d}x'$ ⇒ 折叠 (`SumOneClosed`, 输入层 `cnt one`, 目标第 0 层) 的输出 $c+\mathrm{out}(x)\le c'+\mathrm{out}(x')$, 对一切满足 `HA₁` 的动作, 一切抬升路径与坐标, 一切值可比的底与状态. 输入里可以有任意嵌套的 `ni`, 分支可以读坐标.
> 3. **判据由折叠产出的树满足 (HOLDS, 部分).** `DValKn.Kn-Rf`: 折叠产出的第一个读坐标节点 `CvFoldInst.Kn` 自比 (状态一致时); `Pk-Rf`, `DValInst.rf-A`: `mid₁` 的前两段自比. 动作: `Step` 满足 `HA₁` (`StepV₀`), $\psi_0(\Omega_{\Omega+1})$ 第 1 层链的动作字面归约到它 (`HA-ai`).
> 4. **否定 (编译过).** `DValNeg.¬assoc`: 无条件的结合律让折叠不单调, 所以判据必须有; `xb-not-Rf`: 判据是真限制. `¬κ-refl`: 同余 + 无节点前缀按值 + `nκ` 无条件自比 ⇒ 折叠不单调, 所以 `nκ` 的分支必须按**层的值**对齐. `DValInst.¬rel-*`: `L1Val` 的三对反例都不在关系里.
> 5. **`nκ` 与 $\psi_0(\Omega_{\Omega+1})$ 的上界: 未走通.** $\psi_0(\Omega_{\Omega+1})$ 的计算里, 目标第 0 层要走的第 1 层树 (状态在第 1 层的差) 含 `nκ` (`LayerTrFold.mid-κ`), 而且 `nκ` 嵌在 `ni` 与 `nκ` 的分支里. 本组的定理不覆盖它们. 第一个障碍见 §3. 粗上界 (哪怕 $\le\psi_0(\Omega_b)$ 一类) 也没有做: 它同样要过 `nκ` (判断).

## 1 定义

    data _⊑ᵈ_ : D one V → D one V′ → Set
      n0⊑ : n0 ⊑ᵈ x                     n1⊑ : n1 ⊑ᵈ n1
      ⨾⊑, nl⊑, nwˡ, nwʳ                 同余, 抬升透明
      u0ˡ u0ʳ u1ˡ u1ʳ                    单位 (相对形式: x ⊑ x′ → n0 ⨾ x ⊑ x′ …)
      asˡ asˡ′ asʳ asʳ′ : Rf z → …       结合, 被重排的最后一段要自比
      pre⊑ : x ⊑ x′ → (∀ n → d n ⊑ d′ n) → x ⨾ pre₁ d k ⊑ x′ ⨾ nl d′
      lim⊑ : (∀ n → Rf (d n)) → (∀ k → x ⨾ pre₁ d k ⊑ t) → x ⨾ nl d ⊑ t
      trˡ, trʳ                           传递, 中间的树与一边同世界
      ni⊑ : Mono u → Mono u′ → (∀ q q′ l z z′ → V0 z ≤ V0 z′ → u q l z ⊑ u′ q′ l z′) → ni u ⊑ ni u′

`Rf x = x ⊑ᵈ x` 是输入判据. `Mono u`: 分支在一切抬升路径、一切值可比的坐标上 $\sqsubseteq^{\mathsf d}$.

**与 `L1Val` §2 三条要求的对照.** (1) 定义在差树上, 分支由差树坐标 $w$ 给出: 是. (2) `ni` 逐分支比 (同坐标位置, 坐标按值对齐; 没有 `i≼`): 是; `nκ`: 没有做, 而且 `¬κ-refl` 说明 "同一世界同一路径逐分支" 不够, 要按层的值对齐. (3) 第 0 层的部分按值比, 经规范形: 是, `DValInst.cong↑` (无节点的树抬上来, 第 0 层值 $\le$ 则 $\sqsubseteq^{\mathsf d}$), 由 [DValCanon](DValCanon.lagda.md) 的通用规范形论证从构造子拼出. `Pos` (分支 $\ge1$) 不需要: 它管的是与上确界读法比, 这里不比上确界.

**第一个障碍 (`L1Val` §2) 怎么过的.** 两种比较在同一棵树里交替 ($x⨾\mathrm{ni}\,u$ 对 $(x'⨾0)⨾\mathrm{ni}\,u'$): 结构律做成**相对形式** (`u0ˡ : x ⊑ x′ → n0 ⨾ x ⊑ x′`), 不要求两边自比; 只有结合与极限上界要自比, 那是语义逼出的 (`¬assoc`). 证 "折叠单调" 时把 `CvLayerRun` 的规范形论证对关系抽象一次 (`DValCanon.Gen`, 关系带两个下标, 两边动作可以不同), 用了三次: 目标第 0 层的第 0 层输入 (`DValZero.cong0`, `ni` 的链用它), 第 1 层无节点部分 (`cong↑`), 目标第 1 层用 $\sqsubseteq^{\mathsf d}$ 比输出 (`DValKn.cong1`, `Kn` 用它). 估计 600 行, 实际 agda 代码 1028 行 (8 个文件, 含三个实例与否定).

## 2 定理

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `Gen`, `Gen.Two.cong0`, `Gen.One.canon` | DValCanon | 规范形论证对关系抽象: 十几条结构律 ⇒ 第 0 层值 $\le$ 则相关 | 条件定理 (前提是结构律) |
| `OutLe`, `HAᶜ`, **`cong0`** | DValZero | 目标第 0 层, 第 0 层输入, 两边动作不同 | 条件定理 (`HAᶜ` 三条) |
| **`chain`** | DValZero | `Chn` 的输出 (rise 的 `nl`) 单调 | 条件定理 (`HAᶜ` 三条) |
| `_⊑ᵈ_`, `Rf`, `Mono`, `rf-ni` | DValTree | 关系与判据 | 定义, 定理 |
| **`snd`** | DValSound | $x\sqsubseteq^{\mathsf d}x'$ ⇒ 目标第 0 层输出单调 | 条件定理 (动作 `HA₁`) |
| `Rf-sound` | DValSound | 自比的树对值相同的状态给值相同的输出 | 条件定理 (`HA₁`) |
| `StepV₀`, `HA-ai` | DValInst | `Step` 与 $\psi_0(\Omega_{\Omega+1})$ 第 1 层链的动作满足 `HA₁` | 定理 |
| `mono-L1` | DValInst | `L1Val` 的场景里 `snd` 无前提 | 定理 |
| `¬rel-sup`, `¬rel-shape`, `¬rel-κ` | DValInst | `L1Val` 的三对反例都不相关 | 定理 (否定) |
| **`cong↑`** | DValInst | 无节点部分按第 0 层值比 | 定理 |
| `rf-Ω`, `rf-Step`, `rf-A` | DValInst | $\Omega_1$ 的差树, `Step` 的输出, `mid₁` 第一段自比 | 定理 |
| `cong1`, `cvS`, `stepS` | DValKn | 目标第 1 层, 输出按 $\sqsubseteq^{\mathsf d}$ 比的值同余; 换世界与 `Step` 保持一致 | 条件定理 / 定理 |
| **`Kn-Rf`**, `Pk-Rf` | DValKn | 折叠产出的读坐标节点自比; `mid₁` 第二段自比 | 定理 (`Kn-Rf` 的前提 `Good Y`; `Pk-Rf` 无前提) |
| **`¬assoc`**, `xb-not-Rf`, `ub-not-Mono` | DValNeg | 结合律要判据; 判据是真限制 | 定理 (否定) |
| **`¬κ-refl`**, `v1ᵈ` | DValNeg | `nκ` 无条件自比与单调不相容; $\sqsubseteq^{\mathsf d}$ 满足其余前提 | 定理 (否定) |

**否定的范围.** `¬assoc` 只说无条件结合律不行 (动作 `A⁺` 满足 `HA₁`, 在 `snd` 的范围内). `¬κ-refl` 只否定 "同余 + 能比 $1$ 与 $(\lim_n0)⨾1$ + 每个 `nκ` 自比" 的关系; 不否定带判据 (分支按层的值单调) 的 `nκ` 规则, 不否定别的目标层. 两条的前提都由具体项满足.

**有限测试.** 无. `big`, `bigκ`, `seg0`, `d1`, `Rκ0`, `outR`, `outκ` 是对具体项的归约 (`refl` 或由 η 解出的 `⊤`), 算定理.

## 3 第一个障碍: `nκ`

`nκ` 在目标第 0 层走回灌 (`RKy`): 层 $v_0=W+z$ 字面地由状态的 $z$ 与世界算出, 沿字面路径走 $[a,v_0)$ 上每一层 $c$ 的分支 $u(c)$, 在世界 $v_0$ 里跑; 下一格 $[v_0,v_0+\mathrm{out}_0)$, 依此类推. 两边状态值可比而字面不同时, 走到的层字面不同 (`¬κ-refl` 的反例就是这个), 所以:

- 分支要按层的**值**对齐: 规则形如 "$c\le c'$ ⇒ $u(c)\sqsubseteq u'(c')$". 证这条的 `Walk` 单调, 是 `CvHighCong.M` 对 "世界依赖的分支" 的推广 (判断: 能做, `M` 的四种情形逐一对应).
- 但嵌套时**不够** (判断, 没有编译): 分支 $u(c)$ 的树世界是 $c$, 跑在世界 $v_0$ 里; 它里面的 `nκ` 走 $[c,v_0+z)$. 左边 $c$, 右边 $c'\ge c$ 时, 右边从更高处起步, 少了 $[c,c')$; 而 `ni` 的分支在世界 $v_0$ 对 $v_0'$ 上, 里面的 `nκ` 走 $[v_0,\dots)$ 对 $[v_0',\dots)$. 一处要 "包含" 式对齐 (起点左高右低), 一处要 "平移" 式对齐 (起点左低右低, 长度左短右长). 合起来的充分条件是: 右边区间的终点不低于左边, 且右边起点加上左边区间的长度不超过右边终点. 这要在语义的上下文里记下 "树的世界到跑的世界的那一段" (`dif W q`) 并对它做序数减法, 而 `nw` 的两条透明律在这种上下文下不能同时成立 (判断).
- 所以下一步要的是**带上下文长度的关系**: 上下文 $(a,\ \text{长度})$, 比较两边的区间, 不是只比状态值. 这是跨层的值语义 (`CvLayer` §3 说的 "第 2 项").

$\psi_0(\Omega_{\Omega+1})$ 的计算在第 1 层链上走的树含嵌套的 `nκ`, 所以上界 (精确的或粗的) 都卡在这里.

**`HtFeed` 的层.** 本组只用第 1 层差树 (`SumOneTree.D one`), `HtFeed` 的层 1 也是它; `DValCanon` 与层无关 (只用第 0 层树与关系的结构律), `DValZero`, `DValSound` 的证明只用 `Run` 在 `ni`, 和的结构上的子句, 与 `HtFeedFold` 同形 (判断, 没有搬过去编译).

## 4 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `DValCanon` | 无. `CvLayerRun` §4–§6 对关系抽象 | 提供信息 |
| `DValZero` | 无. 用 `SumOneClosed` 的折叠 ($S=\cdot\omega$ 抄自旧折叠) | 提供信息, 折叠形状受旧树影响 |
| `DValTree` | 无. 构造子由折叠的子句逐条逼出: `ni⊑` 的三条前提来自 `RKi` rise 的链 (`chain` 要 `HAᶜ` 三条); `Rf` 前提来自 `as*`, `lim⊑` 的语义 (`¬assoc`) | 提供信息 |
| `DValSound` | 无. 每个构造子一步, 新用到的字段见该文件表 | 提供信息 |
| `DValInst`, `DValKn` | 无. 用 `SumOneClosed` 的闭项与 `CvFoldInst.Kn` | 提供信息, 形状受旧树影响 |
| `DValNeg` | 无. 反例形状读自 `RKy` 的回灌读层 `sum W z` 与 `Run` 的坐标记法 | 提供信息 |

没有新构造子, 没有新折叠规则. 一步定理与新用到的字段: `snd` 的 `ni⊑` 一步用 `RKi` rise 的链点 $\delta_n$ (状态在第 0 层的差) 与链的动作 `Ai u` (分支在坐标上跑); `as*` 一步用 "同一段在两个值相同、字面不同的状态上走"; `cong1` 用 `cv` 的世界抬升; `¬κ-refl` 用 `nκ` 的回灌层 `v = sum W z` 的字面形状. 这一站加深翻译的标志都没有: 没有读自记号基本列的字段, 闭包定理没有新前提, 不用 `Lab` 验收. 关系的形状 (`ni` 逐分支, 坐标按值对齐) 是 `L1Val` 的三条否定逼出的, 不是从记号读来的.

## 5 审计

- `importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRule --only OCF.Align.TLOpsW --only OCF.Align.SumOne --only OCF.Align.BrwMid --only OCF.Align.LayerTr --only OCF.Align.CvFold --only OCF.Align.CvHigh --only OCF.Align.CvLayer --only OCF.Align.NoCumLit --only OCF.Align.L1Val --only OCF.Align.DVal OCF.Align.DVal`: 闭包 45 个模块 (本地 35), 禁用表命中 0, `--only` 之外 0, OK. 这是编译器保证的不引用; 不说明定义没有受记号启发.
- `depslice.py` (语法级近似): `DValSound:snd` 到达 208 块, `DValKn:Kn-Rf` 202, `DValNeg:¬κ-refl` 153, `DValNeg:¬assoc` 150, `DValInst:cong↑` 81, `DValTree:_⊑ᵈ_` 32, 记号模块块数都是 0, 别处记号词 0. 正对照 `Om1HnAccept:label-term₀`: 到达 1188, 记号模块 92 块, 别处 58.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DVal where

open import OCF.Align.DValCanon using (module Gen) public
open import OCF.Align.DValTree public
import OCF.Align.DValZero
import OCF.Align.DValSound
open import OCF.Align.DValInst using (StepV₀; HA-ai; mono-L1; ¬rel-sup; ¬rel-shape; ¬rel-κ; up; cong↑; rf-Ω; rf-Step; rf-A) public
open import OCF.Align.DValKn using (Good; SRel; cvS; stepS; Kn-Rf; Pk-Rf) public
open import OCF.Align.DValNeg using (¬assoc; xb-not-Rf; ub-not-Mono; ¬κ-refl; v1ᵈ) public
```
