# 结构关系, 第九轮: 树世界处的领先量与带前段对齐的 `nw`: 入口

> **判决: PARTIAL (第 1, 2 项是编译过的定理, 第 3 项暂停).** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 没有改任何已有文件, 没有改树与折叠.
>
> 1. **(HOLDS) 带前段对齐的 `nw`.** 新语义 `SemL lV lV′ x x′` = `StrRel7Snd.SemS` 加三条前提: 树世界处的领先量 $\mathrm{Adm}(V,V';W,W')$, 两条 `Lg` 等式 `lV ≡ lg⊲ q lW` (树世界处的极限结构就是运行路径带下来的那个). 新关系 `Le lV lV′` = $\sqsubseteq^{+}$ 的九个构造子 (带 `Lg` 下标) + **`nwΣᴸ`**: $U\le U'$, $z\sqsubseteq^{\mathsf P}z'$, `Le lU lU′ x x′` ⇒ `nw (sum-fst U z) x` 与 `nw (sum-fst U′ z′) x′` 相关. **`sndᴸ`**: `Le ⇒ SemL`, 对推导归纳一个证明, 无参数, 含嵌套 `nκ`, 对一切深度 (`StrRel9Snd`). 新前提在每个递归调用处都由折叠的字面给出 (下表). 旧关系在一切下标处嵌入 (`emb⁺`); 顶层前提可满足 (`top`). 语义层面的统一规则 `snd-nwA` (前段在自己的顶端世界上对齐 + 前段底端有领先量 ⇒ 两边的 `nw` 透明), `nwΣᴸ` 是它的实例 (`nwΣ′`), 上下文里的 `nw q x` 也是 (`ctx-nw`, 三条前提正好是外层的前提) (`StrRel9Nw`).
> 2. **对照 (定理).** `StrRel8Neg` 的反例在新语义下仍成立 (`StrRel9Ex.¬nwˡᴸ`): 新的三条前提在反例的参数上都满足, 所以 `SemL` 不是靠多加前提变成空真的; `nwΣᴸ` 的可靠性来自前段的形状. 用到新规则、前提可满足的例子 `ex-nw`, `ex-run`; `cv` 读数的形状 `cv-read`.
> 3. **(暂停) 逐层关系族, `R∀` 覆盖一切目标层, 移植到 `HtFeedFold`, `Ωᴴ` 处的 `MonoStep`.** 没有做. 第一个障碍 (判断, §3): 多层时动作是 `Ai` 一类, 读上下文 (上下文就是分支收到的坐标), 所以 "以动作为参数的 `sndᴸ`" 的动作前提必须带上下文关系, 而上下文关系在第 $k$ 层就是第 $k$ 层的 `SemL`: 关系族与语义要对层同时递归 (与 `MonoPort6Rel.Rel` 对层递归同形, 但每层带两世界的对齐与领先量). `ctx-nw` 给出这一递归在 `nw` 一句要的东西. 另有一条读代码得到的事实 (§3): `HtFeedFold.cv` 不给读数包 `nw` (只换目标的下标 `tg↑`), 所以 `StrRel7` §4 说的 "`cv` 给高层读数包 `nw`" 是 `SumOneFold` 的情形; 在主线折叠里, cv 形状的前段只包上下文 (`κc` 的 `nw (sum-fst W (z Y)) w`).

## 0 模块

| 文件 | 内容 | 档 |
|---|---|---|
| [StrRel9Walk](StrRel9Walk.lagda.md) | `GoD.walkᵈ`, `GoD.cellᵈ`: `StrRel7Walk.GoC` 的分支比较多收 `Lg` 等式 | 定理 (`GoD` 以分支比较为模块参数, 与 `GoC` 同) |
| [StrRel9Snd](StrRel9Snd.lagda.md) | `Le` (含 `nwΣᴸ`), `SemL`, **`sndᴸ`**, `adm-lo`, `eq-nw`, `emb⁺`, `top` | 定理, 无参数 |
| [StrRel9Nw](StrRel9Nw.lagda.md) | `snd-nwA`, `nwΣ′`, `ctx-nw` | 定理 |
| [StrRel9Ex](StrRel9Ex.lagda.md) | `cv-read`, `ex-nw`, `ex-run`, `¬nwˡᴸ` | 定理 (`¬nwˡᴸ` 否定) |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel9 where

open import OCF.Align.StrRel9Walk public using (module GoD)
open import OCF.Align.StrRel9Snd public
open import OCF.Align.StrRel9Nw public using (snd-nwA; nwΣ′; ctx-nw)
open import OCF.Align.StrRel9Ex public using (cv-read; xκ; ex-nw; ex-run; ¬nwˡᴸ)
```

## 1 新前提从哪里来

| `sndᴸ` 的一句 | 领先量 $\mathrm{Adm}(V,V';W,W')$ | `Lg` 等式 |
|---|---|---|
| `n0ᴸ`, `n1ᴸ`, `⨾ᴸ`, `nlᴸ`, `prᴸ` | 原样往下传 | 原样往下传 |
| `nwʳᴸ` (右边 `nw p`) | `adm-lo`: 领先量对右边起点反单调 | `lg-tr` |
| `trᴸ` (左左比较) | `KNestAdm.split q lW` (字面路径给出长度) | 原样 |
| `κᴸ` (格里的分支) | 对齐 `aP` 本来就带的 $\mathrm{Adm}(c,c';L,L')$, `GoD` 交给分支 | 走法本来就带的 `e-suc bV (lW s) e`, `GoD` 交给分支 |
| `niᴸ` (`Ai` 里的分支) | 分支在 `self` 上跑: `adm-self` | `refl` |
| **`nwΣᴸ`** | `adm-tr (adv-sum … (adm-self U U′) …) ad` | `eq-nw` (`lgsf`, `lg-tr`) |

`nwΣᴸ` 一句: 内层路径是 `⊲-tr (sum-fst U z) q`, 对齐是 `cat (genᴾ hz lU lU′ hU ad) hq e e′`. `genᴾ` 要的领先量 $\mathrm{Adm}(\Sigma Uz,\Sigma U'z';L,L')$ 正是新语义在 `nw` 树的树世界处带的那一条; 拼接点的 `Lg` 等式正是新语义的 `e`. 这就是 `StrRel8` 判决第 2 条说缺的两件.

## 2 为什么要 `Lg` 等式 (树逼出)

`Lg (alim f)` 带基本列的每一步路径 (`CumReadCF.Lg`), 两个 `Lg` 值不一定相等. `genᴾ` 生成的对齐在 `sum U z` 处用的是 `Lg-sum U z lU`, 而折叠沿运行路径走到 `sum U z` 时用的是 `lg⊲ q lW`. 两者不同时, 左边的走法经过的是另一组极限步, `genᴾ` 的对齐不适用. 所以等式不是工程上的方便, 是 `Walk` 读 `Lg` 的字面逼出的. 在折叠实际调用的地方它都是 `refl` 或已有的 `e-suc` (§1 的表).

## 3 暂停的部分 (判断)

- **`HtFeedFold.cv` 不包 `nw`.** `cv q Y = st (df (λ T → yc (d Y) (tg↑ q T))) n0` (`HtFeedFold` 第 72 到 73 行): 读数按目标的世界 $m$ 存放, 换世界只换目标的下标. 主线折叠里 `nw` 只出现在上下文里: `Run` 的 `w ⨾ nw q₀ x` (前段是运行路径; `ctx-nw` 处理), `Ai` 的 `nw p w`, `Kp`/`Kb` 的 `nw wu w`, `nw p (…)`, `κc` 的 `nw (sum-fst W (z Y)) w` 与后继格的 `nw (sum-fst (v c₀) …) (…)` (cv 形状; `nwΣ′` 处理). 这条是读代码, 没有写成定理.
- **上下文是被读的.** `Run … n1 … = A₀ C.self lW w Y`, 而 `Ai` 把它收到的第三个参数当坐标交给分支 (`u … (inV ly r z)`); 所以在 `Ai` 一类动作下, 上下文就是下一层的坐标. 在 `SumOne` 两层的设置里坐标在第 0 层, $\sqsubseteq^{\mathsf P}$ 有 `wl`, `wr`, `nw` 两边都透明, 所以 `SemS`/`SemL` 可以对上下文全称. 多层时坐标层 $k\ge1$ 含 `nκ`, `nw` 不再透明 (`¬nwˡᴸ`), 上下文必须带关系, 而那个关系就是第 $k$ 层的 `SemL`.
- **所以 (2a)(2b) 是一件事.** 关系族 `Le_k` 与语义 `SemL_k` 对层同时递归: 第 $L$ 层的 `SemL` 的动作前提 = "上下文按 `SemL_k` 相关 ⇒ 输出相关", `R∀` 对一切目标层 $k$ 取 `SemL_k` 意义下的读数关系. `ctx-nw` 说明 `⨾`, `nl` 两句给上下文接的 `nw` 由同一套前提维持; `nwΣ′` 说明 `κc` 给上下文包的前段也可以. 未检查的: `Ai` 的 `nw p w` (p 来自 `BNi` 的 `keep` 分支, 两边的 p 由 `rkT` 的 `cmpH` 在运行时给出, 对齐要从格的对齐读出) 与 `Kp` 的 `nw wu w` (wu 是目标相关的 `W⊲wm τ`). 估计 (判断): 把 `StrRel9Snd` 的证明改成对层递归的关系族 600 到 1000 行; 移植到 `HtFeedFold` 再 800 到 1200 行 (`Walk`, `GoD`, 对齐, `genᴾ` 的高度树版).
- **`Ωᴴ` 处的 `MonoStep`.** 以上述两步为前提; 没有做. `MonoPort6` 的关系是单世界的 (`MonoPort6.lagda.md` §3), `Ωd Ωᴴ` 含 `nκ`, 两边格世界不同, 正需要本轮的两世界语义.

## 4 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 树世界处的领先量 $\mathrm{Adm}(V,V';W,W')$ 作语义前提 | `genᴾ` 拼接前段时要 (`StrRel8` 判决第 2 条); `KNestSound` 的带下标关系同形 | **树逼的** |
| `Lg` 下标与等式 `lV ≡ lg⊲ q lW` | `Walk` 读 `Lg` 里的极限步路径, `cat` 要拼接点一致 (§2) | **树逼的** |
| `GoD` 的分支多收等式 | `walkᶜ` 的 `aP` 一句本来就有 `e-suc …` | **树逼的** (折叠字面) |
| `nwΣᴸ` 的前段形状 `sum-fst U z`, $z\sqsubseteq^{\mathsf P}z'$, $U\le U'$ | `SumOneFold.κc` 的 `cv (sum-fst W (z Y))`, `R∀` 的第二分量 | **树逼的** |
| `snd-nwA` 的两条前提 | `nwΣᴸ` 证明里用到的恰是这两件; 否定 `¬nwˡᴸ` 说没有它们不行 | **树逼的** |

**归类: 提供信息.** 没有新构造子或节点字段 (关系的构造子不是树的), 没有改树与折叠, 没有 `Lab`, 没有记号. `sndᴸ` 对一切推导一个证明, 不按深度加前提; 新前提是语义的, 对一切规则一样, 不是为某一站加的专属前提. 这一站新用到的字段: `Lg (alim f)` 的第一分量 (极限步的路径) 通过 `lgsf`, `lg-tr`; `Al` 的 `aP` 所带的领先量 (以前只在对齐内部用, 现在交给分支). 否定 `¬nwˡᴸ` 划出新语义下仍不能有的规则.

## 5 审计与账

- 编译: 删掉本轮五个 `.agdai` 后从入口从头编译, 退出码 0. 无禁用构造, 不出现 `Funext`.
- 编译用时约 13 秒, 峰值常驻约 1.3G (`-M6G`).
- 导入闭包 (`importclosure.py`, `--only` 同 [StrRel7](StrRel7.lagda.md) 的表, 即 `OCF.Free.Level`, `OCF.BTBO`, `OCF.Align.` 下的 `CumReadCF`, `TLRule`, `TLOpsW`, `SumOne`, `HtGen`, `HtFeed`, `HtCross`, `MonoPort`, `KVal`, `KNest`, `StrRel`, `BrwMid`, `LayerTr`, `NoCumLit`, `L1Val`, `DVal`, `GenAbs`): 入口闭包 65 个模块 (本地 55, 库 10), 禁用表命中 0, `--only` 之外 0, OK.
- `depslice.py`: `StrRel9Snd:sndᴸ` 236 块, `StrRel9Nw:snd-nwA` 143, `StrRel9Nw:ctx-nw` 239, `StrRel9Ex:¬nwˡᴸ` 155, `StrRel9Ex:ex-run` 243; 记号模块块数都是 0, 别处记号词 0. 正对照 `Om1HnAccept:label-term₀`: 1188, 92, 58.
- 代码行 (代码块内非空, 去注释行): 入口 6, `StrRel9Walk` 80 (其中约 70 行逐字沿用 `StrRel7Walk.GoC`), `StrRel9Snd` 197 (其中约 150 行逐句沿用 `StrRel7Snd.snd⁺`), `StrRel9Nw` 40, `StrRel9Ex` 46; 合计 369.
