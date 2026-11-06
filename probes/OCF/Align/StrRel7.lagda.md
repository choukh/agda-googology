# 结构关系, 第七轮: 单个状态的自洽, 传递与 `ni`: 入口

> **判决: PARTIAL.** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 没有改任何已有文件, 没有改树与折叠.
>
> 1. **(HOLDS) 结构版 `coh₁`.** 自洽的状态 (同一状态在任意两条读数路径上的第 0 层读数 $\sqsubseteq^{\mathsf P}$ 相关) 跑**任意**第 1 层树, 输出自洽 (`StrRel7Coh.coh₁`; 动作自洽为前提, 主线动作 `Step` 满足 `cA-step`). 含 `ni` (链 `Chn`, 第 0 层引理 `coh₀`) 与 `nκ`. 一个意外的简化: `nκ` 在第 0 层的读数与读数路径无关 (各格首读数的 `nl`), 所以 `nκ` 一句只要自反, 不要对齐. 附带: $\sqsubseteq^{\mathsf P}$ 自反 (`rfP`), 对齐 `Al` 在同一世界上自反 (`alR`, 领先量由 `KNestAdm.split` 给出). 走法的输出自洽 (`StrRel7Walk.cohWlk`).
> 2. **(HOLDS) 传递与 `ni`.** 新关系 $\sqsubseteq^{+}$ = `StrRel6` 的七个构造子 + **`tr⁺`** (中间一棵与左边同一树世界) + **`ni⁺`** (两边分支在 $c\le c'$、坐标 $z\sqsubseteq^{\mathsf P}z'$ 时相关; 左边分支对坐标单调). 语义 `SemS` = `StrRel6.SemT` 加一条前提: 左边状态自洽. **`snd⁺`**: $x\sqsubseteq^{+}x'$ ⇒ `SemS x x′`, 对推导归纳一个证明, 无参数, 含嵌套 `nκ`, 对一切深度. `ni` 用到第 0 层对 $\sqsubseteq^{\mathsf P}$ **全部八个构造子**可靠的 `StrRel7Zero.snd0` (一切读数路径版, 含 `tr`, `pr`, `wl`, `wr`; 不要对齐, 不要世界的序). 旧关系嵌入 (`emb`), `SemT ⇒ SemS` (`T→S`). 自洽这条前提在主线上总能满足: 空状态自洽 (`ch∅`), 跑过任意树后仍自洽 (`reach`). 前提可满足、分支确实读坐标的例子: `ex-ni`.
> 3. **(未走通, 不是否定) 左边 `nw`.** 编译过的只有方法层面的一条: 左边路径比右边多出底部位置时对齐为空 (`¬Al-lft`, 实例 `¬Al-nw`: 两边都从世界本身出发、左边多走一段 `nw` 时, `snd⁺` 的对齐前提无法给出). 语义上 $\mathrm{nw}\,p\,x\sqsubseteq x$ 对含 `nκ` 的 $x$ 是否成立, 没有编译反例 (判断见 §3: 值上大概不能分辨, 结构上缺 "去掉前一项" 的规则).
> 4. **(未走通, 暂停) 移植到 `HtFeedFold` 并消去 `MonoStep`.** 没有做移植. 第一个障碍 (判断, 理由在 §4): `MonoStep` 比较的是**第 Λ 层**的树 `Ωd Λ`, 含 Λ 以下各层的 `ni`; 本轮的理论是两层的 (第 1 层树, 第 0 层坐标). 多层时链 `Chn` 的第 0 项是状态在**第 k 层目标**上的读数, 所以状态关系 `R∀` 要覆盖一切目标层的读数, 而换世界 `cv` 把这些读数包上 `nw` (两边各一个), 第 k ≥ 1 层的读数含 `nκ` 时就落到第 3 条的左边 `nw` 问题上.

## 0 模块

| 文件 | 内容 | 档 |
|---|---|---|
| [StrRel7Coh](StrRel7Coh.lagda.md) | `rfP`, `alR`, `Ch`, `CA`, `coh₀`, `coh₁`, `cA-step`, `ch∅`, `reach` | 定理 |
| [StrRel7Walk](StrRel7Walk.lagda.md) | `cohWlk`; `GoC.walkᶜ`, `GoC.cellᶜ` (走法比较, 状态关系带左边自洽) | 定理 (`GoC` 以分支比较为模块参数, 与 `GoA` 同) |
| [StrRel7Zero](StrRel7Zero.lagda.md) | `AR`, `cohᴬ`, `snd0` (第 0 层, 全部构造子, 一切读数路径) | 定理 (动作关系为前提) |
| [StrRel7Snd](StrRel7Snd.lagda.md) | $\sqsubseteq^{+}$, `SemS`, `snd⁺`, `emb`, `T→S` | 定理, 无参数 |
| 本文 | `ex-ni`, `ex-tr`, `¬Al-lft`, `¬Al-nw` | 定理 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel7 where

open import Data.Nat using (ℕ)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw)
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.StrRel4Walk using (Al)
open import OCF.Align.StrRel4Pr using (_⊑ᴾ_; z0; o1; sq; lm; wl; wr; tr; pr)
open import OCF.Align.StrRel6 using (nest-rel)
open import OCF.Align.KNestSound using (nest)
open import OCF.Align.StrRel7Coh public using (rfP; alR; Ch; CA; coh₀; coh₁; cA-step; ch∅; reach)
open import OCF.Align.StrRel7Walk public using (cohWlk; module GoC)
open import OCF.Align.StrRel7Zero public using (AR; cohᴬ; snd0)
open import OCF.Align.StrRel7Snd public
```

## 1 例子: 分支读坐标的 `ni`

把第 0 层树原样搬到第 1 层 (`nw` 丢掉, 与 `drp` 同). 它对 $\sqsubseteq^{\mathsf P}$ 单调: 第 0 层的八个构造子各对上 $\sqsubseteq^{+}$ 的一个 (`wl`, `wr` 因为 `nw` 已丢掉而直接过去, `tr` 的中间一棵落在同一树世界). 于是 "分支 = 坐标本身" 的 `ni` 满足 `ni⁺` 的两条前提; 右边分支多接一个 `1`.

```agda
lift₀ : ∀ {V W} → D azero V → D one W
lift₀ n0 = n0
lift₀ n1 = n1
lift₀ (x ⨾ y) = lift₀ x ⨾ lift₀ y
lift₀ (nl d) = nl (λ n → lift₀ (d n))
lift₀ (ni () u)
lift₀ (nκ () u)
lift₀ (nw p x) = lift₀ x

mono₀ : ∀ {V V′ W W′} {z : D azero V} {z′ : D azero V′} → z ⊑ᴾ z′ → lift₀ {W = W} z ⊑⁺ lift₀ {W = W′} z′
mono₀ z0 = n0⁺
mono₀ o1 = n1⁺
mono₀ (sq h h′) = ⨾⁺ (mono₀ h) (mono₀ h′)
mono₀ (lm h) = nl⁺ (λ n → mono₀ (h n))
mono₀ {W = W} {W′} (wl {x = x} {x′} h) = mono₀ {W = W} {W′} {x} {x′} h
mono₀ {W = W} {W′} (wr {x = x} {x′} h) = mono₀ {W = W} {W′} {x} {x′} h
mono₀ {W = W} {W′} (tr {x = x} {y} {z} h h′) = tr⁺ (mono₀ {W = W} {W} {x} {y} h) (mono₀ {W = W} {W′} {y} {z} h′)
mono₀ (pr h) = pr⁺ (mono₀ h)

ex-ni : ∀ {V V′} → ni {W = V} (C.ss C.self) (λ _ _ z → lift₀ z) ⊑⁺ ni {W = V′} (C.ss C.self) (λ _ _ z → lift₀ z ⨾ n1)
ex-ni = ni⁺ (λ _ _ _ _ _ hz → pr⁺ (mono₀ hz)) (λ _ _ hz → mono₀ hz)

-- 传递把两段不同的推导接起来: 嵌套族 ⊑ 自己, 再 ⊑ 后面多接一段
ex-tr : ∀ k {V V′} (y : D one V′) → nest k {V} ⊑⁺ (nest k {V′} ⨾ y)
ex-tr k y = tr⁺ (emb (nest-rel k)) (pr⁺ (emb (nest-rel k)))
```

## 2 由此得到的值

`snd⁺` 的结论对一切读数路径对是 $\sqsubseteq^{\mathsf P}$, 值的单调是 `vsᴾ` 的推论, 与 `StrRel5Nest.sem-val` 同, 不重复.

## 3 左边 `nw`

`Run (nw p x) q = Run x (⊲-tr p q)`: 左边从更低的树世界出发, 路径在底部多出 $[V_0,V)$. 对齐 `Al` 从顶端往下配对位置, 左边走完 (`aS`) 时右边可以剩, 反过来不行: 左边还有位置而右边已到起点时没有构造子.

```agda
¬Al-lft : ∀ {L L′ a b b′} {p : a ⊲ b} {lb : Lg (asuc b)} {lb′ : Lg b′} → ¬ Al L L′ (C.suc p) lb (C.self {b′}) lb′
¬Al-lft ()

-- snd⁺ 的语境: 两边都从世界本身出发 (q = q′ = self, 对齐是 aS), 左边多一层 nw
¬Al-nw : ∀ {L L′ V₀} (lV : Lg (asuc V₀)) → ¬ Al L L′ (C.suc (C.self {V₀})) lV (C.self {asuc V₀}) lV
¬Al-nw lV = ¬Al-lft
```

判断 (不是定理): 对 $x=\mathrm{nκ}\,(\lambda\_\,\_\mapsto 1)$, 左边每格比右边多走底部一个位置, 左边第 $n$ 格的读数大致对应右边第 $n+1$ 格, 两边的极限值大概相同, 所以值上分辨不出, 编译的值反例不可得; 结构上, $\mathrm{nl}\,d\sqsubseteq^{\mathsf P}\mathrm{nl}\,d'$ 只有逐项的 `lm` (与经 `tr` 的组合), 没有 "去掉前一项" 的规则, 所以大概推不出. 证明不可推需要 $\sqsubseteq^{\mathsf P}$ 的一个保持不变量, 本轮没有做. **结论: 未走通.**

## 4 移植到高度树折叠与 `MonoStep` (判断)

- `HtCrossInst.MonoStep` 是同一棵树 `Ωd Λ` (第 Λ 层) 在两种输入下的读数比较: 输入世界 0 对 1, 底 1 对 $1+\omega$, 上下文与状态各多一段. Λ = `Ωᴴ` 时这棵树含一切有限层 (以及更高) 的 `ni`.
- 本轮的理论只有两层: 第 1 层树, 第 0 层坐标, 状态关系 `R∀` 只看第 0 层目标上的读数. 多层时, 第 L 层的 `ni r` ($r$: 层 $k<L$) 的链从**状态在第 k 层目标上的读数**出发 (`Chn` 第 0 项 `yc (d Y) (inj₁ kW)`), 坐标树是第 k 层的树, 含 `ni` 与 `nκ`. 所以要: (a) 关系族 $\sqsubseteq_k$ 对一切层 k, 第 k 层的坐标在第 k 层可靠 (与本轮 `snd0` 同形, 但第 k 层有 `nκ`, 要走法与对齐, 即本轮的 `snd⁺` 以动作为参数的版本); (b) 状态关系覆盖一切目标层; (c) 换世界 `cv` 给一切目标层的读数包上 `nw` (两边各一个, `cvR` 在第 0 层用 `wl (wr …)` 收下), 第 k ≥ 1 层的读数含 `nκ` 时, `wl` 就是 §3 的左边 `nw`, 双边的 `nw` 规则要底部两段的对齐, 而底部的段由 `cmpF` 在运行时给出.
- 所以第一个障碍是 (c), 它把第 3 条变成移植的前提. 移植 `StrRel5Walk`/`StrRel5All`/`StrRel6` 的句子到 `HtFeedFold` 本身是机械的 (两个折叠的 `nκ` 一句同形), 但没有 (a)(b)(c), 移植后的定理覆盖不到 `Ωd Λ` 中第 ≥ 2 层的 `ni`, 也就消不掉 `MonoStep`. **结论: 暂停, 未走通.** 估计: (a)(b) 是本轮的机械推广 (按层归纳, 600 到 900 行); (c) 未知.

## 5 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 状态自洽 `Ch` 作语义前提 | `tr` 的中间一棵只能在一边的环境里跑 (树世界对不上另一边), 要那一边的状态与自己相关 | **树逼的** |
| `ni⁺` 的左边单调 | `snd0` 的 `tr` 一句在左边自比, 动作 `Ai` 把累计坐标交给分支 | **树逼的** |
| `ni⁺` 的 $c\le c'$ 与 $z\sqsubseteq^{\mathsf P}z'$ | `Ai` 在 `C.self` 上调用, 位置是运行路径, 世界 $W\le W'$; 坐标来自链 | **树逼的** |
| `tr⁺` 的中间一棵与左边同一树世界 | `Run` 要一条从树世界到运行世界的路径 | **树逼的** |
| `nκ` 一句只要自反 | `RKy` 在第 0 层与读数路径无关 | **树逼的** (折叠的字面) |

**归类: 提供信息.** 没有新构造子或节点字段 (关系的构造子不是树的), 没有改树与折叠, 没有 `Lab`, 没有记号. `snd⁺` 对一切推导一个证明, 不按深度加前提; 闭包定理没有为某一站新增专属前提. 否定 `¬Al-lft` 划出了对齐不能有的情形 (左边底部多出).

## 6 审计与账

- 编译: 删掉本轮五个 `.agdai` 后从入口从头编译, 退出码 0. 无禁用构造, 不出现 `Funext`.
- 导入闭包 (`--only` 同 [StrRel5](StrRel5.lagda.md) 的扩展表, 加 `OCF.Align.GenAbs`): 闭包 60 个模块 (本地 50, 库 10), 禁用表命中 0, `--only` 之外 0, OK.
- `depslice.py`: `StrRel7Snd:snd⁺` 231 块, `StrRel7Coh:coh₁` 114, `StrRel7Zero:snd0` 111, `StrRel7:ex-ni` 24; 记号模块块数都是 0, 别处记号词 0. 正对照 `Om1HnAccept:label-term₀`: 1188, 92, 58.
- 代码行 (代码块内非空): 入口 43, `StrRel7Coh` 109, `StrRel7Walk` 102 (其中 `walkᶜ` 约 60 行逐字沿用 `StrRel5All.walkᴬ`), `StrRel7Zero` 78, `StrRel7Snd` 167; 合计 499.
