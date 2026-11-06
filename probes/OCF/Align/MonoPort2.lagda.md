# 共同的单调目标, 第二站: 入口

> **判决: PARTIAL (第二站 HOLDS).** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, **不用 `Funext`**, 没有验收文件.
>
> 1. **第 1 层的值关系, 两件一起成立 (HOLDS, 实例 $\Lambda=2$, 世界固定).** [MonoPort2Rel](MonoPort2Rel.lagda.md) 的 $\sqsubseteq$, [MonoPort2Sound](MonoPort2Sound.lagda.md) 的 **`snd`**: $x\sqsubseteq x'$ ⇒ 对一切满足 `HA₁` 的动作、一切 `SRel` 相关且 `Good` 的状态、一切底 $c\le c'$, (a) 第 0 层读数 $c+\mathrm{out}_{T_0}(x)\le c'+\mathrm{out}_{T_0}(x')$, (b) **第 1 层输出封闭** $\mathrm{out}_{T_1}(x)\sqsubseteq\mathrm{out}_{T_1}(x')$. (a) 与 (b) 对推导一起归纳, 一个证明.
> 2. **第 0 层输入的两读数同余 (HOLDS).** [MonoPort2Zero](MonoPort2Zero.lagda.md) `cong0₂`: 第 0 层值 $\le$ ⇒ $T_0$ 读数 $\le$ 且 $T_1$ 输出 $\sqsubseteq$, 两边动作可以不同; `chain₂`: 节点上升的链. 规范形仍是 `DValCanon.Gen` 原样套用.
> 3. **`ChainLe (hs hz)`, 即 `MonoStep (hs (hs hz))`, 无条件 (HOLDS).** [MonoPort2Chain](MonoPort2Chain.lagda.md) `chainLe₁`, **`mono₂`**.
> 4. **推论 $T_2<T_3$ (HOLDS).** `grow₂₃ : asuc (TΛ 2) ≤ TΛ 3` (经 `HtCrossVInst.HsS.hs-reduce<′`, 不用外延性), `grow₀₃ : TΛ 0 + 3 ≤ TΛ 3`.
> 5. **一族 $R_{c,c'}$ 与从 $c$ 到 $c+1$ 的一步: 没有做** (未完成, 不是否定). 见 §3. 没有找到反例, 没有否定定理.

## 1 关系与语义

    data _⊑_ : D₁ → D₁ → Set          -- D₁ = D (hs hz) W, 世界 W 固定
      n0⊑ : n0 ⊑ x                     n1⊑ : n1 ⊑ n1
      ⨾⊑  : Rf x → Rf x′ → x ⊑ x′ → y ⊑ y′ → x ⨾ y ⊑ x′ ⨾ y′
      nl⊑ : (∀ n → Rf (d n)) → (∀ n → Rf (d′ n)) → (∀ n → d n ⊑ d′ n) → nl d ⊑ nl d′
      ni⊑ : Mono u → Mono u′ → (val z ≤ val z′ ⇒ u z ⊑ u′ z′) → ni u ⊑ ni u′      -- 分支只在 self, lW 上取
      tr, u0ˡ u0ʳ u1ˡ u1ʳ
      as*  : Rf x → Rf y → Rf z → …
      pre⊑ : Rf x → Rf x′ → (∀ n → Rf (d n)) → (∀ n → Rf (d′ n)) → x ⊑ x′ → (∀ n → d n ⊑ d′ n) → ∀ k → x ⨾ preL d k ⊑ x′ ⨾ nl d′
      lim⊑ : Rf x → (∀ n → Rf (d n)) → (∀ k → x ⨾ preL d k ⊑ t) → x ⨾ nl d ⊑ t

    SRel Y Y′ = vY Y ≤ vY Y′ × d₁ Y ⊑ d₁ Y′        Good Y = Rf (d₁ Y)
    Sem₁ x x′ = ∀ A → HA₁ A → ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (Run x) (Run x′)
    Obs c c′ Δ Δ′ = (c + out_{T₀} Δ ≤ c′ + out_{T₀} Δ′) × (out_{T₁} Δ ⊑ out_{T₁} Δ′)

与 `DValTree` 的差别, 都是证明逼出的:

- **自比作为子推导带着.** 语义里状态要 `Good` (`tr`, `as*`, `pre⊑`, `lim⊑` 都要在 "同一状态" 或 "值相同、字面不同的两个状态" 上走一段), 加进状态的那一段的输出就要自比. 第 1 层不是一切树都自比 (没有 `rO`), 所以自比只能由推导带着; 作为子推导, `snd` 的递归是结构的.
- **两个读数一起.** (b) 要状态在 $T_1$ 上的差可比, 状态在第 0 层的链里又被第 0 层输入的输出改写, 所以第 0 层那一层 (`cong0₂`, `chain₂`) 也要两读数一起比, 状态关系带 `Good` (同 `DValKn`).
- **世界固定, 分支只在 `self` 上比.** 这一实例里第 1 层的折叠只从 `self` 进 (`Chn`, `RKi` 的上升在当前世界里调动作; `Ai` 在 `self` 上取分支; 输出节点在 $T_1$ 上, 世界不变), `cv self Y` 的两个读数与 $Y$ 定义性相同. 换世界的情形 (`HtFeed` 的一般世界, `nκ`) 不在本组内.

**这个关系是哪一种** (回答 `KNest2` 的接口问题): 是**值的**那一种. 第 1 层上有 `lim⊑` (左极限截断); 第 0 层的坐标按值对齐 (`ni⊑` 的前提是 `val z ≤ val z′`), 第 0 层输入的比较经 `Gen` 的规范形, 用了 `lim-leP`. 所以它的输出**不能**直接接 `KNest2` 的 `CellStep` (那里的头对齐要不用 `lim-leP` 的结构关系). 判断.

## 2 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `G⊕`, `S⊕`, `asS`, `G⊕0`, `S0ˡ`, `S0ʳ`, `rfΩ`, `PreOut.O≡` | MonoPort2Rel | 状态更新, 结合重排, $\Omega_1$ 自比, 部分和的输出 | 定理 |
| `semi⨾`, `semiNl`, `rO`, `unit-*`, `assoc`, `pre-le`, `lim-leP`, `tr⊑*` | MonoPort2Zero | 第 0 层输入, 两读数, 结构律 | 条件定理 (动作的 `HA0`) |
| **`cong0₂`** | MonoPort2Zero | 第 0 层值 $\le$ ⇒ $T_0$ 读数 $\le$ 且 $T_1$ 输出 $\sqsubseteq$ | 条件定理 (三条 `HA0`) |
| **`chain₂`** | MonoPort2Zero | 第 1 层节点上升的链对起点单调 | 条件定理 (三条 `HA0`) |
| `⨾S` … `limS`, `branch`, `niS` | MonoPort2Sound | 每个构造子一步 | 条件定理 (动作 `HA₁`) |
| **`snd`** | MonoPort2Sound | $x\sqsubseteq x'$ ⇒ (a) 第 0 层读数单调, (b) 第 1 层输出封闭 | 条件定理 (动作 `HA₁`) |
| `HA-Step₁` | MonoPort2Chain | `StepA` 满足 `HA₁` | 定理 |
| `chain₁`, **`chainLe₁`** | MonoPort2Chain | 外层链; `ChainLe (hs hz)` | 定理, 无前提 |
| **`mono₂`** | MonoPort2Chain | `Hs.MonoStep (hs (hs hz)) tt` | **定理, 无前提** |
| **`grow₂₃`**, `grow₀₃` | MonoPort2Chain | $T_2+1\le T_3$; $T_0+3\le T_3$ | **定理, 无前提, 无 `Funext`** |
| 一族 $R_{c,c'}$, 一步 $c\to c+1$ | — | 见 §3 | 判断, 未做 |

## 3 一族 $R_{c,c'}$: 看出了什么, 缺什么 (判断)

本组的形状对 $c=0\to1$ 是: 层 $c+1$ 的关系 $\sqsubseteq_{c+1}$, 节点分支的坐标按**层 $c$ 的关系**对齐 (这里 $c=0$, 层 0 的关系就是值 $\le$), 语义同时比 $T_0,\dots,T_{c+1}$ 上的读数, 状态关系是各层的差逐层相关. `ni⊑` 的一步用到的是:

1. 层 $c$ 的输入在动作 `Ai u`, `Ai u′` 下走, 两边动作不同, 读数在 $T_0..T_{c+1}$ 上可比 (这里是 `cong0₂`).
2. 层 $c+1$ 的分支在更新后的状态里走, 用归纳 (这里是 `snd` 自己).

推到 $c+1\to c+2$ (实例 $\Lambda=c+3$) 要把 1 换成: 层 $c+1$ 的输入、两边动作不同、读数多一层的 `snd`. 本组的 `snd` 两边动作相同, 只读 $T_0,T_1$, 所以**不是**把它代进去就行: 要把 `snd` 改写成两动作 (下标同 `MonoPort2Zero.I`)、读数与状态对层数参数化的形式, 那才是 "一步定理". 与第 0 层不同, 层 $\ge1$ 的坐标按关系对齐而不是按值, 不需要规范形 (`Gen`), 这一面更简单. 没有写, 不算结论.

## 4 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 关系的构造子 (和的结构, `ni⊑` 逐分支) | 照 `DValTree` | 树侧, 照已有 |
| 构造子带自比 | `snd` 的状态要 `Good`, 第 1 层不是一切树自比 | **树逼的** (证明的形状) |
| 两读数一起, `SRel` 带 $T_1$ 的差 | (b) 要比状态在 $T_1$ 上的差, 状态在第 0 层的链里被改写 | **树逼的** (折叠的形状: `Chn`, `BNi`) |
| 分支只在 `self` 上比, 世界固定 | 这一实例的折叠只从 `self` 进 | 树侧, 计算 |
| `outB` | 字面就是 `RKi` 保留时的分支 (`BNi`) | 树侧, 计算 |
| 第 0 层的动作下标带单调证明 | 同 `DValKn`, 让 `rO` 对树归纳 | 树侧 |

**按 `AGENTS.md` 归类: 提供信息.** 没有新构造子或节点字段, 没有改折叠, 没有 `Lab`, 没有记号. 一步: `snd` 对一切动作与状态, `cong0₂`, `chain₂` 对一切下标; 只有 `HA-Step₁` 与起点是这一站的. 脚手架 (判断): 自比的子推导与 `Good` 的跟踪约占 `MonoPort2Sound` 与 `MonoPort2Zero` 的三分之一, 是 "状态关系不自反" 逼出的; `Zero` 与 `Sound` 的结构律有重复 (两层的上下文前提不同, 没有合并). 第 0 层一份与 `MonoPortZero` 重复, 多了 $T_1$ 的那一半. 没有序数值验收 (无参照树), `grow₂₃` 只说明不塌缩.

## 5 账

| 文件 | 行 | 内容 |
|---|---|---|
| `MonoPort2Rel` | 109 | 实例, 读数, 关系, 状态, 小件 |
| `MonoPort2Zero` | 359 | 第 0 层两读数的结构律, `Gen`, `cong0₂`, `chain₂` |
| `MonoPort2Sound` | 271 | 每个构造子一步, `snd` |
| `MonoPort2Chain` | 75 | 外层链, `mono₂`, `grow₂₃` |
| 入口 | 6 | |
| 合计 | 820 | |

## 6 审计

- **导入闭包** (`importclosure.py`, `--only` 同 [MonoPort](MonoPort.lagda.md)): 入口 45 个模块 (本地 35), `Rel` 30, `Zero` 31, `Sound` 32, `Chain` 44; 都是退出码 0, 禁用表 0, `--only` 之外 0.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `MonoPort2Chain:mono₂` 325/0/0, `MonoPort2Chain:grow₂₃` 406/0/0, `MonoPort2Chain:chainLe₁` 316/0/0, `MonoPort2Sound:snd` 283/0/0, `MonoPort2Zero:cong0₂` 242/0/0, `MonoPort2Zero:chain₂` 246/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58.
- **禁用构造**: 五个文件无 `postulate`, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不用 `--cubical`, 不出现 `Funext`.
- **编译**: 删掉本组自己的 `.agdai` 后重编, 入口退出码 0 (5 秒, 峰值 0.7G); 共享模块没有用 `--ignore-interfaces`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort2 where

import OCF.Align.MonoPort2Rel
import OCF.Align.MonoPort2Zero
import OCF.Align.MonoPort2Sound
open import OCF.Align.MonoPort2Chain using (HA-Step₁; chainLe₁; mono₂; grow₂₃; grow₀₃) public
```
