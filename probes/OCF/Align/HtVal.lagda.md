# `T-Ω` 的序数值: 高度树一族的第一条值定理 (ψ₀(Ω_Ω) 一站)

> 入口. 本文件只导入树侧的文件 (不读记号); 读记号的是验收文件 [HtValAccept](HtValAccept.lagda.md) (读 `BTBOᴵ`) 与 [HtValAcceptE](HtValAcceptE.lagda.md) (读 `EndLowAccept`, 要归档拷贝). 任务 (11-05 派): 不改 `HtFeedTree.Ωd`, 走值语义, 先证 `BTBOᴵ ≼ ⟪ T-Ω ⟫`, 能做到再证反方向.
>
> **判决: 未走通 (暂停). `BTBOᴵ ≼ ⟪ T-Ω ⟫` 与反方向都只有条件定理, 没有否定.** 编译过的是一次精确的约化与一条否定, 它们把缺口定在一处:
>
> 1. **`T-Ω` 里的 `nκ` 只有一个, 目标第 0 层只经回灌** (`HtValSplit.Ψ≡`, `refl`). 闭项的第 0 层输出字面是 $1⨾(s_0⨾\mathrm{nl}\,(n\mapsto\mathrm{drp}\,\Delta_n))$: $s_0$ 是动作在第一个 `n1` 上的输出, $\Delta_n$ 是回灌第 $n$ 格 (`κc`/`κΔ`/`Walk`) 的输出. `RKk`, `Kp`, `Kb` (`nκ` 在非零目标上的输出) 不在第 0 层的输出里. 格里 `Walk` 跑的是层 `emb c` 上的节点 $N_c$ (分支 `λ _ _ _ → n1`, 没有 `nκ`); 链的输入是状态在层 `emb c` 上的差, 由 `Step` 与 `RKi` 的输出拼成, 也没有 `nκ` (判断, 读代码). **所以不要嵌套 `nκ` 的值语义.** 单层 `nκ` 的结果 (`KValK.snd-hi`, `mono-hi`) 的**形状**正好是这里要的 (格 = 区间和, 整段的包含式对齐 `CutM`, 对格归纳), 但**不够**: 它们在 `SumOneFold` 上, 输入层是 $1$ (分支里只有层 $0$ 的节点), 而 `T-Ω` 的格里每一层 `emb c` ($c<v_n$) 都有节点要比; 缺的是分支 (`lo` 档) 的关系对一切可数层的节点成立.
> 2. **骨架与 `SumOne` 相同, 闭项是格的极限** (`HtValSplit`): `a (suc n) = v n`, `v (suc n) = sum (v n) (Δ n)` (`refl`), `T≤lim`, `lim≤T`; 验收文件里 `T-Ω≈lim : trA T-Ω ≈ᵛ lim (trA ∘ v)` (定理).
> 3. **可数层 $\Omega_t$ 的写法只经动作进来** ([HtValAct](HtValAct.lagda.md)). 折叠里 `Ωd` 只出现在 `Step` 与闭项的输入; 高度 $\Omega$ 的输入只有 `nκ` 与 $N_c$, 与 `SumOne.Ω̂₀` 同形. 参照动作 `Act′` 把 $\Omega_t$ 照 `SumOneTree.Ωd` 写成 $1⨾\mathrm{Dif}_t$, 参照闭项 `T-Ω′` (只作参照物, 不进主线). 这正是 `EndLowT` 的出路 (a) ("只改 `Ωd` 在 `hs`, `hl` 上的两行") 给出的闭项 (第 0 层多一个 `n0`). **主线写法是参照写法的删除** (`Ωd≡`, `refl`): $\Omega_{b+1}=1⨾N_b$ 对 $1⨾(\mathrm{Dif}_b⨾N_b)$. `T-Ω≇T-Ω′` (定理, [HtValNeg](HtValNeg.lagda.md)): 换动作在结构上看得见. 有限测试 ([HtValTest](HtValTest.lagda.md)): `T-Ω′` 在 `T-Ω` 与 `SumOne.T₀` 分开的那条路径上与 `T₀` 相同, 宽 3 到深度 12 同形; 同一比较器分得开 `T-Ω` 与 `T₀`. 所以 `T-Ω` 与 `T₀` 的差别 (测试档) 只来自动作里 $\Omega_t$ 的写法.
> 4. **约化 (条件定理, `HtValAccept.lo`, `hi`, `HtValAcceptE.loᴱ`, `hiᴱ`).** 两对缺的命题都是树侧的 (值序 `TLRuleSpec._≤_`, 不含记号):
>    - `PortLo : T₀ ≤ T-Ω′`, `PortHi : T-Ω′ ≤ T₀` (两个折叠之间; 测试支持它们其实是结构互模拟);
>    - `SwapLo : ∀ n → Σ m. R.v n ≤ M.v m`, `SwapHi : ∀ n → Σ m. M.v n ≤ R.v m` (同一个折叠, 两个动作, 回灌格的层互相共尾).
>
>    `lo : PortLo → SwapLo → BTBOᴵ ≼ trA T-Ω`, `hi : PortHi → SwapHi → trA T-Ω ≼ BTBOᴵ`; 经桥: `loᴱ : … → treeE 2 ≼ ⟪ T-Ω ⟫`, `B≼ᴱ : … → BTBOᴵ ≼ ⟪ T-Ω ⟫`, `hiᴱ`. 第 0 格无条件 (`swapLo₀`, `swapHi₀`: 两边都是 $\omega$).
> 5. **否定 (`HtValNeg.no-pointwise`).** `SwapLo` 不能由 "逐点比较两个动作" 的核得到, 只要关系把层 $0$ 的节点只对层 $0$ 的节点: 层 $2$ 的目标上, 空状态时参照动作的输出有层 $0$ 的节点 $N_0$, 主线的没有. 这杀的正是 `MonoPort3Gen` (`HA`), `StrRel` (`HA0`, `HA₁`), `DVal`, `KVal` 那种前提的形状用在 `SwapLo` 上. 不杀链的错位、跨层对齐、按值的关系. 上界方向不受影响.
>
> **第一个障碍: `SwapLo`, `SwapHi` 在 $n=1$, 即第 0 格的输出 $\Delta_0$ 里层 `emb 2` 上的节点 $N_2$.** $v_0=1+s_0=\omega$ 两边相同 (`swapLo₀`, `swapHi₀`). $v_1=v_0+\Delta_0$, $\Delta_0$ 走层 $[a_0,v_0)=[0,\omega)$ 上的一切 $N_c$ (`a-zero`, `v-suc`). 层 $0,1$ 上两个动作只差 `n0` (`s₀≡`, `s₀′≡`; `Ωd′ (hs hz)` = $1⨾(0⨾N_0)$ 对 `Ωd (hs hz)` = $1⨾N_0$), 从层 $2$ 起写法不同 (`Ωd≡`). 所以 $v_1$ 对 $v'_1$ 是第一个要比而比不了的; 它要的是 (判断, 依据写在每条里):
>
> - 一族在**一切可数层** `emb c` 上的差树关系, 对 `HtFeedFold` 的输出封闭, **世界可变** (回灌的格世界 $v_n$, 节点分支的世界 $W'\ge W$). 现有的只到第 1 层: `StrRel` 的 $\sqsubseteq_0,\sqsubseteq_1$ 在 $\Lambda=2$, 世界固定, 分支只在 `self`; `DVal`, `KVal` 在 `SumOneFold` 的第 1 层; `MonoPort3Gen` 对任意 $\Lambda$ 但世界固定, 只管和的构造子, 节点那几步要按关系另写. 这与 `MonoPort` 的 "第三站", `KValC` 的 "跨层值同余" 是同一个缺口.
> - **上界方向 (`SwapHi`) 是删除的单调** (主线写法是参照写法删去 $\mathrm{Dif}_b$, `Ωd≡`): 关系要有 `n0 ⊑ x` 与同层节点逐分支对齐; 两个动作可以逐点比 (方向 `Act ⊑ Act′`).
> - **下界方向 (`SwapLo`) 要吸收**: 逐点不行 (`no-pointwise`); 出路是链的错位, 参照链第 $n$ 点对主线链第 $n+1$ 点. 在格里, 主线状态在层 2 上的差已有走过的 $N_0, N_1$ 的保留 (判断, 读 `Walk` 的状态累加), 所以错位后同层对齐可能够, 外加 ℕ-极限的重排 (一份对两份). 这条没有试.
> - `PortLo`, `PortHi`: `HtFeedFold` (高度 $\Omega$, 动作 `Act′`) 与 `SumOneFold` 的互模拟. 两个折叠逐句对应, 但目标的下标不同 (`HtFeedFold.Tg W t m` 带任意世界 $m$; `SumOneFold.Tg t W` 的世界是 `wm τ`), `cv` 的写法不同 (`tg↑` 对 `cmpF` 加 `nw`), 顶层另有 `ŷ`. 判断: 机械, 但量大.
>
> 估计 (判断): `SwapHi` 一千行上下 (`StrRel` 在 $\Lambda=2$ 固定世界约一千七百行, 这里要对层归纳并放开世界); `SwapLo` 更多, 而且错位加重排是否够没有定理; `Port` 八百到一千五百行. 都没有否定的迹象, 也都没有做.
>
> **只管序数值.** `Funext` 没有用到. 强度一律按 $\psi_0(\Omega_x)$ 写: `T-Ω` 读 $\psi_0(\Omega_\Omega)$ 仍是判断.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtVal where

open import OCF.Align.HtValSplit using (sum-drp≤; ≤sum-drp; u′; module Split; module M; T-Ω≡; s₀≡) public
open import OCF.Align.HtValAct using (Dif′; Ωd′; Ωd≡; Step′; Act′; module R; T-Ω′; s₀′≡; v0≤v0′; v0′≤v0) public
open import OCF.Align.HtValNeg using (Z0; L2; outA; outA′; outA≡; outA′≡; yes0; no0; no-pointwise; T-Ω≇T-Ω′) public
```

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `Split.Ψ≡`, `v-zero`, `a-zero`, `v-suc`, `a-suc` | HtValSplit | 闭项的第 0 层输出 = 第一个 `n1` 的输出接回灌的 ℕ-和; 格的层的递推 (对任意动作) | 定理 (`refl`) |
| `Split.v-step` | HtValSplit | $v_n\lhd v_{n+1}$ | 定理 |
| `sum-drp≤`, `≤sum-drp`, `Split.T≤lim`, `Split.lim≤T` | HtValSplit | `drp` 不改值; 闭项与 $\lim v_n$ 互相 $\le$ | 定理 |
| `T-Ω≡`, `s₀≡` | HtValSplit | `T-Ω` 是主线动作的实例; 第一个 `n1` 上输出 $\omega\cdot(1⨾0)$ | 定理 (`refl`) |
| `Ωd≡` | HtValAct | 主线的 $\Omega_{b+1}$ 是参照写法删去 $\mathrm{Dif}_b$ | 定理 (`refl`) |
| `T-Ω′`, `Act′`, `Ωd′`, `Dif′` | HtValAct | 参照动作与参照闭项 (验收用, 不进主线) | 定义 |
| `s₀′≡`, `v0≤v0′`, `v0′≤v0` | HtValAct | 第 0 格两边都是 $\omega$ | 定理 |
| `outA≡`, `outA′≡` | HtValNeg | 两个动作在空状态、层 2 目标上的输出 | 定理 (`refl`) |
| **`no-pointwise`**, `yes0`, `no0` | HtValNeg | 保 "有层 0 节点" 的关系不能把参照输出放在主线输出之下 | 否定, 定理 |
| **`T-Ω≇T-Ω′`** | HtValNeg | 主线闭项与参照闭项不 $\cong$ | 否定, 定理 |
| `path′`, `t12`, `c12` | HtValTest | `T-Ω′` 与 `T₀`: 分开 `T-Ω` 的路径上相同, 宽 3 深 12 同形; 对照: `T-Ω` 与 `T₀` 在同一比较器下分开 | 有限测试 |
| `T-Ω≈lim`, `T-Ω′≈lim` | HtValAccept | `trA` 下闭项与格的极限值相等 | 定理 (验收文件) |
| `swapLo₀`, `swapHi₀` | HtValAccept | `SwapLo`, `SwapHi` 的第 0 格 | 定理 |
| **`lo`**, **`hi`**, `T-Ω≈B` | HtValAccept | `PortLo → SwapLo → BTBOᴵ ≼ trA T-Ω`; `PortHi → SwapHi → trA T-Ω ≼ BTBOᴵ` | 条件定理 |
| **`loᴱ`**, `B≼ᴱ`, **`hiᴱ`** | HtValAcceptE | 同上, 经 `⟪_⟫` 对 `treeE 2` 与 `BTBOᴵ` | 条件定理 |
| `PortLo`, `PortHi`, `SwapLo`, `SwapHi` | HtValAccept | 缺的四个树侧命题 | 未走通 |
| `T-Ω` 读 $\psi_0(\Omega_\Omega)$ | — | — | 判断 |

**条件定理的前提** (Agda 类型原样, 都在 `HtValAccept` §2):

    PortLo = T₀ ≤ T-Ω′                           PortHi = T-Ω′ ≤ T₀
    SwapLo = ∀ n → Σ ℕ (λ m → R.v n ≤ M.v m)     SwapHi = ∀ n → Σ ℕ (λ m → M.v n ≤ R.v m)

可满足性 (判断): 四条按读法都成立 ($\psi_0(\Omega_\Omega)$ 的两种写法); `Port` 有宽 3 深 12 的测试支持; `Swap` 的第 0 格是定理. 没有一条被否定.

## 翻译账

| 新增 | 来源 | 类 |
|---|---|---|
| `Split` (对任意动作的闭项与格) | `HtFeedClosed.At` 的字面, 动作抽成参数 | 无新构造子; 提供信息 (定出 $\Omega_t$ 只经动作进来) |
| `Dif′`, `Ωd′`, `Act′`, `T-Ω′` | 逐句抄 `SumOneTree.Dif`, `Ωd` (旧树的写法, 不是记号) | 只作验收的参照物, 不进主线; 是 `EndLowT` 出路 (a) 的闭项 |
| `Z0`, `no-pointwise` | 由 `Ωd≡` 的删除逼出: 删掉的是低层节点 | 否定, 划出 "逐点比动作" 不能有 |
| 第 4 层逼出 | 无: 主线定义一个没改 (作者 11-05 定) | — |

**按 AGENTS 归类: 提供信息.** 没有新构造子或节点字段, 没有改树、折叠、`Ωd`; 标签只在两个验收文件. 一步定理: `Split` 对一切动作. 这一站新用到的字段: `RKy hz` (回灌), `κc` 的 `v`, `a`, `Walk` 的层区间, `Step` 里的 `Ωd t`.

## 审计

- **编译** (从仓库根, 退出码不经管道): 树侧 `HtValSplit`, `HtValAct`, `HtValNeg`, 入口: 各 0, 峰值约 0.5G, 几秒到几十秒. `HtValTest`: 0, 约 290 秒, 峰值约 0.45G. `HtValAccept`: 0, 约 7 秒, 峰值约 1.3G. `HtValAcceptE` (要归档拷贝): 0, 约 25 秒, 峰值约 3.4G.
- **禁用构造**: 七个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 不用 `Funext`; 都带 `--safe --without-K --lossy-unification`.
- **导入闭包** (`importclosure.py`, `--only OCF.Align.CumReadCF --only OCF.Align.TLRule --only OCF.Align.SumOne --only OCF.Align.HtFeed --only OCF.Align.HtGen --only OCF.Align.HtCross --only OCF.Align.MonoPort --only OCF.Align.StrRel --only OCF.Align.GenAbs --only OCF.Align.KVal --only OCF.Align.NoCumsum --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.HtVal`): `HtValSplit` 20 个模块 (本地 10), `HtValAct` 21 (本地 11), 禁用表 0, `--only` 之外 0, 退出码 0. `HtValNeg`, `HtValTest`, 入口导入 `EndLowTShape` (走路径的比较器与 `path`, 树侧), 要再加 `--only OCF.Align.EndLowT`: `HtValNeg`, `HtValTest` 各 27 个模块 (本地 16), 入口 28 (本地 17), 禁用表 0, 之外 0, 退出码 0. 两个验收文件闭包含记号, 不审.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 验收: `HtValAccept:lo` 1077/0/0, `hi` 1077/0/0 (`BTBOᴵ` 经 `T₀≈`, 切片里不到记号模块), `HtValAcceptE:loᴱ` 1551/91/83, `hiᴱ` 1551/91/83. 树侧: `HtValAct:T-Ω′` 117/0/0, `Act′` 45/0/0, `v0≤v0′` 122/0/0, `HtValNeg:no-pointwise` 36/0/0, `T-Ω≇T-Ω′` 189/0/0, `HtValAccept:T-Ω≈lim` 236/0/0.
- **行数** (代码块里非空非注释行): `HtValSplit` 88, `HtValAct` 49, `HtValNeg` 44, `HtValTest` 26, `HtValAccept` 37, `HtValAcceptE` 15, 入口 5. 合计 264.
- **编译配方**: `agda --library-file=<含 stdlib 与 cubical 的库文件> -i src -i probes probes/OCF/Align/HtVal.lagda.md +RTS -M6G -RTS` (同样编译 `HtValTest`, `HtValAccept`). `HtValAcceptE` 另要归档拷贝: `cp -R archive/src/Mahlo <arch>/`, `<arch>/arch.agda-lib` 写 `name: htval-arch`, `depend: standard-library-2.4`, `include: .`, `flags: --hidden-argument-puns -W noUnsupportedIndexedMatch`, 编译加 `-i <arch>` (归档模块的接口若没有, 按 [EndLow](EndLow.lagda.md) 文末分步编译).
