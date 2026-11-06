# `nκ` 的值语义: 入口

> **判决: PARTIAL.** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> 1. **关系 (HOLDS).** [KValTree](KValTree.lagda.md) 的 $\sqsubseteq_{[m]}$, 两档. `lo`: [DValTree](DValTree.lagda.md) 的构造子, `ni⊑` 的分支改成**跨世界**比. `hi`: 多一条 `κ⊑`, 分支**按层的值**对齐 ($c\le c'$ ⇒ $u(c)\sqsubseteq_{\mathsf{lo}}u'(c')$, 两边各自单调 `KMono`), 右边树世界不高于左边 ($V'\le V$); 分支只在 `lo` 档, 所以**不嵌套**.
> 2. **折叠单调, 跨世界, 两档一个证明 (条件定理).** [KValSound](KValSound.lagda.md) `snd kh`: 除 `κ⊑` 外的每个构造子一步, 两边可以在不同世界里折叠 (目标第 0 层), 上下文是状态的路径一致与值可比, `hi` 档另加回灌层可比 $W+z\le W'+z'$. `κ⊑` 那一格是参数 `kh`. **`snd-lo = snd tt` 无此参数**: `lo` 档的跨世界单调是定理 (动作前提 `HA⁺`, `Step` 满足, [KValInst](KValInst.lagda.md) `mono-lo` 无前提).
> 3. **`κ⊑` 的单层情形: 树侧一半做完, 折叠侧一半未完成.** 树侧 ([KValCut](KValCut.lagda.md)): 区间和 `Cut u [a,b)` 的包含式对齐 **`CutM`** ($a'\le a$, $b\le b'$ 按值 ⇒ 区间和相关), 以及复合 `T`, 与路径无关 `PI`, 尾路径 `TailE`, 全是定理. 折叠侧还缺两步 (§3): `Walk` 与 `Run (Cut …)` 值相同; 回灌的各格拼成一个区间和. 所以 `kh` 没有构造出来, `hi` 档的单调**未走通 (未完成, 不是否定)**.
> 4. **路径一致 (HOLDS).** [KValSem](KValSem.lagda.md): 状态在一切到第 0 层的路径上值相同, 则**任何**第 1 层输入 (含 `ni`, `nκ`) 的输出也如此 (`coh₁`), 换世界不改值 (`cv≤`, `≤cv`). 这是跨世界比较必须先有的: `nκ` 的格读 `z⊲ v`, 格里 `ni` 的链从 `κ₀ ll` 起, `cv` 经 `cmpF` 换路径.
> 5. **嵌套 `nκ`: 未走通.** 纸面上找到一个机制 (判断, 未编译): 外层两边的回灌层序列 $v_n\le v'_n$ 时, 同一层 $c$ 在右边可能落在**更低**的格世界里 (例: 左 $1,2,4,8$, 右 $1,3,7,15$, 层 $4$ 左边在世界 $8$, 右边在 $7$). 分支里的内层 `nκ` 走 $[c, \text{格世界}+z)$, 右边就短了. 所以 "包含式" 与 "平移式" 对齐在嵌套时都需要外层提供的上下文, 而 `snd` 的格的上下文里没有 "格世界可比" 这一条 (那正是 `lo` 档不要 `Hℓ` 的原因). 没有编译的否定.
> 6. **共同目标 `MonoTarget` 的最低一站: 未反驳, 未证明** ([KValMonoTest](KValMonoTest.lagda.md)). 按作者 2026-11-05 的决定先试反驳: `Hs.MonoStep (hs hz)` 纸面两边都是 $\varepsilon_0$ 型的链, 右边每项不低; 有限测试 `G 1` 左 $4$ 右 $32$. 没有反驳. 证明要 `DValZero.chain` 在 `HtFeedFold` 上的同形物 (判断, 约 500 行), 没有做.

## 1 定义

    data _⊑[_]_ : D one V → Md → D one V′ → Set        -- Md = lo | hi
      n0⊑ n1⊑ ⨾⊑ nl⊑ nwˡ nwʳ trˡ trʳ u0* u1* as* pre⊑ lim⊑      任一档, 同 DValTree
      ni⊑ : (三条跨世界的分支前提, lo 档) → ni u ⊑[ m ] ni u′
      κ⊑  : V′ ≤ V → KMono u → KMono u′ → (c ≤ c′ ⇒ u c ⊑[ lo ] u′ c′) → nκ u ⊑[ hi ] nκ u′

语义 (`KValSound.OutLe m`): 两边 `Sd` (世界, 合法性, 输入层路径, 动作), `Ok` (动作前提 `HA⁺` 三条, 路径一致两条), 上下文 `Cx m` (状态路径一致两条, 规范路径上的值可比, `hi` 档另加 $\ell\le\ell'$), 结论对一切底 $c\le c'$: $c+\mathrm{out}\le c'+\mathrm{out}'$.

## 2 定理

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `_⊑[_]_`, `KMono`, `rf-κ`, `up-hi` | KValTree | 关系与判据 | 定义, 定理 |
| `coh₀`, `coh₁` | KValSem | 状态路径一致 ⇒ 输出路径一致, 对一切第 0, 1 层输入 | 条件定理 (动作路径一致) |
| `cohCv`, `cv≤`, `≤cv`, `nl-drp`, `drp≤` | KValSem | 换世界不改值; `drp` 不改和 | 定理 |
| `cong0`, `chain` | KValZero | `DValZero` 的跨世界版 | 条件定理 (`HAᶜ` 三条) |
| **`snd`** | KValSound | 两档的跨世界单调, `κ⊑` 交给参数 | 条件定理 (`kh`, 动作 `Ok`) |
| **`snd-lo`** | KValSound | `lo` 档的跨世界单调 | 条件定理 (动作 `Ok`) |
| `HA-Step`, `Coh-Step`, **`mono-lo`** | KValInst | `Step` 满足前提; `lo` 档在 `Step` 上下文里单调 | 定理 |
| `uκ-not-KMono`, `no-10` | KValInst | `¬κ-refl` 的反例分支不满足 `κ⊑` 的判据 | 定理 (否定) |
| `CutX`, `CutRf`, `T`, `PI`, `L4′`, `TailE` | KValCut | 区间和: 同路径对齐, 复合, 与路径无关, 尾路径 | 定理 (前提 `KMono`) |
| **`CutM`** | KValCut | 包含式对齐: $a'\le a$, $b\le b'$ ⇒ `Cut u [a,b) ⊑ Cut u′ [a′,b′)` | 定理 (前提 `KMono` 两条, 对齐一条) |
| `MonoTarget`, `MonoTarget₁` | KValMonoTest | 共同目标的陈述 | 定义 |
| `target≡` | KValMonoTest | `MonoTarget₁` 字面是两个读数的 $\le$ | 定理 |
| `test-G1-lhs`, `test-G1-rhs` | KValMonoTest | `G 1` 两边 $4$, $32$ | **有限测试** |

**否定的范围.** `uκ-not-KMono` 只说 `DValNeg.uκ` 不满足判据, 所以 `¬κ-refl` 不否定 `κ⊑`. 本组没有别的否定; 嵌套与 `MonoTarget` 都只写 "未走通"/"未证明".

## 3 第一个障碍: 回灌的各格拼成一个区间和

`κ⊑` 的单调要证 (判断, 下面每一步的依据都在):

- 第 $n$ 格: 世界 $v_n$, 状态 $S_n$, 走 $[a_n,v_n)$ (`Walk`). 先证 `Walk` 的输出与 `Run (Cut u v_n …)` 值相同 (两边按路径平行展开, 每格一次 `snd-lo` 的自比; 坐标不同但 `lo` 档不读第 1 层坐标). **没有写.**
- 前 $n$ 格合起来与 `Cut u [V, a_n)` 在一个世界里走一次值相同: 每次换世界 `cv` 不改值 (`cv≤`, `≤cv`), 相邻两段由 `T` 拼起来, 跨世界由 `snd-lo` 的自比. **没有写.**
- 于是左边前 $n$ 格 $\approx$ `Cut u [V, a_n)`, 右边同; $a_n=v_{n-1}\le v'_{n-1}=a'_n$ (归纳, 起点 $\ell\le\ell'$ 由 `Hℓ`), $V'\le V$, 用 **`CutM`** 与 `snd-lo` 比. 极限由 `l≤`, `≤l`.

这里用不到逐格的对齐 (逐格时右边格的起点更高, 是 "平移" 问题); 用整段的包含式对齐就绕过了. 估计还要 300–400 行. 单层的障碍是工作量, 不是已知的数学障碍 (判断).

嵌套时 (入口判决 5) 这条路断在格的上下文: 格里的分支要 `hi` 档的上下文, 而格世界 $v_n$ 与 $v'_m$ 不可比.

## 4 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `KValTree` | 无. 两档由 "格在不同世界里跑" 逼出; `ni⊑` 跨世界由同一原因逼出; `κ⊑` 按值对齐由 `DValNeg.¬κ-refl` 逼出, $V'\le V$ 由回灌的起点 (`κc` 的 `a = W₀`) 逼出 | 提供信息 |
| `KValSem` | 无. 路径一致由 `nκ` 读 `z⊲ v`、链读 `κ₀ ll`、`cv` 经 `cmpF` 逼出 | 提供信息 |
| `KValZero`, `KValSound` | 无. `DValZero`, `DValSound` 的跨世界版; 新用到的字段: 状态的 $z$ 在 `z⊲ W` 上的读数 (`Hℓ` 的推进 `hℓ⊕`) | 提供信息 |
| `KValCut` | 无. `CvHighCong` §4–§6 对 `Cut` (带分支的 `dif`) 搬; 起点不能取 $0$, 所以对两端归纳, 用尾路径 | 提供信息 |
| `KValInst`, `KValMonoTest` | 无. `Step` 抄自旧折叠 ($S=\cdot\omega$) | 提供信息, 折叠形状受旧树影响 |

没有新构造子, 没有新折叠规则, 不用 `Lab`. 一步定理与新用到的字段: `snd` 的 `ni⊑` 一步用链的起点 (状态在 `κ₀ ll` 上的差) 与两个世界里各自的 `Ai`; `CutM` 的后继一步用一格的分支对齐, 极限一步用 `L4′` (左) 或 `TailE` (右); `coh₁` 的 `nκ` 一步用 `RKy` 的 `azero` 子句不看路径.

## 5 审计

- `importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRule --only OCF.Align.TLOpsW --only OCF.Align.SumOne --only OCF.Align.BrwMid --only OCF.Align.LayerTr --only OCF.Align.CvFold --only OCF.Align.CvHigh --only OCF.Align.CvLayer --only OCF.Align.NoCumLit --only OCF.Align.L1Val --only OCF.Align.DVal --only OCF.Align.HtGen --only OCF.Align.HtFeed --only OCF.Align.HtCross --only OCF.Align.KVal OCF.Align.KVal`: 闭包 48 个模块 (本地 38, 库 10), 禁用表命中 0, `--only` 之外 0, OK. 编译器保证的不引用; 不说明定义没有受记号启发.
- `depslice.py` (语法级近似): `KValSound:snd` 到达 251 块, `KValInst:mono-lo` 266, `KValInst:uκ-not-KMono` 277, `KValSem:coh₁` 151, `KValMonoTest:MonoTarget` 119, `KValCut:CutM` 72, `KValTree:_⊑[_]_` 35; 记号模块块数都是 0, 别处记号词 0. 正对照 `Om1HnAccept:label-term₀`: 到达 1188, 记号模块 92 块, 别处 58.
- agda 代码行 (非空, 代码块内): KVal 9, KValTree 76, KValSem 155, KValZero 208, KValSound 252, KValCut 148, KValInst 58, KValMonoTest 27, 合计 933.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KVal where

open import OCF.Align.KValTree public
open import OCF.Align.KValSem using (CohY; CohD; CohA; coh₀; coh₁; cohCv; cv≤; ≤cv) public
open import OCF.Align.KValZero using (module S₀; cong0; chain)
open import OCF.Align.KValSound using (Sd; Ok; Cx; OutLe; HA⁺; KH; KX; snd; snd-lo) public
open import OCF.Align.KValCut using (CutX; module One; module Two) public
open import OCF.Align.KValInst using (HA-Step; Coh-Step; mono-lo; uκ-not-KMono) public
open import OCF.Align.KValMonoTest using (MonoTarget; MonoTarget₁) public
```
