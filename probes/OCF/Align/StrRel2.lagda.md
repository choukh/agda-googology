# 结构关系, 第二轮: `CellStep` 的桥与第 0 格: 入口

> **判决: PARTIAL.** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 接 [StrRel](StrRel.lagda.md); 没有改任何已有文件.
>
> 1. **桥 (HOLDS).** [StrRel2Pos](StrRel2Pos.lagda.md): `Walk` 的位置 `WP` 逐句照 `Walk` 的三个子句定义; `⊲-tr` 的复合拆成两段 (`wL`, `wR`, `wS`, 层不变; 尾巴的类型不看里面的路径, `tailP`/`WRp` 的下标 $m+n$ 不用搬); 沿 `sum-fst v x` 的位置与树的位置 `Sp x` 一一对应 (`toW`, `fromW`, 层是 $v+\mathrm{pre}\,s$). 极限那一句只在 `toW` 一边要 $n+0=n$ (`+-identityʳ`, 对 $\mathbb N$ 下标的 `subst`).
> 2. **首对齐落到 `Walk` 上 (HOLDS), 两个折叠都有.** **`walkHead`** (`HtFeedTree` 的第 0 层树, 即 `HtFeedFold.Walk`) 与 **`walkHeadᴼ`** (`SumOneTree` 的第 0 层树, 即 `SumOneFold.Walk`, 经 `ofS`): 两格坐标 $d\sqsubseteq_0 d'$, 起点 $v\le v'$ ⇒ 左格 `Walk` 的每个位置有右格 `Walk` 的位置, 层 $\le$, 领先量 $\mathrm{Adm}(c,c';v+d,v'+d')$. 路径与格世界**正是** `KNest2Glue.CellStep` 第 $n+1$ 格的 (`κc (suc n)` 的 `av = sum-fst (v c) d₀`, 格世界 `sum (v c) d₀`).
> 3. **第 0 格: 只由值对齐推出 LPO (否定, 编译过).** [StrRel2Neg](StrRel2Neg.lagda.md) **`phead→LPO`**: 对任意两条合法路径, 在 `CellStep` 的值前提 ($a\le a'$, $\mathrm{Adm}(a,a';W,W')$) 下把左边 `Walk` 的位置送到右边、保持领先量的过程推出 LPO. 只杀 "任意字面路径 + 值" 的做法. 第 0 格的路径 `⊲-tr q₀ (sum-fst W z)` 的前一段 $q_0$ 正是这种路径.
> 4. **语义换成结构的 (`OutLeᴬ` → 给出 $\sqsubseteq_0$ 的观察), `kstep`/`snd²` 走一遍: 未做.** 见 §2, 是这一轮的第一个障碍. 不是否定.
> 5. **"树世界可比" 能否去掉.** 第 $n+1$ 格不要它: 起点 $v_n\le v'_n$ 是上一格给的 (`kstep` 里本来就是 `inj₁`), `walkHeadᴼ` 只要 $v\le v'$. 第 0 格: 它不够. `PHead` 带着 $a\le a'$ 仍推出 LPO, 所以有了可比性, 只由值在任意 $q_0$ 上对齐仍不行. 判断: 第 0 格要 $q_0$ 也由推导给出结构; 到那时右边起点低的情形 ($V'<V$, 恒等对齐) 是否可避免, 未查.
> 6. **`MonoPort3Gen`**: 没有接 (本轮没写和结构的语义步骤, 无处可省).

## 1 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `WP`, `lev`, `levL` | StrRel2Pos | `Walk` 的位置与层 | 定义 / 定理 |
| `wL`, `wR`, `wS`, `lg-tr` | StrRel2Pos | `⊲-tr` 的位置拆成两段, 层不变 | 定理 |
| `lgFst`, `toW`, **`fromW`** | StrRel2Pos | `sum-fst v x` 的位置 ≅ `Sp x`, 层 $=v+\mathrm{pre}\,s$ (`HtFeedTree`) | 定理 |
| `sO≤`, `≤sO`, `lgFstᴼ`, `toWᴼ`, **`fromWᴼ`** | StrRel2Pos | 同上, `SumOneTree`, 层 $\approx$ | 定理 |
| **`walkHead`**, **`walkHeadᴼ`** | StrRel2Pos | 坐标结构相关 ⇒ 两格 `Walk` 的位置首对齐, 带领先量 | 定理 |
| `cancel` | StrRel2Neg | $c+x\le c+y$ ⇒ $x\le y$ (布劳威尔树上构造的) | 定理 |
| `phead→vhead`, **`phead→LPO`** | StrRel2Neg | 任意路径上只由值对齐 ⇒ LPO | **否定, 定理** |
| `CellStep`, 结构的 `kstep`/`snd²` | — | 见 §2 | 未走通 |

**有限测试.** 无. "`Walk` 的输出在每个 `WP` 位置上恰调一次 `Run`" 是由定义同形看出的判断, 没有写成定理.

## 2 第一个障碍: 结构的观察要一直推到 `KVal` 的 `lo` 档 (判断)

`CellStep` 的第 $n+1$ 格要 $d_n\sqsubseteq_0 d'_n$, 它是第 $n$ 格的输出关系. 所以格的结论要给出结构关系, 这又要求格里每个位置上分支的输出 (`SX u u′`) 是结构的. 往下追, 依据都是 `KNest*` 的定义:

1. `snd²` 的 `n1²` 一句用动作的 `HA⁺` (`KValSound.Ok`), 它只给值. 要加一条结构的动作前提. `Step` 满足它 (同 `StrRelChain.HA-Stepˢ`).
2. `snd²` 的 `lo²` 一句交给 `KValSound.snd-lo`. 它的 `ni⊑` 按值对齐坐标, 并且有 `lim⊑`; 链经 `KValZero.chain` 套 `Gen`. 要的是 `StrRel` 在 `SumOne` 折叠上、两边世界不同的版本. 形状已在 `StrRelZero`/`StrRelSound` 里 (世界固定, $\Lambda=2$); 跨世界与 `cv` 的路径一致 (`KValSem.cv-l`/`cv-r`) 要改写成结构的 (`cv` 只包 `nw`, 对 $\sqsubseteq_0$ 透明, 估计不难).
3. 上下文 `Cxᴬ` 要加状态在第 0 层上的结构关系. 第 0 格的路径还用到状态的 $z$ 分量, 所以 $z$ 也要结构相关.
4. 格之内: 有了 1 到 3, 对 $d\sqsubseteq_0 d'$ 的推导归纳. 位置的对应用 `walkHeadᴼ`, 输出的拼接要 `Walk` 沿 `⊲-tr` 的**输出**拆分 (本轮只拆了位置). 那里分支取在 `⊲-tr ap (⊲-tr p q)` 与 `⊲-tr (⊲-tr ap p) q` 两条命题相等的路径上, 由 `SX u u` 自比换过去.

估计 (判断): 1 到 4 合计 1200 到 1800 行, 主要是 2 (约等于 `StrRel` 的 700 行加跨世界). 第 0 格另算 (见判决第 5 条).

## 3 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `WP`, `lev` | 逐句照 `Walk` 的子句 | 树侧, 计算 |
| `wL`/`wR`/`wS`, `lgFst` | `sum-fst` 在 `⨾` 处是 `⊲-tr`; `Lg` 不是命题, 中点的合法性取 `lg⊲ q lb` | **树逼的** |
| `toW`/`fromW` 的 $m+0$ | `Walk` 尾巴的下标 | 树逼的 (一处 `subst`) |
| `PHead` | `CellStep` 的值前提 | 树侧, 否定 |

**归类: 提供信息.** 没有新构造子或节点字段, 没有改树或折叠, 没有 `Lab`, 没有记号. 一步定理: `toW`/`fromW` 对一切树, `walkHead` 对一切推导. 否定定理划出不能有的: 第 0 格 "任意路径 + 值" 的对齐 (`phead→LPO`).

## 4 审计与账

- 编译: 删掉本组 `StrRel2*` 的 `.agdai` 后从头编译入口, 退出码 0. 三个文件无禁用构造, 不出现 `Funext`.
- 导入闭包 (`--only` 同 [StrRel](StrRel.lagda.md)): 入口 26 (本地 16), `Pos` 23 (13), `Neg` 25 (15); 都是禁用表 0, `--only` 之外 0, 闭包里没有 `DValCanon`/`MonoPortZero`/`MonoPort2Zero` (`ofS` 本地重写一份).
- 定义级切片 (到达 / 记号块 / 别处记号词): `walkHead` 85/0/0, `walkHeadᴼ` 107/0/0, `fromWᴼ` 73/0/0, `phead→LPO` 112/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58.
- 代码行: `StrRel2Pos` 235, `StrRel2Neg` 45, 入口 4, 合计 284.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel2 where

open import OCF.Align.StrRel2Pos using (WP; lev; wL; wR; wS; toW; fromW; toWᴼ; fromWᴼ; walkHead; walkHeadᴼ) public
open import OCF.Align.StrRel2Neg using (PHead; cancel; phead→LPO) public
```
