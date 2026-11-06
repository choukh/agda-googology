# 单层 `nκ` 的值语义: 入口

> **判决: HOLDS (单层), mid₁ 那一段未做.** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`. 接 [KVal](KVal.lagda.md) (那里的文件一个没改).
>
> 1. **`kh : KH hi` 构造出来了, 所以 `snd-hi = snd kh` 是定理** ([KValKHi](KValKHi.lagda.md)): `KValTree` 的 `hi` 档 (含 `κ⊑`: 分支按层的值对齐, 右边树世界不高于左边, 分支在 `lo` 档) 推出折叠在目标第 0 层**跨世界**单调. 前提只有两边动作的 `Ok` (`Step` 满足) 与上下文 `Cx hi` (状态路径一致, 值可比, 回灌层 $W+z\le W'+z'$). `mono-hi` ([KValKInst](KValKInst.lagda.md)) 是 `Step` 上下文里的推论.
> 2. **一格 = 一个区间和** ([KValKWalk](KValKWalk.lagda.md)): `Walk` 与 `Run (Cut …)` 值相同, 两个方向 (`WCf`, `WCb`), 输出路径一致 (`cohW`).
> 3. **前 $n$ 格 = 一棵树 `Pre n`** ([KValKIter](KValKIter.lagda.md)): 部分和与状态两边都对上 (`cl`, 四件, 对 $n$ 归纳); `Pre n` $\approx$ `Cut u [V,a_n)` (`PreCut`, 树侧); 层 $v_n$ 与 $\ell+$ 部分和值相同 (`vpt`, `ptv`).
> 4. **判据不空, 反例被排除** (KValKInst): $\sum_{c\ge V}\sum_{z:0}1$ 自比 (`rf-κΩ`); `DValNeg.¬κ-refl` 的那一对不在 `hi` 档里 (`¬rel-κκ`, 由 `snd-hi` 推出).
> 5. **`mid₁` 的 `nκ` 段自比: 没有做.** 要三件: `mid₁` 前两段在 `lo` 档 (跨世界的 `ni` 判据) 自比, 那是 `DValKn.Kn-Rf` 的跨世界版; `nκ` 的分支 `c ↦ yc (Kb … c)` 对层的值单调, 而这个分支是在层 $c$ 上对第 $c$ 层差走链得到的第 1 层树, 要折叠对第 $c\ge1$ 层输入的值同余 (`CvFold` 入口已指出, 现有定理只到第 0 层输入). 判断: 第三件是真正的下一步, 量级与 `DValZero`+`DValCanon` 相当, 而且要对层 $c$ 一致地做.

## 1 证明的结构

`κ⊑` 一格 (`kh`):

    第 n 个部分和  ≈  从 cv Y 走 Pre n         (cl: WCf/WCb + 跨世界 snd-lo + cv≤/≤cv)
    Pre n          ≈  Cut u [V, a_n)           (PreCut: T, PI)
    Cut u [V,a_n)  ⊑  Cut u′ [V′, a′_n)         (CutM: V′ ≤ V, a_n = v_{n-1} ≤ v′_{n-1})
    v_{n-1} ≤ v′_{n-1}                          (vpt, ptv, 第 n-1 步的结论, ℓ ≤ ℓ′)

`mono-n` (部分和) 与 `PP` (`Pre` 的比较) 互相调用, $n$ 递减. **用的是整段的包含式对齐, 不是逐格**: 逐格时右边第 $n$ 格从更高的层起步 (平移问题), 整段时只要起点 $V'\le V$ 与终点可比.

## 2 定理

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `cohW` | KValKWalk | 一格的输出路径一致 | 条件定理 (`Ok`, 状态一致) |
| **`WCf`, `WCb`** | KValKWalk | 一格 `Walk` 与 `Run (Cut …)` 值相同 (状态可比时, 两个方向) | 条件定理 (`KMono`, `Ok`) |
| `rfPre`, `cohSv`, `cvv`, `PC⁺`, `PC⁻`, `Wk⁺`, `Wk⁻` | KValKIter | `Pre n` 自比; 格的状态一致; 两个格世界之间的一步 | 条件定理 (同上) |
| **`cl`** | KValKIter | 前 $n$ 格 ≈ 走一次 `Pre n` (部分和与状态, 四件) | 条件定理 (同上) |
| `vpt`, `ptv` | KValKIter | $v_n\approx\ell+$ 部分和 | 定理 |
| **`PreCut`** | KValKIter | `Pre n ≈ Cut u [V, a_n)` | 定理 (前提 `KMono`) |
| **`kh`** | KValKHi | `κ⊑` 的处理 | 定理 |
| **`snd-hi`** | KValKHi | `hi` 档跨世界单调 | 条件定理 (`Ok`, `Cx hi`) |
| `mono-hi` | KValKInst | `Step` 上下文里的 `hi` 档单调 | 定理 (前提是状态的三条, 可满足) |
| `mono-uΩ`, `rf-κΩ`, `rf-1κΩ` | KValKInst | $\sum_{c\ge V}\sum_{z:0}1$ 满足判据并自比 | 定理 |
| `¬rel-κκ` | KValKInst | `¬κ-refl` 的那一对不在 `hi` 档里 | 定理 (否定) |

**有限测试.** 无.

**范围.** 单层: `κ⊑` 的分支在 `lo` 档, 不含 `nκ`. `ni` 的分支也在 `lo` 档, 所以 `ni` 分支里的 `nκ` 也不在范围内. 嵌套仍是 `KVal` 判决 5 的 "未走通".

## 3 第一个障碍

`mid₁` 的 `nκ` 段 (入口判决 5): 分支对层 $c$ 的值单调, 要折叠对**第 $c$ 层输入**的值同余, 对一切层 $c\ge1$ 一致. 现有的值同余只对第 0 层输入 (`CvHighCong.cong0`, `DValZero.cong0`, `KValZero.cong0`). 这是把 $\psi_0(\Omega_{\Omega+1})$ 的第 1 层链 (`T₁`) 接到 `snd-hi` 上之前缺的那一步; `T₁` 的后几项还要嵌套的 `nκ`.

## 4 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `KValKWalk` | 无. 一格与区间和的对应读自 `SumOneFold.Walk` 与 `SumOneTree.Cut` 的子句 (两者同形) | 提供信息 |
| `KValKIter` | 无. `Pre n` 的形状读自回灌的 `κc` (格的起点 $a_{n+1}=v_n$, 路径 `ap` 复合); 无新构造子 | 提供信息 |
| `KValKHi` | 无. 整段对齐代替逐格, 由平移问题逼出 | 提供信息 |
| `KValKInst` | 无. `Step` 抄自旧折叠 ($S=\cdot\omega$); `A⁺` 抄自 `DValNeg` | 提供信息, 折叠形状受旧树影响 |

没有新构造子, 没有新折叠规则, 不用 `Lab`, 闭包定理没有为 `nκ` 新增专属前提 (`κ⊑` 的前提在 `KVal` 里已定). 一步定理与新用到的字段: `WCf`/`WCb` 的后继一步用一格的分支 (`u (ap ⨾ p)`), 极限一步用 `WRp` 与 `Rpt` 的平行推进; `cl` 的一步用格的世界 $v_{n+1}$、状态 `cv (Sv ⊕ Δ)` 与 `ap` 的复合; `kh` 的一步用 `Hℓ` (回灌层 $W+z$).

## 5 审计

- `importclosure.py` (同 `KVal` 的 `--only` 列表) `OCF.Align.KValK`: 闭包 43 个模块 (本地 33, 库 10), 禁用表命中 0, `--only` 之外 0, OK. 只保证不引用.
- `depslice.py` (语法级近似): `KValKHi:kh` 到达 329 块, `KValKHi:snd-hi` 330, `KValKInst:mono-hi` 345, `KValKInst:¬rel-κκ` 379; 记号模块块数都是 0, 别处记号词 0. 正对照 `Om1HnAccept:label-term₀`: 1188, 92, 58.
- agda 代码行 (非空, 代码块内): KValK 6, KValKWalk 103, KValKIter 138, KValKHi 42, KValKInst 43, 合计 332.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KValK where

open import OCF.Align.KValKWalk using (module W) public
open import OCF.Align.KValKIter using (module It) public
open import OCF.Align.KValKHi using (kh; snd-hi) public
open import OCF.Align.KValKInst using (mono-hi; rf-κΩ; rf-1κΩ; ¬rel-κκ) public
```
