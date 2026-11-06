# 跨层值同余: 入口

> **判决: 未走通 (第 2 件), 归结与测试完成.** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`. 接 [KVal](KVal.lagda.md), [KValK](KValK.lagda.md), 那里的文件一个没改.
>
> 1. **`mid₁` 归结为三件** ([KValCMid](KValCMid.lagda.md), 定理): `mid₁` 字面是 `Aᵐ ⨾ (Pk ⨾ nκ tt uMid)` (`mid≡`, `refl`); `rf-mid : PkRf → MidMono → Rfᵏ hi mid₁`; 第一件 `rf-Aᵐ` 无前提成立. 剩 `PkRf` (`Pk` 在 `lo` 档自比) 与 `MidMono` (`KMono uMid`), 两者都导出为 `Set`.
> 2. **`MidMono` 先试反驳, 没有反驳出来** ([KValCTest](KValCTest.lagda.md), 有限测试). `MidMono` 推出层 $1$ 与层 $\lim_n1$ 的分支值相同、不超过层 $2$ 的. 三个值的基本列读数 `G 0` 都是 $0$ (`refl`); `G 1` 三个都在 4G 堆内耗尽, 没有读数. 所以测试没有分辨力. 纸面 (判断): 层 $\lim_n 1$ 的分支与层 $1$ 的只差在 $\Omega_{\lim_n1}$ 的差树多出一段 $\lim_m 0$ (`Dif` 在极限处的尾段全是空区间), 看不出让值变小的机制; 层 $2$ 的差树多一个第 $1$ 层节点, 链只会更长.
> 3. **第 2 件 (跨层值同余) 未走通.** 分支 $u(c)$ 是在世界 $c$ 里, 对第 $c$ 层的差 (第 $c$ 层树) 走链, 读目标第 1 层. 要比 $u(c)$ 与 $u(c')$ 就要一族关系 $R_{c,c'}$ 在第 $c$ 层树与第 $c'$ 层树之间, 满足: (i) 目标第 1 层的输出在 `⊑[ lo ]` 里相关; (ii) 目标第 $c$ 层对第 $c'$ 层的输出仍在 $R_{c,c'}$ 里 (链才能接下去); (iii) 走第 $c$ 层树时, 第 $1\le k<c$ 层的节点在目标第 1 层上升, 走状态在第 $k$ 层的差, 所以 $R$ 还要管一切中间层, 并且左右的中间层要**按层的值**对齐 ($c<c'$ 时右边多出的层只能往上加). 这是一族按层编号的逻辑关系, 就是 `CvLayer` §3 说的跨层值语义. 判断: 不能由 `KValZero`/`KValSound` 的第 0 层值同余直接推出 (那里输入的值是 `A` 里的序数, 这里输入的 "值" 本身就是关系). 本轮没有写出它.
> 4. **第 1 件 (`PkRf`, 跨世界的 `Kn-Rf`) 与第 3 件 (接 $\psi_0(\Omega_{\Omega+1})$ 的链), 粗上界: 没有做.** 第 1 件判断可行 (照 `DValKn` 搬到 `lo` 档, `cong1` 改成跨世界, 约 350 行), 但它单独不推出 `Rfᵏ hi mid₁`.
> 5. **对 `MonoPort` 的 (b)**: 本组**没有**给出 "第 1 层树在第 1 层目标上的输出对关系封闭" ($\delta_n\sqsubseteq\delta'_n\Rightarrow\delta_{n+1}\sqsubseteq\delta'_{n+1}$). 第 3 点的 (ii) 取 $c=c'=1$ 就是它, 在 `SumOneFold` 上; 未做.

## 1 定理

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `κBr`, `uMid` | KValCMid | 取出 `mid₁` 的 `nκ` 分支 | 定义 |
| `mid≡` | KValCMid | `mid₁ ≡ Aᵐ ⨾ (Pk ⨾ nκ tt uMid)` | 定理 (`refl`) |
| `rf-Aᵐ` | KValCMid | `Aᵐ` 在 `lo` 档自比 | 定理 |
| **`rf-mid`** | KValCMid | `PkRf → MidMono → Rfᵏ hi mid₁` | 条件定理 |
| `PkRf`, `MidMono` | KValCMid | 剩下两件的陈述 | 定义 |
| `test-G0` | KValCTest | `G 0` 三者为 $0$; `G 1` 未算出 | **有限测试** (无分辨力) |

## 2 第一个障碍

见判决 3: 一族按层编号、按层的值对齐中间层的关系 $R_{c,c'}$, 对折叠在第 1 层目标与第 $c$ 层目标上的输出同时封闭. `KVal` 的 `κ⊑` 是这种对齐在 "层" 这一个坐标上的特例 (分支按层对齐), 这里要的是在差树内部的每个节点层上都这样对齐.

## 3 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `KValCMid` | 无. 拆分读自 `mid₁` 的归约形状 | 提供信息 |
| `KValCTest` | 无. 测试 | (测试) |

没有新构造子, 没有新折叠规则, 不用 `Lab`.

## 4 审计

- `importclosure.py` (同 `KVal` 的 `--only` 列表) `OCF.Align.KValC`: 闭包 44 个模块 (本地 34, 库 10), 禁用表命中 0, `--only` 之外 0, OK.
- `depslice.py`: `KValCMid:rf-mid` 152 块, `KValCMid:MidMono` 141, `KValCTest:test-G0` 138, 记号模块 0, 别处记号词 0. 正对照 `Om1HnAccept:label-term₀`: 1188, 92, 58.
- agda 代码行: KValC 4, KValCMid 27, KValCTest 28.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KValC where

open import OCF.Align.KValCMid using (uMid; mid≡; rf-Aᵐ; rf-mid; PkRf; MidMono) public
open import OCF.Align.KValCTest using (vOne; vLim; vTwo) public
```
