# 折叠对值同余: 第 0 层输入做完, 第 1 层输入暂停

> 入口. **判决: PARTIAL.**
>
> - 第 2 项 (一般值同余): **完成**. `CvHighCong.cong0`: 第 0 层输入 $\mathrm{toA}\,z\le\mathrm{toA}\,z'$ 时, 折叠 (`SumOneFold.Run`, 动作满足 `HA`) 从值小的状态走 $z$ 不超过从值大的状态走 $z'$. 实例 `CvHighInst.Kn-mono`: `mid₁` 里那个读坐标的节点, 分支对坐标的值单调, 无前提.
> - 第 1 项 (推到第 1 层输入): 没有做, 暂停. 下一个障碍见 §2.
> - 第 3 项 (带上下文的层单调, $\psi_0(\Omega_{\Omega+1})$ 的上界与验收): 没有做, 暂停. 它依赖第 1 项.
> - 第 4 项: 没有反例, 也没有编译的否定.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; 不读记号.

## 1 定理

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `G` | CvHighCong | 第 0 层布劳威尔树的第一位置无环 | 定理 |
| `T` | CvHighCong | 沿复合路径读差走起来就是分段读 | 条件定理 (`HA`) |
| `PI`, `PI′`, `PIL`, `L4′` | CvHighCong | 读回的差与路径、与合法性证明无关 | 条件定理 (`HA`) |
| `pre-le`, `lim-leP`, `infl`, `infl-r` | CvHighCong | 极限的部分和是上确界; 走什么都不低于起点 | 条件定理 (`HA`) |
| `M` | CvHighCong | $a\le b$ 则读回的差 $\mathrm{dif}\,a\sqsubseteq^{\mathsf O}\mathrm{dif}\,b$ | 条件定理 (`HA`) |
| **`cong0`**, `cong0≈`, `cong-sum` | CvHighCong | 第 0 层输入值单调 / 值同余 | 条件定理 (`HA`) |
| **`Kn-mono`**, `Kn-cong` | CvHighInst | 折叠产出的读坐标节点的分支对坐标值单调 | 定理 (`HA` 由 `StepV` 给) |

**证法要点.**

- `PI` 在极限处不比较两条路径的下标. 一边每个部分和都被另一边某个部分和压住: 用尾路径 (`L4′`) 读到 $h(k+n)$, 再用另一条链的尾路径走到 $h(m+(k+n))$. 两边下标的等式 (`+-comm`) 只出现在路径的类型里, 由 `substD` 搬.
- 自身到自身的非平凡路径用 `G` 排除.
- `PI` 不对两条都是 `self` 的路径做模式匹配 (那要 K); 改成对起点带一条等式 (`PI′`).

## 2 第 1 项: 停在哪里

**`HA` 对读坐标的动作不成立.** `CvFoldRun` 的前提 `HA` 要求动作一步之后的值对**一切**坐标 $w,w'$ 单调地只依赖状态的值. 第 0 层坐标上, 实例的动作是 `Step`, 不读坐标, 所以成立. 第 1 层输入 $x$ 的 `ni` 分支 $u$ 在折叠里变成动作 `Ai`: 在坐标 $w$ 上跑 `Run (u (Int w …))`. $u$ 读坐标时, 这一步的值依赖 $w$, `HA` 就不成立 (判断; `LayerTrNeg.xᶜ` 那样的 $u$ 给出不同值).

**要的接口 (判断, 没有写).**

1. 把 `HA` 换成带坐标的 `HAᶜ`: 状态值 $\preccurlyeq$ 且坐标的第 0 层值 $\le$, 则一步之后值 $\preccurlyeq$.
2. 把 `canon`, `cong0` 改成同时跟踪坐标的值. 走 $x ⨾ y$ 时坐标是 `w ⨾ nw q x`, 值是 $w+x$; `DEC`, `PI` 的每一步都要多带一条坐标不等式.
3. 对 `Ai` 证 `HAᶜ`. 这要三件:
   - `Int` 对 $z$ 值单调;
   - 输入分支 $u$ 对坐标值单调, 这正是 `Kn-mono` 那种结论, 也就是第 0 层的归纳结论;
   - `Run` 对第 1 层输入树 $u(c)$ 值单调, 这是第 1 层的归纳假设.

所以对层归纳的形状是: 第 $k$ 层输入的值单调 ⟸ 第 $k$ 层分支的坐标值单调 (第 $k-1$ 层的结论) + `Int` 单调 + 对 $u(c)$ 的同一命题 (结构归纳). 第 0 层这一圈已经闭合 (`cong0`, `Kn-mono`).

**rise 分支另有一件.** `RKi` 的 rise 在目标 $t$ 低于节点层 $k$ 时出现. `Chn` 走状态在第 $k$ 层的差树 $\delta_n$, 值的泛函要换成目标 $t$ 上的值. 目标 0 时是第 0 层的和 (`sum`), 还要加上回灌读层 `sum W (z Y)` 之后沿字面的层 (`Walk`, `Cut`) 走: 那一步对层的值单调, 本轮没有碰.

## 3 第 3 项

暂停. 带上下文的层单调 $a\preccurlyeq b\Rightarrow\psi_0(X+\Omega_a)\preccurlyeq\psi_0(X+\Omega_{\mathrm{next}\,b})$ 要折叠对第 $\ge1$ 层输入单调 (§2), 本轮只到第 0 层输入. 上界与 `SumOneAccept.step-T₁` 的合并没有做.

## 4 有限测试

无.

## 5 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `CvHighCong` | 无 | 提供信息 |
| `CvHighInst` | 用 `SumOneClosed` 的折叠 ($S=\cdot\omega$ 抄自旧折叠) | 提供信息, 形状受旧树影响 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CvHigh where

import OCF.Align.CvHighCong
open import OCF.Align.CvHighInst using (br; Kn-mono; Kn-cong) public
```
