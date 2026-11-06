# 对层归纳的值单调: 第一步

> 入口. **判决: PARTIAL.**
>
> - 第 1 项的接口: **完成.** `CvLayerRun`: 前提换成带坐标的 `HAᶜ`; `canon`, `cong0` 改成同时跟踪三样: 底, 状态的值, 坐标的第 0 层值.
> - 对 `Ai` 证 `HAᶜ`: **只做了一类输入.** 第 1 层输入 `xs`, 分支是坐标抬上来 (`↑`). `AiH` 成立, 由此 `KL-mono`: 折叠在目标第 1 层上走 `xs` 产出的 `ni` 节点, 分支对坐标的值单调. 这是第一个读坐标的第 1 层输入. 一般的 "折叠对第 1 层输入树值单调" (分支里还有 `ni`, `nκ`) 没有做, 未走通 (§2).
> - 第 2 项 (rise 分支回灌读层后沿字面的层走): 没有做, 暂停. 判断见 §3.
> - 第 3 项: 暂停.
> - 第 4 项: 没有反例.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; 不读记号.

## 1 定理

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `Ob`, `OutLe`, `_⊑_`, `HAᶜ` | CvLayerRun | 带底、状态值、坐标值的走; 第二件 `toA z ≤ toA z′` 让 `⨾` 之后坐标可比 | 定义 |
| `⨾-mono` … `assoc`, `pre-le`, `lim-leP`, `TI`, `DEC`, `Cc`, `ZL`, `T`, `PI`, `L4′`, `M` | CvLayerRun | 同 `CvFoldRun`, `CvHighCong`, 前提换成 `HAᶜ` | 条件定理 |
| **`canon`**, **`cong0`**, `cong-sum` | CvLayerRun | 规范化值同余; 第 0 层值 $\le$ 则走起来 $\preccurlyeq$ (前提 `HAᶜ`) | 条件定理 |
| `Tr.Up`, `Tr.Down` | CvLayerInst | 第 1 层走 `↑ z` 与第 0 层走 $z$ 值互相 $\preccurlyeq$ (前提: 两个动作对应) | 条件定理 |
| `AiH` | CvLayerInst | `xs` 的 `Ai` 满足 `HAᶜ` | 定理 |
| **`KL-mono`**, `KL-ni` | CvLayerInst | 折叠走 `xs` 产出 `ni` 节点, 分支对坐标的值单调 | 定理 |

`HA` (不读坐标) 是 `HAᶜ` 的特例, `StepV` 给它. `HAᶜ` 的前提对读坐标的动作可满足: `AiH`.

**第二件不要消去律.** `toA z ≤ toA z′` 这一件全部由结构律 (`⨾`, `nl`, 单位, 结合) 拼出. `TI`, `DEC`, `PI` 等都是这些律的复合, 所以照抄 `CvHighCong` 的证明就带上了.

## 2 第 1 层输入: 停在哪里

`AiH` 的证法: `Ai` 的一步是折叠走 `u w`. 对 `xs`, `u w = ↑ w` 里没有节点, 所以可以搬到第 0 层 (`Up`, `Down`), 用第 0 层的 `cong0` (它靠规范形 `dif ∘ toA` 与 `M`).

一般的 $u(w)$ 是第 1 层的树, 里面有 `ni`, `nκ`, 两棵树 $u(w)$, $u(w')$ 形状不同. 要比折叠在它们上的值, 第 0 层的办法是走规范形. 第 1 层的规范形是 `LayerTrOne.dif₁ ∘ toB`, 它有两处不够 (都是已有的结论):

- `nκ` 没有读回 (`LayerTr` §3, 极限世界). 而 $\psi_0(\Omega_{\Omega+1})$ 的计算里折叠要走的第 1 层状态树含 `nκ` (`LayerTrFold.mid-κ`).
- 有 `ni` 时往返只在 `Cv` 下保值 (`round-Cv`; 反例 `no-round`), 而且读回对 $\preccurlyeq$ 单调 (第 1 层的 `M`) 没有做.

所以对层归纳停在 "第 1 层树之间比折叠的值". 这是未走通, 没有否定定理. 判断: 绕开规范形, 要直接给折叠在第 1 层树上的值一个只依赖输入值的刻画 (像第 0 层的 `M`), 而第 1 层的值前序跨世界、分支取上确界, 树之间的比较不对应结构.

## 3 第 2 项 (rise, 回灌读层)

没有做. 判断: 目标第 0 层时 `RunK` 取层 $v=$ `sum W (z Y)`, 再沿 $v$ 的字面路径走 (`Walk`, `Cut`). 每一格在层 $c'$ 上折叠顶层节点 `ni {k = c′}`, 链 `Chn` 走状态在第 $c'$ 层的差树. 要说 "对层的值单调", 得比两个值相等而字面不同的层 $v$, $v'$, 也就是比第 $c'$ 层与第 $c''$ 层的差树. 那是不同的类型, 这里没有跨层的值语义 (`LayerTr` 只做了第 1 层). 这件事在第 1 项之后.

## 4 有限测试

无.

## 5 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `CvLayerRun` | 无 | 提供信息 |
| `CvLayerInst` | 用 `SumOneClosed` 的折叠 ($S=\cdot\omega$ 抄自旧折叠) | 提供信息, 形状受旧树影响 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CvLayer where

import OCF.Align.CvLayerRun
open import OCF.Align.CvLayerInst using (↑; xs; KL; AiH; KL-mono; KL-ni) public
```
