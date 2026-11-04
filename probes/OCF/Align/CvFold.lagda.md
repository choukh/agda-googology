# 折叠输出满足 `Cv` 吗

> 入口. **判决: PARTIAL.** 第一个由折叠产出、读坐标的 `ni` 节点满足 `Cv`, 证明对折叠走第 0 层坐标的那一步是一般的 (编译过); 由此 `SumOneClosed.Δ₀` 在目标第 1 层输出里不含 `nκ` 的两段值上互译 (`Pk-round`, `A-round`). 输出里 `nκ` 那一段没有做 (分支里有链, 要折叠对高层输入值同余). 带上下文的层单调与 $\psi_0(\Omega_{\Omega+1})$ 的上界没有做, 暂停. 没有反例. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; 不读记号.

## 1 三个结果

**和对加数的值同余** ([CvFoldSub](CvFoldSub.lagda.md)). `S-congʸ`: 同一世界上 $0+y\preccurlyeq 0+y'$ 推出 $b+y\preccurlyeq b+y'$, 对一切第 1 层差树 (含 `ni`, `nκ`). 证法是换底 (`Sub`): $b+y$ 就是把 $0+y$ 的底换成 $b$, 换底保持 $\preccurlyeq$ (`Sub-mono`). 推论 `Cv⁰→Cv`: `Cv` 只要对底 $0$ 验, 即 "分支的值对规范坐标不变".

**折叠走第 0 层坐标, 对规范坐标值不变** ([CvFoldRun](CvFoldRun.lagda.md)). 对象是 `SumOneFold.Run` 本身 ($S=\cdot\omega$ 的实例), 输入是第 0 层差树 $z$, 动作 `A₀` 任意, 只要满足 `HA`: 动作一步之后状态在目标第 1 层的值只单调地依赖之前的值. 结论 `canon`: 从值小的状态走 `cw z` 不超过从值大的状态走 $z$, 反之亦然. 证明只用和的结构: 单位, 结合, 平移不变 (`TI`), 加法分解 (`DEC`), `toA` 与 `dif` 的往返 (`C`, `ZL`).

**第一个实例** ([CvFoldInst](CvFoldInst.lagda.md)). `mid₁` (`Δ₀` 在目标第 1 层的输出) $=$ `A ⨾ (Pk ⨾ nκ …)`.

- `StepV`: `Step` 一步之后的值只单调地依赖状态的值 (由 `S-congʸ`). 所以 `HA` 成立.
- `Kn-CO`: 折叠在目标第 1 层上走顶层节点 `ni self (λ _ _ _ → n1)` 得到的树, 不含 `nκ`, 满足 `Cv⁰`, 对一切满足不变量 `Gs` 的状态. 这个树的分支在坐标 $z$ 上是 `Step (Y₂ ⊕ Run z …)` (`SumOneFold` 的 `RKi` keep, `BNi`, `Ai`), 读坐标.
- `Pk-CO`, `Pk-round`: `Pk` 是这种树前面接一个 `n0`, `toB (difT Pk) ≈ toB Pk`. `A-CO`, `A-round`: `A` 同 (它的分支不读坐标).

## 2 定理表

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `Sub-S`, `Sub-mono`, `S-congʸ`, `S-congʸ≈` | CvFoldSub | 和对加数的值同余 | 定理 |
| `Cv⁰`, `Cv⁰→Cv` | CvFoldSub | `Cv` 对底 0 验即可 | 定义, 定理 |
| `refl⊑`, `⨾-mono`, `nl-mono`, `unit-l`, `unit-r`, `assoc` | CvFoldRun | 走第 0 层坐标的结构律 (前提 `HA`) | 条件定理 |
| `TI`, `DEC`, `C`, `ZL` | CvFoldRun | 读回差的形状 (前提 `HA`) | 条件定理 |
| **`canon`** | CvFoldRun | `cw z ~ᴼ z` (前提 `HA`) | 条件定理 |
| `StepV` | CvFoldInst | `Step` 对状态的值单调, 给出 `HA` | 定理 |
| `Gd-Step`, `Gd-cv`, `Gd-Run` | CvFoldInst | 不变量 `Gs` (目标第 1 层的差树 `Ok no` 且 `Cv⁰`) 沿 `Step`, `cv`, `Run` 保持 | 定理 |
| **`Kn-CO`** | CvFoldInst | 折叠产出的读坐标节点满足 `Cv⁰` 与 `Ok no` | 定理 |
| **`Pk-round`**, `A-round` | CvFoldInst | `mid₁` 不含 `nκ` 的两段值上互译 | 定理 |

`canon` 的前提 `HA` 在实例里由 `StepV` 给出, 所以 `Kn-CO`, `Pk-round` 无前提.

## 3 范围和没有做的

- **`nκ` 那一段.** `mid₁` 的第三段是 `nκ tt (λ c → yc (Kb …))`. 它的分支在世界 $c>1$ 上走顶层节点 `ni {k = c}`, 目标第 1 层低于 $c$, 走 `RKi` 的 rise: 链 `Chn` 走状态在第 $c$ 层的差树. 要它满足 `Cv`, 需要折叠对**第 $c\ge1$ 层输入**值同余; 这里只做了第 0 层输入. 而且 `nκ` 本身读不回 (`LayerTrFold.mid-κ`, `LayerTr` §3), 所以 `round-Cv` 用不上. 判断: 两件事无关. `Cv` 管 `ni` 的坐标, `nκ` 的回程卡在极限世界 (要从前面各支的极限到 $g(c)$ 的字面第一位置路径, 或 $g$ 在 $c$ 处连续). `Cv` 给不出这两样.
- **一般的值同余.** 只证了 $z$ 与 `cw z` 一对: 规范化不变. 一般的 "第 0 层输入值相等 ($\mathrm{sum}\,0\,z\approx\mathrm{sum}\,0\,z'$) 则输出值相等" 没有做. 还缺一条: 读回的差走起来对 $A$ 树的 $\le$ 单调 (`dif` 沿 $f\,n\lhd\lim f$ 的分解). 判断能做, 是 `DEC` 的同类.
- **带上下文的层单调, $\psi_0(\Omega_{\Omega+1})$ 的上界.** 没有做, 暂停. 判断: 它要折叠对第 $\ge1$ 层输入的单调 (链走高层差树), 与上一条同属折叠对高层输入值同余, 本轮只到第 0 层输入.
- **反例.** 没有找到折叠输出不满足 `Cv` 的例子, 也没有编译的否定. 可能破坏 `Cv` 的位置 (判断): `Run` 在高层输入上的规则 (`RKi` rise 的 `Chn`, `Walk`/`Cut` 沿字面路径) 读高层差树与层的字面形状; 第 0 层坐标上的规则 (`Run` 的 `n0`, `n1`, `⨾`, `nl`, `nw`) 已证不破坏 (`canon`).

## 4 世界

值前序 `≼` 的 `bi`, `bκ` 取一切更大世界上的分支, 所以树的值依赖它所在的世界. `S-congʸ` 只在同一世界上陈述. 第一次的证法 (直接定义布劳威尔树的加法 $b\oplus t$) 在抬升底时要把 $t$ 的分支限制到更大的世界, 值可能变小, 结合律证不出; 换底 (`Sub`) 不移动世界, 所以过. 这是判断, 没有编译那条失败的证法.

## 5 有限测试

没有单独的有限测试. `Pk-CO` 由检查器把 `mid₁` 归约到 `n0 ⨾ ni …` 的形状再套用一般定理; 这是对具体项的归约, 算作定理.

## 6 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `CvFoldSub`, `CvFoldRun` | 无 | 提供信息 |
| `CvFoldInst` | 用 `SumOneClosed` 的闭项与折叠 ($S=\cdot\omega$ 抄自旧折叠) | 提供信息, 形状受旧树影响 |

## 审计

见报告.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CvFold where

open import OCF.Align.CvFoldSub using (Sub; Sub-S; Sub-mono; S-congʸ; S-congʸ≈; Cv⁰; Cv⁰→Cv) public
import OCF.Align.CvFoldRun
open import OCF.Align.CvFoldInst using (StepV; Gs; Kn; Kn-CO; Aᵐ; Pk; A-CO; Pk-CO; Pk-round; A-round) public
```
