# NegValW (入口): 带世界证据的模拟, 否定一路

> 不含记号. 与构造一路 [ValW](ValW.lagda.md) 配对, 共用接口 [ValWIf](ValWIf.lagda.md) (接口定稿 2026-11-05 23:43; 本路不改它). 作者本轮选定原话: "值定理: 带世界证据的模拟". 第 4 层: 只新增关系与定理, 不改树, 折叠, 合法性. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延 (连前提也没有).
>
> **对纲领与目标.** 纲领 1: 一切值的比较在 `HB S⊥` (布劳威尔树) 上, 用 `NegLeanLvVal._≤_`. 纲领 2: 无公理. 纲领 3: 本路的定理只比较带字面证据的东西 (同一个目标世界, 或 $W\le W'$ 的证据, 或同一棵 $\Lambda$ 之下的两个第一位置); `no-cell-≤` 说的正是某一对世界之间**没有**这样的证据. 纲领 4: 本路不读记号. 目标 "让树自足": 本路把 "回灌提高值" 这条值定理要穿过的三处写成编译过的实例 (状态清零, 数据对世界不单调, 结点跨层与 `keep`/`rise` 分裂), 并证明接口的律 X1, X2 是盲的、X3 至少包含同一折叠对层与世界的单调. 这些都不说明回灌不提高值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegValW where

open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Relation.Nullary using (¬_)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbSt using (SLs; ΛF; lΛF; oneF)
open import OCF.Lean.LeanFbTm using (bkS; fb)
import OCF.Lean.NegValWReset
import OCF.Lean.NegValWInst
import OCF.Lean.NegValWBlind
import OCF.Lean.ValWIf
```

## 主要的一对 (`TL` 的折叠对 `TF` 的折叠) 上的盲定理

接口的模块参数取 `TL` 与 `TF` 的那一组 (`T = SLs`, 底种类 `bkS`, 最高层 `ΛF`, 左 `λ _ → inj₂ tt`, 右 `fb`).

```agda
module Main = OCF.Lean.NegValWBlind SLs bkS ΛF lΛF oneF (λ _ → inj₂ tt) fb
module MainIf = OCF.Lean.ValWIf SLs bkS ΛF lΛF oneF (λ _ → inj₂ tt) fb

main-blind : MainIf.SimW
main-blind = Main.blindSim

main-no-RunPres : ¬ MainIf.Goals.RunPres Main.blindSim
main-no-RunPres = Main.Bld.no-RunPres

main-no-Cross0 : ¬ MainIf.Goals.Cross0 Main.blindSim
main-no-Cross0 = Main.Bld.no-Cross0
```

## 定理表

| 名字 | 文件 | 陈述 | 档 |
|---|---|---|---|
| `strict`, `no-hs⊲`, `above` | Reset §1 | $\mathrm{hs}\,a\lhd b \Rightarrow b\not\lhd a$; $\neg(\mathrm{hs}\,a\lhd a)$ | 定理 |
| `Cells.reset-z₁`, `reset-z` | Reset §2 | 回灌每一格 ($\forall n$, $\forall F$) 的状态 `z₁`, `z` 为 `n0` | 定理 (`refl`) |
| `Cells.lossy-row`, `fed-cell` | Reset §2 | 有损行用状态 $Y$; 回灌第 $n$ 格用 `SA (c n)` | 定理 (`refl`) |
| `start-L`, `start-R` | Reset §2 | 新种类闭包第 0 格的界: 左 $\mathrm{rd}_1(\beta, z_1Y)$; 状态 `z₁ ≡ n0` 时右 $\beta$ | 定理 |
| **`no-cell-≤`** | Reset §2 | 前提 `Pos lW (z₁ Y)`: 左右 `κc₁` 第 0 格的世界之间没有 $\le$ (任何 $w_A$) | 定理 (条件; 前提实例 `pos-Y1`, `pos-after`) |
| `after-n1`, `pos-after` | Reset §3 | $\Omega_\Lambda$ 第一步 `n1` 在 `Stp` 下之后的 `z₁` 满足 `Pos` | 定理 |
| **`anti`**, `outL≡`, `outR≡` | Inst §2 | 实例 `T₁ = step S⊥`, $\Lambda_1$: 同一数据, $W\le W'$, 读数左 $\omega$ 右 $0\cdot\omega$, 左 $\not\le$ 右 | 定理 |
| `lvl-L`, `lvl-R`, `Ωd-br` | Inst §3 | $\Omega_{\Lambda_1}$ 闭包分支的结点: $W$ 里第 1 层, $W'$ 里第 3 层 | 定理 (`refl`) |
| **`rk-split`** | Inst §3 | 同一目标 (层 2, 世界 $W'$): 左 `keep (ss hself)`, 右 `rise` | 定理 (`refl`) |
| **`blindSim`** | Blind §1 | `SimW` 被 "只在第 0 对第 0 层有内容" 的 `Bl` 满足 | 定理, 对一切实例 |
| **`Bld.no-RunPres`**, **`Bld.no-Cross0`** | Blind §3 | 对 `Bl`, X3 与 `Cross0` 不成立 | 定理, 对一切实例; 主要的一对见上 `main-no-RunPres`, `main-no-Cross0` |
| **`Forced.mono`** | Blind §4 | 前提 `SimW`, `RunPres`: $\Omega_{\mathrm{ly}_1}@W_1$ 的第 0 层读数 $\le$ $\Omega_{\mathrm{ly}_2}@W_2$ ($\mathrm{ly}_1\lhd\mathrm{ly}_2$, $W_1\le W_2$, 动作与状态输出 $\Omega$) | 条件定理 (X3 的必要条件) |

## 只否定什么, 不否定什么

- `no-cell-≤`: 只否定 "回灌行里, 关系逐格 (同下标) 在新种类闭包 `κc₁` 里要右世界 $\ge$ 左世界" 这一做法. **适用范围**: 只在数据里出现新种类闭包 (`nc (inj₂ tt)`) 时; 接口的判断是 `ΛF = up Λs` 不含新种类 $\Omega$-结点, 那时折叠不经过 `κc₁` (判断, 本路没有写成对折叠全程的定理), 所以它对主要的一对**不构成**障碍, 而是说明接口的 `StX` 只比 `d` 这一选择离不开那条判断.
- `anti`: 只否定 "对一切数据" 的世界单调. 不说 $\Omega_L$ 与 `Int` 产出的数据不单调.
- `rk-split`: 只否定逐构造子同形的输出关系 (如 `ValNewRel.Mo`) 穿过跨层的结点; 不否定把 `ni` 与 `nl` 相连的关系. 它是接口 `RkR` 的 `kr` 情形的一个具体实例 ($k_1=1\lhd t=2\lhd k_2=3$), 说明 `kr` 确实出现.
- `no-RunPres`, `no-Cross0`: 只否定 "X1, X2 足以推出 X3 / `Cross0`". 不否定存在满足 X3 的关系.
- `Forced.mono`: 不是否定. 取 `fb₁ = fb₂` 时, 它说 X3 蕴含同一折叠在这组 $\Omega$ 输入上对层与世界单调. 本路没有找到这条单调的反例, 也没有证它.

## 有限测试

本路没有新的有限测试. 引用: `LeanFbTest.sz-5`, `sz-7L` (`TF` 与 `TL` 在深度 $\le7$ 的有界展开结点数相同), 回灌行离根比预算深 (`LeanLvShape.exec-TVs2`, 11 步). 这只说明测试的比较器在这一深度上没有分辨力, 不是值相等的证据. 本路**没有**证出 `TF` 与 `TL` 值相等, 也没有证不等.

## 判断 (不是定理)

- 构造一路的 X3 要处理三件事: 数据的世界单调谓词 (`anti` 说明不能省); 跨层的结点与 `kr` (`lvl-L/R`, `rk-split`); 并且至少包含 `Forced.mono`, 即此前各路未证的 "跨世界的值单调" (`GoodUp`, `TpMonoIf` (b), `ValTK.DomW`). 这三件是否是全部, 是判断.
- 接口的目标 `Cross0` 只到 $\le$. 即使证出, 严格 (`TL` $<$ `TF`) 还要另一步; `NegLeanLvVal.absorb-D` 说明回灌行逐格严格推不出闭项严格, 严格的那一步要回灌格不被有损格的常数倍界住.
- 任务里提到的 "回灌增量在常数倍之内则闭项值与全有损互相 $\le$" (把 `absorb-D` 推广到折叠层面) 本路没有做: 第 0 层的输出经 `feed0` (级层 0, 读回 `sum`) 又抬高世界, 值相等的两份输出给出不同的世界, 所以它不是对 `sum` 的同余, 要一条跨世界的关系 (判断).

## 文件

| 文件 | 内容 |
|---|---|
| [NegValW](NegValW.lagda.md) | 入口; 主要的一对上的盲定理 |
| [NegValWReset](NegValWReset.lagda.md) | 回灌格清零状态; `κc₁` 起点世界不可比 (不依赖接口) |
| [NegValWInst](NegValWInst.lagda.md) | 小实例: `anti`, `lvl-L/R`, `rk-split` (不依赖接口) |
| [NegValWBlind](NegValWBlind.lagda.md) | 对接口: 盲定理与 `Forced.mono` |
