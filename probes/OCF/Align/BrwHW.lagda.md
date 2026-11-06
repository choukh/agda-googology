# 折叠的输出是否世界稳定 (`HW`)

> 入口. 第 1 层的 View `view₁` ([BrwViewKappa](BrwViewKappa.lagda.md)) 与它的良基 `view₁ᵂ` ([BrwWfOne](BrwWfOne.lagda.md)) 都以 `HW` (世界稳定, 遗传) 为合法性. `HW` 不是无条件的 (`BrwViewLift.not-HW`). 这里问: 主线上折叠实际产出的第 1 层树满足 `HW` 吗? 对象是 `SumOneClosed` 的 $\psi_0(\Omega_\Omega)$ 一步 `Δ₀` 在目标第 1 层的输出 `mid₁ = Aᵐ ⨾ (Pk ⨾ κ段)` ([CvFoldInst](CvFoldInst.lagda.md), [LayerTrFold](LayerTrFold.lagda.md)). 不读记号, 不用 `Funext`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> **判决: PARTIAL.**
>
> 1. **前两段是定理.** `Aᵐ` (`Step` 的输出) 与 `Pk` (含一个由折叠产出、**分支读坐标**的 `ni` 节点 `Kn`) 都 `HW` (`HW-A`, `HW-Pk`). 更一般: 对一切满足不变量 `Good` 的状态, `Kn w Y` 都 `HW` (`HW-Kn`). `Good` 在 `Step`, `⊕`, 换世界 `cv` 下保持, 沿第 0 层坐标的 `Run` 也保持 (`RunR`, 跨世界的模拟). 所以 `view₁` 与 `view₁ᵂ` 对它们都适用 (`view-A`, `view-Pk`).
> 2. **第三段 (`nκ` 段) 暂停.** `HW mid₁` 化归为 `HW (κD mid₁)` 一条 (`HW-mid`, 编译过), 它要两件, 都没有做:
>    (a) `nκ` 节点自己的 `WSq`: 一个方向 (大世界 ≼ 小世界) 是 `Ksuf` 的 $\preccurlyeq$ 版, 无条件可得 (判断, 未编译); 另一个方向要 "对每个层 $c\ge W$ 找 $c'\ge W_2$ 使 $[W,c]$ 上的段不超过 $[W_2,c']$ 上的段", 要分支对层的**值**单调, 就是 [KVal](KVal.lagda.md) 里 `κ⊑` (`hi` 档) 未走通的那一件.
>    (b) `nκ` 的分支 (`Kb` 的输出, 在层 $c$ 上跑 $\Omega_c$ 节点的上升链, 坐标是状态在第 $c$ 层的差) 都 `HW`: 要把 `RunR` 推广到折叠的一切构造 (`RunNi`, `Ai`, `Int`, `Chn`, `Walk`, `RunK`, ...), 是 `KValSound.snd` 在目标第 1 层上的同形物. 没有做.
>
>    没有找到反例, 也没有编译的否定. 只能写 "暂停".
> 3. **第 2 层的 `Rv`/`wf₁`: 没有做.** 仓库里没有第 2 层的翻译 (第 2 层的布劳威尔树、`toB`、View), 不便宜. 判断: `Rv` 的论证只用 "大世界的分支是小世界分支的一部分", 与层号无关.
> 4. **`HtFeedFold`: 不适用.** `HW` 定义在 `SumOneTree` 的 `D one W` 上; `HtFeedFold` 的树是 `HtFeedTree.D` (按高度加下标), 它在第 1 层还没有 View, `HW` 在那里没有意义. 要先有那边的 View.

## 1 方法 ([BrwHWBase](BrwHWBase.lagda.md))

`WSq` 只比同一棵树在 $W$ 与更大的 $W'$ 里的值. 对读坐标的节点, 左边在 $(W'',p,y)$ 的分支要对右边某个分支, 而 $W''$ 与 $W_2$ 互不可比. 所以换成更强的、可合成的关系:

```text
R2 x x′ = ∀ q q′ l l′ → b ≈ b′ → S q l b x ≈ S q′ l′ b′ x′      -- 两棵树, 各沿任意路径抬到任意世界
Sh z z′                                                           -- 两个世界上的第 0 层坐标形状相同 (nw 可插, 极限逐项)
UI u u′ = ∀ r r′ l l′ → Sh w w′ → R2 (u r l w) (u′ r′ l′ w′)
R2-ni : UI u u′ → R2 (ni (ss self) u) (ni (ss self) u′)           -- 左支 (W″,p,y) 对右边世界本身 (self) 上的同一 y
R2→WSq : R2 x x → WSq x
```

积分跨世界逐段比 (`Ic`), 坐标 `dif y` 在两个世界上形状相同 (`Sh-dif`).

## 2 折叠 ([BrwHWFold](BrwHWFold.lagda.md))

`Good Y = RS Y Y × HWs Y`: 状态在目标第 1 层的差对一切目标路径两两 `R2`, 且都 `HW`. 保持它的是一步的结构定理: `⊕R`, `StepR` ($\Omega_1$ 的 `R2-Ω`), `cvR` (对 `cmpF` 的两个结果各一行), `RunR` (对坐标的形状 `Sh` 归纳, 两边在**不同的世界**里沿形状相同的坐标折叠). `Kn` 的分支是 `Step (cv Y ⊕ Run z …)`, 所以 `UI-br` 是这几条的合成, `HW-Kn` 由 `R2-ni` 得到.

## 3 定理

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `Sh-dif`, `Ic`, `R2-ni`, `R2→WSq` | BrwHWBase | 坐标形状; 积分跨世界; `ni` 节点跨世界; `R2` 推出 `WSq` | 定理 |
| `R2-Ω`, `HW-Ω` | BrwHWBase | $\Omega_1$ 的差树在一切世界之间 `R2`, 并且 `HW` (推广 `HW-Ωx`, 世界任意) | 定理 |
| `⊕R`, `StepR`, `cvR`, **`RunR`** | BrwHWFold | 状态关系在 `⊕`, `Step`, `cv`, 沿第 0 层坐标的 `Run` 下保持 (跨世界) | 定理 |
| `HW-⊕`, `HW-Step`, `HW-cv`, `HW-Run` | BrwHWFold | `HW` 一半同样保持 | 定理 |
| **`HW-Kn`**, `R2-Kn` | BrwHWFold | 对一切 `Good` 状态, 读坐标的节点 `Kn w Y` `HW` (且跨世界 `R2`) | **定理** |
| **`HW-A`**, **`HW-Pk`** | BrwHWFold | `mid₁` 的前两段 `HW` | **定理** |
| `HW-mid` | BrwHW | `HW (κD mid₁) → HW mid₁` | 定理 (化归) |
| `view-A`, `view-Pk` | BrwHW | `view₁` 用在 `Aᵐ`, `Pk` 上 (部分良基由 `view₁ᵂ`) | 定理 |
| `nκ` 段的 `HW` | — | (a) 节点 `WSq` 要分支对层值单调; (b) 分支 `HW` 要 `RunR` 推广到整个折叠 | **暂停** |

## 4 翻译账

| 模块 | 记号读来的字段或形状 | 树逼出的 | 类 |
|---|---|---|---|
| `BrwHWBase` | 无 | `R2` (跨世界) 由 "读坐标的分支要在不可比的世界之间比" 逼出; `Sh` 由 "不用 `Funext`" 逼出 | 提供信息 |
| `BrwHWFold` | 无. `KnB` 照 `CvFoldInst.Kn-CO` 的记法 | 不变量 `Good` 的两半; `cvR` 对 `cmpF` 的两个结果; `RunR` 是对坐标形状的一步模拟 | 提供信息 |
| `BrwHW` | 无 | `nκ` 段化归成两条, 一条与 `KVal` 的 `κ⊑` 是同一个缺口 | 提供信息 |

**按 `AGENTS.md` 归类: 提供信息.** 没有新构造子, 没有改树或折叠, 没有 `Lab`, 不爬站. `R2` 与 `Good` 是树侧的判据 (与记号无关的世界稳定性), 只在第 0 层坐标与 `Step` 的子语言上证了保持.

## 5 审计

`importclosure.py` 用任务给的 `--only` 表 (`OCF.Free.Level`, `OCF.BTBO`, `CumReadCF`, `TLRuleSpec`, `TLRuleSum`, `TLRule`, `SumOne`, `BrwMid`, `LayerTr`, `NoCumLit`, `HtFeed`, `BrwView`, `BrwWf`, `BrwHW`) 跑 `OCF.Align.BrwHW`: 闭包 35 个模块 (本地 25, 库 10), 禁用表 0, `--only` 之外 3 个: `CvFoldInst`, `CvFoldRun`, `CvFoldSub`. 研究对象 `Kn`, `Pk`, `Aᵐ` 就定义在 `CvFoldInst` 里. 加上 `--only OCF.Align.CvFold` 之后 OK.

`depslice.py` (到达块 / 记号模块块 / 别处记号词): `BrwHWBase:R2-ni` 47/0/0, `BrwHWFold:RunR` 128/0/0, `BrwHWFold:HW-Kn` 181/0/0, `BrwHWFold:HW-Pk` 196/0/0, `BrwHW:HW-mid` 200/0/0, `BrwHW:view-Pk` 249/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明没有受记号启发.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwHW where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁)
open import OCF.Align.SumOneTree using (D; _⨾_; n0)
open import OCF.Align.LayerTrOne using (one; toB)
open import OCF.Align.BrwViewDef using (BrwView)
open import OCF.Align.BrwViewOne using (HW; V₁)
open import OCF.Align.BrwViewKappa using (view₁)
open import OCF.Align.CvFoldInst using (Aᵐ; Pk; Kn)
open import OCF.Align.LayerTrFold using (mid₁)
open import OCF.Align.BrwHWBase using (Sh; R2; R2→WSq; R2-ni; UI; Ic; Sh-dif; R2-Ω; HW-Ω) public
open import OCF.Align.BrwHWFold using (ΔR; RS; ⊕R; StepR; cvR; RunR; HWs; Good; Good-⊕Step; Good-cv; Good-Y₀; Good-Y₁; HW-Kn; R2-Kn; HW-A; HW-Pk) public

-- mid₁ 的第三段
κD : ∀ {W} → D one W → D one W
κD (_ ⨾ (_ ⨾ z)) = z
κD _ = n0

HW-mid : HW (κD mid₁) → HW mid₁
HW-mid h = HW-A , (HW-Pk , h)

view-A : V₁ (one , tt) (toB tt Aᵐ)
view-A = BrwView.view view₁ Aᵐ HW-A

view-Pk : V₁ (one , tt) (toB tt Pk)
view-Pk = BrwView.view view₁ Pk HW-Pk
```
