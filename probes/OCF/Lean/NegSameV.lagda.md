# NegSameV (入口): 同值不同结构, 否定一路

> 不含记号. 与构造一路 SameV 配对, 共用接口 [SameVIf](SameVIf.lagda.md) (定稿 2026-11-06 21:03; 本路不改它). 作者本轮选定原话: "核心: 同值不同结构". 第 4 层: 只新增关系与定理, 不改树, 折叠, 合法性. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 不开 K. `Cd` 上的 UIP 只作模块参数 (条件), 函数外延不出现.
>
> **对纲领与目标.** 纲领 1, 2, 4: 一切比较都在布劳威尔树上, 无公理, 不读记号. 纲领 3: 同值不同结构的两层没有合法的字面公共上界 (`no-common`), 所以律里成对的层要带别的证据 (构造一路的配对 `Match`). 目标 "树侧的合法性标准": 决定只看值 (`dec-agree`), 与 `Match` 的三条律是同一件事的两面; 但 `Match` 本身不含值 (`tp-not-free`).
>
> **结局.** 本路没有否定 `P2`: 构造一路证了它 (`SameVGoal.P2-thm`, 条件 UIP; 本路复编通过, 陈述核对 `P2-same`). 本路的结果是它的边界与检查.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegSameV where

open import OCF.Lean.CRwBase using (Cd)
open import Relation.Binary.PropositionalEquality using (_≡_)
import OCF.Lean.NegSameVSpine
import OCF.Lean.NegSameVMor
import OCF.Lean.NegSameVStrict

module WithUIP (uipC : ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′) where
  import OCF.Lean.NegSameVKr uipC as Kr
  import OCF.Lean.NegSameVLit uipC as Lit
  import OCF.Lean.NegSameVBlind uipC as Blind
  import OCF.Lean.NegSameVCheck uipC as Check
```

## 地图

| 名字 | 文件 | 陈述 | 档 |
|---|---|---|---|
| **`stall-up`**, **`kR-not-val`**, **`P2ᵀᴸ-false`** | Kr | $k_R\,x+1\le k_R(\lim(x,x,\dots))$, 两个坐标标准同值; `P2` 的前提不能放宽到 `TL.≤` | 条件 UIP |
| `st-val`, `st-not-le` | Kr, Spine | 这一对标准同值, 不在 `LeAt` 里 | 定理 |
| **`strict-⊲`**, **`≤→⊲`**, **`one-spine`**, **`no-common`** | Spine | `LeAt` 在合法树的第一位置上就是字面 $\lhd$; 同值不同结构的两层不在同一合法世界 | 定理 |
| **`dec-agree`**, `above-mono`, `keep-mono` | Spine | 同值的层与同值的目标决定相同; 否则单调 | 定理 |
| **`P2-on`**, `P2-ω₁₂`, `P2-ω₂₁` | Lit | `gt` 在 $\le_X$ 下可比时 P2 由 `monoX` 得; $\omega_1,\omega_2$ 这一对不用跨层 | 条件 UIP |
| **`im-nz`**, **`self-safe`** | Mor | 沿 `LvMor`, 分量 $0$ 只配分量 $0$ | 定理 |
| **`M₁₂`** | Mor | $\omega_1+1\to\omega_2+1$ 的搬运, 接口全部律 | 定理 |
| **`crossV`**, **`blind`**, **`blind-top`** | Blind | 记录 `CrossV` 有无跨层内容的实例; 其中 `¬ Le M₁₂ (top _) (top _)` | 条件 UIP |
| **`shape-up`**, `shape-up2`, **`shape-bound`** | Strict | 形状 "部分和极限, 首项 $\ge X$" 给出 $X+1$, $X+2$, 而这个极限 $\le X+\omega$ | 定理 |
| **`self-no`**, `copy-ok`, `copy-Mw` | Check | $\Omega_1$ 本身比不到拷贝; 反方向成立 | 条件 UIP |
| **`not-reflect`** | Check | `_≼X_` 不层反射 (`gtP` 与 `floor-block` 对上) | 条件 UIP |
| **`Mw`**, `w-not-le`, **`tp-not-free`** | Check | 有配对 $\omega_1\sim1$, 地板不相关: 地板律不是配对的推论 | 定理 (模块带 UIP 参数) |
| `LE-not-refl` | Check | 跨层关系不自反 | 同上 |
| `tu-block`, `Mb` | Check | `crossX` 右边不能取 `inU₁`; 裸的 `floor-block` 层号对有配对 | 同上 |
| `P2-same`, `p2-at`, `goal-at` | Check | 构造一路的陈述就是接口的陈述 | 条件 UIP |

## 只否定什么, 不否定什么

- `kR-not-val`, `P2ᵀᴸ-false`: 只否定对 `TLRuleSpec._≤_` 的单调. **不否定** `P2` (已证).
- `no-common`: 只否定单一目标的归纳形状 (`monoX` 的形状). **不否定** 成对目标 (构造一路走的就是它).
- `blind`: 只否定 "`CrossV` 的字段推出跨层比较". **不否定** 构造一路的 `LE`, `tp`, `gtP`.
- `shape-*`: 只否定 "`goal`, `goal2` 的严格是强度证据". **不否定** `goal`, 也不否定 `TU 1` 高于 `TX` (读法, 判断).
- `tp-not-free`, `LE-not-refl`, `self-no`: 只说关系的性质.
- `tu-block`: 只否定以 `inU₁` 为 `crossX` 的右边. **不否定** `TU-mono`.

## 前提实例

- `uipC`: 函数外延推出 (`ValCUip.fe→uipC`, 条件 Funext).
- `stall-up`: 一切 $x$; 合法实例 `Lg-st`.
- `dec-agree`, `no-common`: `ex-dec`, `ex-dec₂`, `ex-no-common`.
- `blind-top`: `M₁₂`, `m-ne`.
- `self-no`, `copy-ok`: 一切配对 / `Mw`.
- 构造一路: `Match` 的实例 `M.match` (定理), `tp` 的实例 `Core.tp` (定理), `ShLaw` 的实例 `shLaw₁` (定理), 右边的 `MoX` 由 `MoX-U`, `MoX-gt` 给出 (定理).

## 文件

| 文件 | 内容 |
|---|---|
| [NegSameVSpine](NegSameVSpine.lagda.md) | 第一位置上的严格; 同一世界放不下同值不同结构的两层; 决定一致 |
| [NegSameVKr](NegSameVKr.lagda.md) | $k_R$ 不是标准值的函数 |
| [NegSameVLit](NegSameVLit.lagda.md) | 不用跨层的那部分 P2 |
| [NegSameVMor](NegSameVMor.lagda.md) | 对 `LvMor`: 分量 0; `M₁₂` |
| [NegSameVBlind](NegSameVBlind.lagda.md) | `CrossV` 的盲实例 |
| [NegSameVStrict](NegSameVStrict.lagda.md) | 严格只是后继档 |
| [NegSameVCheck](NegSameVCheck.lagda.md) | 对构造一路定理的检查 |
| 本篇 | 入口 |

## 结论 (按档)

- **[定理]** 上表标 "定理" 的各条. **[条件定理, 条件 UIP (由 Funext 推出)]** 上表标 "条件 UIP" 的各条.
- **[判断]** 没有找到 `LeAt` 对子上不存在协调搬运的例子; 裸的 $m$ 上配对能否由任意推导构造, 未走通; `TU-mono` 未证未否定; 跨层关系与传递性没有矛盾 (没有写成定理).
